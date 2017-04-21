theory Insert_many
imports Find
begin

(* like Insert, but allows to insert many keys during a single traversal to a leaf *)

datatype i_t = I1 "r*kvs" | I2 "(r*k*r) * kvs"

type_synonym focus_t = "i_t"
type_synonym fo = focus_t

type_synonym down_state = "fs * (v * kvs)"
type_synonym d = down_state

type_synonym up_state = "fo*rstk"
type_synonym u = up_state

datatype i_state_t = 
  I_down d
  | I_up u
  | I_finished "r * kvs"

type_synonym ist = i_state_t  

definition mk_insert_state :: "k \<Rightarrow> v \<Rightarrow> kv list \<Rightarrow> r \<Rightarrow> i_state_t" where
"mk_insert_state k v kvs r = (I_down (mk_find_state k r,(v,kvs)))"


definition dest_i_finished :: "ist \<Rightarrow> (r * kvs) option" where
"dest_i_finished s = (case s of I_finished (r,kvs) \<Rightarrow> Some (r,kvs) | _ \<Rightarrow> None)"

(* defns ------------------------------------ *)

definition step_down :: "d \<Rightarrow> d MM" where
"step_down d = (
  let (fs,v) = d in
  find_step fs |> fmap (% d'. (d',v))
)"

(* insert kv, and as many from new as possible subject to lu bound and max size of 2*max_leaf_size; 
kv<new, and new are sorted in order; return the remaining new that were not inserted
*)
definition kvs_insert_2 :: "k option \<Rightarrow> (k*v) \<Rightarrow> kvs \<Rightarrow> kvs \<Rightarrow> kvs * kvs" where
"kvs_insert_2 u kv new existing = (
  let step = (% s. 
    let (acc,new') = s in
    case (length acc \<ge> 2 * constants|>max_leaf_size) of
    True \<Rightarrow> None
    | False \<Rightarrow> (
      case new' of
      [] \<Rightarrow> None
      | (k,v)#new'' \<Rightarrow> (
        case (check_keys compare_k None {k} u) of 
        True \<Rightarrow> (Some(kvs_insert compare_k (k,v) acc,new''))
        | False \<Rightarrow> (None))))
  in
  iter_step step (existing,new)
)"

(* how to split a leaf where there are n > max_leaf_size and \<le> 2*max_leaf_size elts?

we want the first leaf ge the second leaf, and 2nd leaf to have at least min_leaf_size

for second leaf, we want n2=min_leaf_size+delta, where delta is minimal such that n1+n2=n and n1 \<le> max_leaf_size

so n2 = min_leaf_size; n1 = n - min_leaf_size
then delta = n1 - max_leaf_size
n2+=delta
n1-=delta

*)

definition split_leaf :: "kvs \<Rightarrow> kvs * k * kvs" where
"split_leaf kvs = (
  let n = List.length kvs in
  let n1 = n in
  let n2 = 0 in
  let delta = constants|>min_leaf_size in
  let n1 = n1 - delta in
  let n2 = n2 + delta in
  let delta = (n1 - constants|>max_leaf_size) in
  let n1 = n1 - delta in
  let n2 = n2 + delta in
  let (l,r) = split_at n1 kvs in
  let k = (case r of [] \<Rightarrow> impossible1 (STR ''insert_many: split_leaf'') | (k,v)#_ \<Rightarrow> k) in
  (l,k,r)
)"


definition step_bottom :: "d \<Rightarrow> u MM" where
"step_bottom d = (
  let (fs,(v,kvs0)) = d in
  case dest_f_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    store_free (r0#(r_stk_to_rs stk)) |> bind 
    (% _.
    let (l,u) = stack_to_lu_of_child stk in
    let (kvs',kvs0') = kvs_insert_2 u (k,v) kvs0 kvs in
    let fo = (
      case (length kvs' \<le> constants|>max_leaf_size) of
      True \<Rightarrow> (Leaf_frame kvs' |> store_alloc |> fmap (% r'. I1(r',kvs0')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf kvs' in
        Leaf_frame kvs1 |> store_alloc |> bind
        (% r1. Leaf_frame kvs2 |> store_alloc |> fmap (% r2. I2((r1,k',r2),kvs0')))) )
    in
    fo |> fmap (% fo. (fo,stk))))
)"

definition step_up :: "u \<Rightarrow> u MM" where
"step_up u = (
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible1 (STR ''insert, step_up'') (* FIXME what about trace? can't have arb here; or just stutter on I_finished in step? *)
  | x#stk' \<Rightarrow> (
    let ((ks1,rs1),_,(ks2,rs2)) = dest_ts_frame x in
    case fo of
    I1 (r,kvs0) \<Rightarrow> (
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> store_alloc |> fmap (% r. (I1 (r,kvs0),stk')))
    | I2 ((r1,k,r2),kvs0) \<Rightarrow> (
      let ks' = ks1@[k]@ks2 in
      let rs' = rs1@[r1,r2]@rs2 in
      case (List.length ks' \<le> constants|>max_node_keys) of
      True \<Rightarrow> (
        Node_frame(ks',rs') |> store_alloc |> fmap (% r. (I1 (r,kvs0),stk')))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node constants (ks',rs') in  (* FIXME move split_node et al to this file *)
        Node_frame(ks_rs1) |> store_alloc |> bind
        (% r1. Node_frame (ks_rs2) |> store_alloc |> fmap 
        (% r2. (I2((r1,k,r2),kvs0),stk'))))
    )
  )
)"

definition insert_step :: "ist \<Rightarrow> ist MM" where
"insert_step s = (
  case s of 
  I_down d \<Rightarrow> (
    let (fs,(v,kvs0)) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 (r,kvs0) \<Rightarrow> return (I_finished (r,kvs0))
      | I2((r1,k,r2),kvs0) \<Rightarrow> (
        (* create a new frame *)
        (Node_frame([k],[r1,r2]) |> store_alloc |> fmap (% r. I_finished (r,kvs0)))))
    | _ \<Rightarrow> (step_up u |> fmap (% u. I_up u)))
  | I_finished f \<Rightarrow> (return s)  (* stutter *)
)"


(* wellformedness ------------------------------------------------------------ *)

(*
definition wf_d :: "tree \<Rightarrow> store \<Rightarrow> d \<Rightarrow> bool" where
"wf_d t0 s d =  assert_true' (
  let (fs,v) = d in
  wellformed_find_state s t0 fs  
)"

definition wf_u :: "tree \<Rightarrow> key \<Rightarrow> value_t \<Rightarrow> store \<Rightarrow> u \<Rightarrow> bool" where
"wf_u t0 k v s u =  assert_true' (
  let r_to_t = r_to_t s in
  let (fo,stk) = u in
  case fo of
  I1 r \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    (t_stk|>no_focus = stk|>stack_map r_to_t|>no_focus) &
    (* FIXME need wf_tree r , and below *)
    ( (t_fo|>tree_to_kvs|>kvs_insert (k,v)) = (r|>r_to_t|>tree_to_kvs))  )
  | I2 (r1,k',r2) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    (t_stk|>no_focus = stk|>stack_map r_to_t|>no_focus) &
    ( let (l,u) = stack_to_lu_of_child t_stk in
      let (t1,t2) = (r1|>r_to_t,r2|>r_to_t) in
      let (ks1,ks2) = (t1|>tree_to_keys,t2|>tree_to_keys) in
      check_keys l ks1 (Some k') &
      check_keys (Some k') ks2 u &
      ((t_fo|>tree_to_kvs|>kvs_insert (k,v)) = (t1|>tree_to_kvs @ (t2|>tree_to_kvs))) 
    )
  )
)"

definition wf_f :: "tree \<Rightarrow> key \<Rightarrow> value_t \<Rightarrow> store \<Rightarrow> r \<Rightarrow> bool" where
"wf_f t0 k v s r =  assert_true' (
  let t' = r_to_t s r in
  wellformed_tree (Some(Small_root_node_or_leaf)) t' &
  ( (t0|>tree_to_kvs|>kvs_insert (k,v)) = (t'|>tree_to_kvs))
)"

definition wellformed_insert_state :: "tree \<Rightarrow> key \<Rightarrow> value_t \<Rightarrow> store \<Rightarrow> ist \<Rightarrow> bool" where
"wellformed_insert_state t0 k v s is =  assert_true' (
  case is of 
  I_down d \<Rightarrow> (wf_d t0 s d)
  | I_up u \<Rightarrow> (wf_u t0 k v s u)
  | I_finished r \<Rightarrow> (wf_f t0 k v s r) 
)
"
*)

(* don't bother with wf_trans *)

end