theory Insert
imports Find
begin


datatype 'k i12_t = I1 r | I2 "r*'k*r"

type_synonym 'k focus_t = "'k i12_t"
type_synonym 'k fo = "'k focus_t"

type_synonym ('k,'v) down_state = "('k,'v) fs*'v"
type_synonym ('k,'v) d = "('k,'v) down_state"
type_synonym 'k up_state = "'k fo*'k stk"
type_synonym 'k u = "'k up_state"

datatype ('k,'v) i_state_t = 
  I_down "('k,'v) d"
  | I_up "'k u"
  | I_finished r

type_synonym ('k,'v) is_t = "('k,'v) i_state_t"  

definition mk_insert_state :: "'k \<Rightarrow> 'v \<Rightarrow> r \<Rightarrow> ('k,'v) i_state_t" where
"mk_insert_state k v r = (I_down (mk_find_state k r,v))"


definition dest_i_finished :: "('k,'v) is_t \<Rightarrow> r option" where
"dest_i_finished s = (case s of I_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"

(* defns ------------------------------------ *)

definition step_down :: "('k,'v) store \<Rightarrow> ('k,'v) d \<Rightarrow> ('k,'v) d MM" where
"step_down s d = (
  let (fs,v) = d in
  find_step s fs |> fmap (% d'. (d',v))
)"

definition step_bottom :: "('k,'v) store \<Rightarrow> ('k,'v) d \<Rightarrow> 'k u MM" where
"step_bottom s d = (
  let c = s|>s2c in
  let (fs,v) = d in
  case dest_f_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    store_free s (r0#(r_stk_to_rs stk)) |> bind 
    (% _.
    let kvs' = kvs |> kvs_insert (s|>s2ord) (k,v) in
    let fo = (
      case (length kvs' \<le> (c|>max_leaf_size)) of
      True \<Rightarrow> (Leaf_frame kvs' |> store_alloc s |> fmap (% r'. I1(r')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf c kvs' in
        Leaf_frame kvs1 |> store_alloc s |> bind
        (% r1. Leaf_frame kvs2 |> store_alloc s |> fmap (% r2. I2(r1,k',r2)))) )
    in
    fo |> fmap (% fo. (fo,stk))))
)"

definition step_up :: "('k,'v) store \<Rightarrow> 'k u \<Rightarrow> 'k u MM" where
"step_up s u = (
  let c = s|>s2c in
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible1 (STR ''insert, step_up'') (* FIXME what about trace? can't have arb here; or just stutter on I_finished in step? *)
  | x#stk' \<Rightarrow> (
    let ((ks1,rs1),_,(ks2,rs2)) = dest_frame x in
    case fo of
    I1 r \<Rightarrow> (
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> store_alloc s |> fmap (% r. (I1 r,stk')))
    | I2 (r1,k,r2) \<Rightarrow> (
      let ks' = ks1@[k]@ks2 in
      let rs' = rs1@[r1,r2]@rs2 in
      case (List.length ks' \<le> c|>max_node_keys) of
      True \<Rightarrow> (
        Node_frame(ks',rs') |> store_alloc s |> fmap (% r. (I1 r,stk')))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node c (ks',rs') in  (* FIXME move split_node et al to this file *)
        Node_frame(ks_rs1) |> store_alloc s |> bind
        (% r1. Node_frame (ks_rs2) |> store_alloc s |> fmap 
        (% r2. (I2(r1,k,r2),stk'))))
    )
  )
)"

definition insert_step :: "('k,'v) store \<Rightarrow> ('k,'v) is_t \<Rightarrow> ('k,'v) is_t MM" where
"insert_step str s = (
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down str d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom str d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 r \<Rightarrow> return (I_finished r)
      | I2(r1,k,r2) \<Rightarrow> (
        (* create a new frame *)
        (Node_frame([k],[r1,r2]) |> store_alloc str |> fmap (% r. I_finished r))))
    | _ \<Rightarrow> (step_up str u |> fmap (% u. I_up u)))
  | I_finished f \<Rightarrow> (return s)  (* stutter *)
)"


(* wellformedness ------------------------------------------------------------ *)

definition wf_d :: " ('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v) tree \<Rightarrow> ('k,'v) d \<Rightarrow> bool" where
"wf_d str w t0 d =  assert_true' (
  let (fs,v) = d in
  wellformed_find_state str w t0 fs  
)"

definition wf_u :: "('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v) tree \<Rightarrow>'k \<Rightarrow> 'v \<Rightarrow> 'k u \<Rightarrow> bool" where
"wf_u str w t0 k v u =  assert_true' (
  let n = height t0 in
  let ord = str|>s2ord in
  let s = store_to_r2f str w in
  let r2t = frame_store_to_tree_store s n in
  (* need to check the stack and the focus *)
  let check_focus = % t r. wf_store_tree s r t in
  let check_stack = % rstk tstk. ((rstk|>stack_map r2t|>no_focus) = (tstk|>stack_map Some|>no_focus)) in   
  let (fo,stk) = u in
  case fo of
  I1 r \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    check_stack stk t_stk &
    (* FIXME need wf_tree r , and below *)
    (case (r2t r) of 
    None \<Rightarrow> False
    | Some t' \<Rightarrow> (
      t' |> tree_to_kvs = 
      t_fo|>tree_to_kvs|>kvs_insert ord (k,v))))
  | I2 (r1,k',r2) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack ord k t0 (List.length stk) in
    check_stack stk t_stk &
    ( let (l,u) = stack_to_lu_of_child t_stk in
      case (r2t r1, r2t r2) of
      (Some t1, Some t2) \<Rightarrow> (
        let (ks1,ks2) = (t1|>tree_to_keys,t2|>tree_to_keys) in
        check_keys ord l ks1 (Some k') &
        check_keys ord (Some k') ks2 u &
        ((t_fo|>tree_to_kvs|>kvs_insert ord (k,v)) = (t1|>tree_to_kvs @ (t2|>tree_to_kvs))))
      |(_,_) \<Rightarrow> False
    )
  )
)"

definition wf_f :: "('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v) tree \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> r \<Rightarrow> bool" where
"wf_f str w t0 k v r =  assert_true' (
  let c = str|>s2c in
  let n = height t0 in
  let ord = str|>s2ord in
  let s = store_to_r2f str w in
  let r2t = frame_store_to_tree_store s n in
  case r2t r of
  None \<Rightarrow> False
  | Some t' \<Rightarrow> (
    wellformed_tree c (Some(Small_root_node_or_leaf)) ord t' &
    ( (t0|>tree_to_kvs|>kvs_insert ord (k,v)) = (t'|>tree_to_kvs))
  )
)"

definition wellformed_insert_state :: "('k,'v) store \<Rightarrow> world \<Rightarrow> ('k,'v) tree \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v) is_t \<Rightarrow> bool" where
"wellformed_insert_state str w t0 k v is =  assert_true' (
  case is of 
  I_down d \<Rightarrow> (wf_d str w t0 d)
  | I_up u \<Rightarrow> (wf_u str w t0 k v u)
  | I_finished r \<Rightarrow> (wf_f str w t0 k v r) 
)
"

(* don't bother with wf_trans *)

end