theory Delete
imports Find
begin

datatype del_t =
  D_small_leaf "kvs"
  | D_small_node "ks * rs"
  | D_updated_subtree "r"

type_synonym fo = del_t  (* focus *)

datatype delete_state = 
  D_down "find_state * r"  (* r is the original pointer to root, in case we don't delete anything *)
  | D_up "fo * rstk * r"
  | D_finished r
  
type_synonym u = "fo * rstk"  
type_synonym d = "find_state * r"

type_synonym dst = delete_state

definition mk_delete_state :: "k \<Rightarrow> r \<Rightarrow> dst" where
"mk_delete_state k r = (D_down(mk_find_state k r,r))"

definition dest_d_finished :: "dst \<Rightarrow> r option" where
"dest_d_finished x = (case x of D_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"

(* steal or merge -------------------------------------------- *)

type_synonym 'a frac_t = "ks * 'a list"

definition frac_mult :: "'a frac_t \<Rightarrow> 'a frac_t \<Rightarrow> 'a frac_t"  where
"frac_mult xs ys = (
let (a,b) = xs in
let (a',b') = ys in
(a@a',b@b')
)"

(* 'a - the tree type; 'v - the values in the children; 't - the values in the parent
'c - child type = ks * 'v list
'p - parent type = ks * 't list
*)

datatype 'a d12_t = D1 "'a" | D2 "'a * k * 'a"

(* this defn rather horrible; apologies; it is needed to avoid duplication at the block level *)
definition steal_or_merge :: 
  "bool \<Rightarrow>  (* right *)
  bool \<Rightarrow>   (* leaf *)
  ((ks * 'v list) \<Rightarrow> 'c) \<Rightarrow>  (* mk_child *) 
  (ks * 'v list) \<Rightarrow>  (* child *) 
  k \<Rightarrow> 
  (ks * 'v list) \<Rightarrow> (* sibling *) 
  'c d12_t" where
"steal_or_merge right leaf mk_c c p_k s = ( 
  let m = frac_mult in
  (* sibling *)
  let (s_ks,s_ts) = s in
  let ((s_k,s_t),s_1) = (
    case right of
    True \<Rightarrow> (let ((k,ks),(t,ts)) = (dest_list s_ks,dest_list s_ts) in ((k,t),(ks,ts)))
    | False \<Rightarrow> (let ((ks,k),(ts,t)) = (dest_list' s_ks,dest_list' s_ts) in ((k,t),(ks,ts))))
  in
  case (1+List.length(fst s_1) > (if leaf then constants|>min_leaf_size else constants|>min_node_keys)) of
  True \<Rightarrow> (
    (* steal *)
    let c' =
      (* slightly different for leaf *)
      let k = (if leaf then s_k else p_k) in
      (if right then m c ([k],[s_t]) else m ([k],[s_t]) c) 
    in 
    let s' = mk_c s_1 in
    let p_k' = (if leaf then (
      let right_sib = if right then s_1 else c' in
      right_sib |> fst |> List.hd) 
      else s_k)
    in
    let c' = mk_c c' in
    (if right then D2(c',p_k',s') else D2(s', p_k', c'))
  )
  | False \<Rightarrow> (
    (* merge *)
    let k' = (if leaf then ([],[]) else ([p_k],[])) in
    let c' = mk_c (if right then m (m c k') s  else m s (m k' c)) in
    D1 c'
  )
)"  


(* when called on a node (D_...) which is a root resulting from a delete op,
we may have the situation that the root contains no keys, or is small *)

type_synonym ks_rs = "ks * rs"

definition post_steal_or_merge :: "rstk \<Rightarrow> (k,r) ts_frame \<Rightarrow> (ks * rs) \<Rightarrow> (ks * rs) \<Rightarrow> r d12_t => u MM" where
"post_steal_or_merge stk' p_unused p_1 p_2 x = (
      let m = frac_mult in
      case x of 
      D1 c' \<Rightarrow> (
        let p' = Node_frame(m (m p_1 ([],[c'])) p_2) in
        let p_sz = p'|>dest_Node_frame|>fst|>List.length in
        let f' = ( (* we may be at root, having deleted the single key *)
          case (p_sz = 0) of
          True \<Rightarrow> (
            let _ = assert_true (stk'=[]) in
            return (D_updated_subtree(c')))
          | False \<Rightarrow> (
            case (p_sz < constants|>min_node_keys) of 
            True \<Rightarrow> (return (D_small_node(p'|>dest_Node_frame)))
            | False \<Rightarrow> (
              (* write the frame at this point *)
              p'|>store_alloc|>fmap (% r. D_updated_subtree(r)))))
        in
        f' |> fmap (% f'. (f',stk')) )
      | D2(c1,k,c2) \<Rightarrow> (
        let p' = Node_frame(m (m p_1 ([k],[c1,c2])) p_2) in
        let p_sz = p'|>dest_Node_frame|>fst|>List.length in
        let f' = (
          (* we may be at the root, in which case f' may be small *)
          case (p_sz < constants|>min_node_keys) of
          True \<Rightarrow> (
            let _ = assert_true (stk'=[]) in
            return (D_small_node(p'|>dest_Node_frame))
          )
          | False \<Rightarrow> (
            p' |>store_alloc|>fmap (% r. D_updated_subtree(r))))
        in
        f' |> fmap (% f'. (f',stk')))       
)"

(* delete --------------------------------------------------------  *)

definition get_sibling :: "(ks_rs * ks_rs) \<Rightarrow> bool (* right *) * (ks_rs * ks_rs) * (k*r)" where
"get_sibling p = (
  let (p_1,p_2) = p in
        case p_2 of
        (p_k#p_ks2,r#p_ts2) \<Rightarrow> (
        let right = True in
        (right,(p_1,(p_ks2,p_ts2)),(p_k,r)))
        | _ \<Rightarrow> (
          case p_1 of
          (_#_,_#_) \<Rightarrow> (
            let right = False in
            let (p_ks1,p_ts1) = p_1 in
            let (p_1_ks,p_k) = dest_list' p_ks1 in
            let (p_1_ts,s) = dest_list' p_ts1 in
            let (p_1,p2) = ((p_1_ks,p_1_ts),p_2) in
            (right,(p_1,p_2),(p_k,s)))
          | _ \<Rightarrow> impossible1 (STR ''delete, get_sibling'')
        ))
"

definition step_up :: "u \<Rightarrow> u MM" where
"step_up du = (
  let (f,stk) = du in
  case stk of
  [] \<Rightarrow> (impossible1 (STR ''delete, step_up''))
  | p#stk' \<Rightarrow> (
    case f of   
    D_updated_subtree r \<Rightarrow> (
      let ((ks1,rs1),_,(ks2,rs2)) = p|>dest_ts_frame in
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> store_alloc |> fmap (% r'. (D_updated_subtree r',stk'))
    )
    | D_small_leaf(kvs) \<Rightarrow> (
      let leaf = True in
      let mk_c = (% ks_vs. let (ks,vs) = ks_vs in Leaf_frame(List.zip ks vs)) in
      let ((p_ks1,p_rs1),_,(p_ks2,p_rs2)) = p|>dest_ts_frame in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm = store_read r in
      let d12 :: frame d12_t MM = frm |> fmap (% frm. steal_or_merge right leaf mk_c (kvs|>unzip) p_k (frm|>dest_Leaf_frame|>unzip)) in
      let d12' :: r d12_t MM = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> store_alloc |> fmap (% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> store_alloc |> bind
          (% r1. frm2 |> store_alloc |> fmap 
          (% r2. D2(r1,p_k,r2)))))
      in
      d12' |> bind (% x. post_steal_or_merge stk' p p_1 p_2 x) 
    )
    
  | D_small_node(ks,rs) \<Rightarrow> (
      (* FIXME almost identical to small leaf case *)
      let leaf = False in
      let mk_c = (% ks_rs. Node_frame(ks_rs)) in 
      (* FIXME the small cases can be handled uniformly; want steal left,right to be uniform, and take a child as arg; also return option *)  
      (* parent info is already read, but we must read the siblings from disk *)
      let ((p_ks1,p_rs1),_,(p_ks2,p_rs2)) = p|>dest_ts_frame in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm = store_read r in
      let d12 :: frame d12_t MM = frm |> fmap (% frm. steal_or_merge right leaf mk_c (ks,rs) p_k (frm|>dest_Node_frame)) in
      let d12' :: r d12_t MM = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> store_alloc |> fmap(% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> store_alloc |> bind
          (% r1. frm2 |> store_alloc |> fmap 
          (% r2. D2(r1,p_k,r2)))))
      in
      d12' |> bind (% x. post_steal_or_merge stk' p p_1 p_2 x)
    )
  )
)"

definition delete_step :: "delete_state \<Rightarrow> delete_state MM" where
"delete_step s = (
  case s of 
  D_down(f,r0) \<Rightarrow> (
    case (dest_f_finished f) of
    None \<Rightarrow> (find_step f |> fmap (% f'. D_down(f',r0)))
    | Some x \<Rightarrow> (
      let (r0,k,r,kvs,stk) = x in
      store_free (r0#(r_stk_to_rs stk)) |> bind 
      (% _.
      case k : set (kvs|>List.map fst) of
      True \<Rightarrow> (
        (* something to delete *)
        let kvs' = kvs|>List.filter (% x. ~ (key_eq (fst x) k)) in
        case (List.length kvs' < constants|>min_leaf_size) of
        True \<Rightarrow> (return (D_up(D_small_leaf(kvs'),stk,r0)))
        | False \<Rightarrow> (
          Leaf_frame(kvs') |> store_alloc |> fmap
          (% r. D_up(D_updated_subtree(r),stk,r0)))
      )
      | False \<Rightarrow> (
        (* nothing to delete *)
        return (D_finished r0)
      ))
    )
  )
  | D_up(f,stk,r0) \<Rightarrow> (
    case stk of
    [] \<Rightarrow> (
      case f of
      D_small_leaf kvs \<Rightarrow> (Leaf_frame(kvs)|>store_alloc|>fmap (% r. D_finished r)) 
      | D_small_node (ks,rs) \<Rightarrow> (
        Node_frame(ks,rs)|>store_alloc|>fmap (% r. D_finished r)
      )
      | D_updated_subtree(r) \<Rightarrow> (return (D_finished r))
    )
    | _ \<Rightarrow> (step_up (f,stk) |> fmap (% (f,stk). (D_up(f,stk,r0))))
  )
  | D_finished(r) \<Rightarrow> (return s)  (* stutter *)
  
)"

(* wellformedness ------------------------------------------------- *)

definition wf_d :: "kv_tree \<Rightarrow> store \<Rightarrow> d \<Rightarrow> bool" where
"wf_d t0 s d =  assert_true' (
  let (fs,r) = d in
  wellformed_find_state s t0 fs  
)"

definition wf_u :: "kv_tree \<Rightarrow> k \<Rightarrow> store \<Rightarrow> u \<Rightarrow> bool" where
"wf_u t0 k str u =  assert_true' (
  let n = height t0 in
  let r2f = mk_r2f str in
  let r2t = mk_r2t r2f n in
  let (fo,stk) = u in
  let check_stack = % rstk tstk. ((rstk|>stack_map r2t|>no_focus) = (tstk|>stack_map Some|>no_focus)) in
  let check_wf = % ms t. (wellformed_tree constants ms compare_k t) in
  let check_focus = % fo kvs. fo|> tree_to_kvs |> kvs_delete compare_k k = kvs in
  case fo of
  D_small_leaf kvs \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_leaf) in
    check_stack stk t_stk & 
    check_wf ms (Leaf kvs) &
    check_focus t_fo kvs
  )
  | D_small_node (ks,rs) \<Rightarrow> (
    (* FIXME don't we need some wf on Node(ks,rs)? *)
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_node) in
    let t = Node(ks,rs|>List.map r2t |> List.map dest_Some) in  (* FIXME check we can dest_Some *)
    check_stack stk t_stk &
    check_wf ms t &
    check_focus t_fo (t|>tree_to_kvs)   
  )
  | D_updated_subtree(r) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> None) in
    let t = r|>r2t|>dest_Some in  (* FIXME check dest *)
    check_stack stk t_stk &
    check_wf ms t &
    check_focus t_fo (t|>tree_to_kvs)   
  )
)"

definition wf_f :: "kv_tree \<Rightarrow> k \<Rightarrow> store \<Rightarrow> r \<Rightarrow> bool" where
"wf_f t0 k str r =  assert_true' (
  let n = height t0 in
  let r2f = mk_r2f str in
  let r2t = mk_r2t r2f n in
  let t' = r2t r |> dest_Some in  (* check dest_Some *)
  wellformed_tree constants (Some(Small_root_node_or_leaf)) compare_k t' &
  ( (t0|>tree_to_kvs|>kvs_delete compare_k k) = (t'|>tree_to_kvs))
)"

definition wellformed_delete_state :: "kv_tree \<Rightarrow> k \<Rightarrow> store \<Rightarrow> delete_state \<Rightarrow> bool" where
"wellformed_delete_state t0 k str ds =  assert_true' (
  let n = height t0 in
  let r2f = mk_r2f str in
  let r2t = mk_r2t r2f n in
  case ds of 
  D_down d \<Rightarrow> (wf_d t0 str d)
  | D_up (fo,stk,r) \<Rightarrow> (wf_u t0 k str (fo,stk) & (r2t r = Some t0))
  | D_finished r \<Rightarrow> (wf_f t0 k str r) 
)
"

end