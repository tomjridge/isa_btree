theory Delete
imports Find
begin

datatype del_t =
  D_small_leaf "kvs"
  | D_small_node "ks * rs"
  | D_updated_subtree "r"

type_synonym fo = del_t  (* focus *)

datatype d_state = 
  D_down "find_state * r"  (* r is the original pointer to root, in case we don't delete anything *)
  | D_up "fo * stk * r"
  | D_finished r
  
type_synonym u = "fo * stk"  (* r is unused parameter *)
type_synonym d = "find_state * r"

type_synonym ds_t = d_state

definition mk_delete_state :: "key \<Rightarrow> r \<Rightarrow> d_state" where
"mk_delete_state k r = (D_down(mk_find_state k r,r))"

definition dest_d_finished :: "d_state \<Rightarrow> r option" where
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

datatype 'a d12_t = D1 "'a" | D2 "'a * key * 'a"

(* this defn rather horrible; apologies; it is needed to avoid duplication at the block level *)
definition steal_or_merge :: 
  "bool (* right *) \<Rightarrow>
  bool (* leaf *) \<Rightarrow> 
  ((ks * 'v list) \<Rightarrow> 'c) \<Rightarrow> 
  (ks * 'v list) \<Rightarrow> key \<Rightarrow> (ks * 'v list) \<Rightarrow> 'c d12_t" where
"steal_or_merge right leaf mk_c c p_k s = ( (* child sibling *)
  let m = frac_mult in
  (* sibling *)
  let (s_ks,s_ts) = s in
  let ((s_k,s_t),s_1) = (
    case right of
    True \<Rightarrow> (let ((k,ks),(t,ts)) = (dest_list s_ks,dest_list s_ts) in ((k,t),(ks,ts)))
    | False \<Rightarrow> (let ((ks,k),(ts,t)) = (dest_list' s_ks,dest_list' s_ts) in ((k,t),(ks,ts))))
  in
  case (1+List.length(fst s_1) > (if leaf then min_leaf_size else min_node_keys)) of
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

definition post_steal_or_merge :: "stk \<Rightarrow> r frame \<Rightarrow> ks_rs \<Rightarrow> ks_rs \<Rightarrow> r d12_t => u MM" where
"post_steal_or_merge stk' p p_1 p_2 x = (
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
            case (p_sz < min_node_keys) of 
            True \<Rightarrow> (return (D_small_node(p'|>dest_Node_frame)))
            | False \<Rightarrow> (
              (* write the frame at this point *)
              p'|>frame_to_page|>alloc|>fmap (% r. D_updated_subtree(r)))))
        in
        f' |> fmap (% f'. (f',stk')) )
      | D2(c1,k,c2) \<Rightarrow> (
        let p' = Node_frame(m (m p_1 ([k],[c1,c2])) p_2) in
        let p_sz = p'|>dest_Node_frame|>fst|>List.length in
        let f' = (
          (* we may be at the root, in which case f' may be small *)
          case (p_sz < min_node_keys) of
          True \<Rightarrow> (
            let _ = assert_true (stk'=[]) in
            return (D_small_node(p'|>dest_Node_frame))
          )
          | False \<Rightarrow> (
            p' |>frame_to_page|>alloc|>fmap (% r. D_updated_subtree(r))))
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
          | _ \<Rightarrow> impossible1 ''delete, get_sibling''
        ))
"

definition step_up :: "u \<Rightarrow> u MM" where
"step_up du = (
  let (f,stk) = du in
  case stk of
  [] \<Rightarrow> (impossible1 ''delete, step_up'')
  | p#stk' \<Rightarrow> (
    case f of   
    D_updated_subtree r \<Rightarrow> (
      let ((ks1,rs1),_,(ks2,rs2)) = p|>dest_frame in
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> frame_to_page |> alloc |> fmap (% r'. (D_updated_subtree r',stk'))
    )
    | D_small_leaf(kvs) \<Rightarrow> (
      let leaf = True in
      let mk_c = (% ks_vs. let (ks,vs) = ks_vs in Leaf_frame(List.zip ks vs)) in
      let ((p_ks1,p_rs1),_,(p_ks2,p_rs2)) = p|>dest_frame in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm :: pframe MM = r |> page_ref_to_frame in
      let d12 :: pframe d12_t MM = frm |> fmap (% frm. steal_or_merge right leaf mk_c (kvs|>unzip) p_k (frm|>dest_Leaf_frame|>unzip)) in
      let d12' :: r d12_t MM = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> frame_to_page |> alloc |> fmap (% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> frame_to_page |> alloc |> bind
          (% r1. frm2 |> frame_to_page |> alloc |> fmap 
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
      let ((p_ks1,p_rs1),_,(p_ks2,p_rs2)) = p|>dest_frame in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm = r|>page_ref_to_frame in
      let d12 :: pframe d12_t MM = frm |> fmap (% frm. steal_or_merge right leaf mk_c (ks,rs) p_k (frm|>dest_Node_frame)) in
      let d12' :: r d12_t MM = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> frame_to_page |> alloc |> fmap(% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> frame_to_page |> alloc |> bind
          (% r1. frm2 |> frame_to_page |> alloc |> fmap 
          (% r2. D2(r1,p_k,r2)))))
      in
      d12' |> bind (% x. post_steal_or_merge stk' p p_1 p_2 x)
    )
  )
)"

definition delete_step :: "d_state \<Rightarrow> d_state MM" where
"delete_step s = (
  case s of 
  D_down(f,r0) \<Rightarrow> (
    case (dest_f_finished f) of
    None \<Rightarrow> (find_step f |> fmap (% f'. D_down(f',r0)))
    | Some x \<Rightarrow> (
      let (k,r,kvs,stk) = x in
      case k : set (kvs|>List.map fst) of
      True \<Rightarrow> (
        (* something to delete *)
        let kvs' = kvs|>List.filter (% x. ~ (key_eq (fst x) k)) in
        case (List.length kvs' < Constants.min_leaf_size) of
        True \<Rightarrow> (return (D_up(D_small_leaf(kvs'),stk,r0)))
        | False \<Rightarrow> (
          Leaf_frame(kvs')|>frame_to_page |> alloc |> fmap
          (% r. D_up(D_updated_subtree(r),stk,r0)))
      )
      | False \<Rightarrow> (
        (* nothing to delete *)
        return (D_finished r0)
      )
    )
  )
  | D_up(f,stk,r0) \<Rightarrow> (
    case stk of
    [] \<Rightarrow> (
      case f of
      D_small_leaf kvs \<Rightarrow> (Leaf_frame(kvs)|>frame_to_page|>alloc|>fmap (% r. D_finished r)) 
      | D_small_node (ks,rs) \<Rightarrow> (
        Node_frame(ks,rs)|>frame_to_page|>alloc|>fmap (% r. D_finished r)
      )
      | D_updated_subtree(r) \<Rightarrow> (return (D_finished r))
    )
    | _ \<Rightarrow> (step_up (f,stk) |> fmap (% (f,stk). (D_up(f,stk,r0))))
  )
  | D_finished(r) \<Rightarrow> (return s)  (* stutter *)
  
)"

(* wellformedness ------------------------------------------------- *)

definition wf_d :: "tree \<Rightarrow> store \<Rightarrow> d \<Rightarrow> bool" where
"wf_d t0 s d = (
  let (fs,r) = d in
  wellformed_find_state s t0 fs  
)"

definition wf_u :: "tree \<Rightarrow> key \<Rightarrow> store \<Rightarrow> u \<Rightarrow> bool" where
"wf_u t0 k s u = (
  let r_to_t = r_to_t s in
  let (fo,stk) = u in
  case fo of
  D_small_leaf kvs \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_leaf) in
    (t_stk|>no_focus = stk|>stack_map r_to_t|>no_focus) &
    (wellformed_tree ms (Leaf kvs)) &
    ( (t_fo|>tree_to_kvs|>kvs_delete k) = kvs)   
  )
  | D_small_node (ks,rs) \<Rightarrow> (
    (* FIXME don't we need some wf on Node(ks,rs)? *)
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_leaf) in
    let t = Node(ks,rs|>List.map r_to_t) in
    (t_stk|>no_focus = stk|>stack_map r_to_t|>no_focus) &
    (wellformed_tree ms t) &
    ( (t_fo|>tree_to_kvs|>kvs_delete k) = (t|>tree_to_kvs))   
  )
  | D_updated_subtree(r) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_stack k t0 (List.length stk) in
    let t = r|>r_to_t in
    (t_stk|>no_focus = stk|>stack_map r_to_t|>no_focus) &
    (wellformed_tree None t) &
    ( (t_fo|>tree_to_kvs|>kvs_delete k) = (t|>tree_to_kvs))   
  )
)"

definition wf_f :: "tree \<Rightarrow> key \<Rightarrow> store \<Rightarrow> r \<Rightarrow> bool" where
"wf_f t0 k s r = (
  let t' = r_to_t s r in
  wellformed_tree (Some(Small_root_node_or_leaf)) t' &
  ( (t0|>tree_to_kvs|>kvs_delete k) = (t'|>tree_to_kvs))
)"

definition wellformed_delete_state :: "tree \<Rightarrow> key \<Rightarrow> store \<Rightarrow> ds_t \<Rightarrow> bool" where
"wellformed_delete_state t0 k s ds = (
  case ds of 
  D_down d \<Rightarrow> (wf_d t0 s d)
  | D_up (fo,stk,r) \<Rightarrow> (wf_u t0 k s (fo,stk) & (r_to_t s r = t0))
  | D_finished r \<Rightarrow> (wf_f t0 k s r) 
)
"


end