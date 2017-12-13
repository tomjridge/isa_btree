theory Delete2
imports Find
begin

(* FIXME merge in documentation from Delete *)

(* new version with less attempt at treating all cases uniformly *)

datatype ('k,'v,'r)del_t =
  D_small_leaf "('k*'v)s"
  | D_small_node "'k s * 'r s"
  | D_updated_subtree "'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r) del_t"  (* focus *)

(* dead: https://groups.google.com/forum/#!topic/fa.isabelle/hWGSgu3pSsM *)

(* D_down: r is the original pointer to root, in case we don't delete anything *)
datatype (dead 'k, dead 'v,dead 'r) delete_state = 
  D_down "('k,'v,'r) fs * 'r"  
  | D_up "('k,'v,'r) fo * ('k,'r) rstk * 'r"  (* last 'r is the root, for wellformedness check *)
  | D_finished "'r" 
  
type_synonym ('k,'v,'r)u = "('k,'v,'r)fo * ('k,'r)rstk"  
type_synonym ('k,'v,'r)d = "('k,'v,'r)find_state * 'r"

type_synonym ('k,'v,'r)dst = "('k,'v,'r) delete_state"

definition mk_delete_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)dst" where
"mk_delete_state k r = (D_down(mk_find_state k r,r))"

definition dest_d_finished :: "('k,'v,'r)dst \<Rightarrow> 'r option" where
"dest_d_finished x = (case x of D_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"



(* steal or merge --------------------------------------------------- *)



(* fixup empty parent --------------- *)

(* it may be the case that we merge two children, and the parent root has just one key, 
which is then removed as well, leaving a potentially malformed tree; 
this code fixes that problem *)

(* fo is the alternative focus in case root is empty *)
definition maybe_fixup_empty_parent_after_merge :: 
  "constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k,'v,'r)fo \<Rightarrow> (('k,'v,'r)fo,'t)MM"
where
"maybe_fixup_empty_parent_after_merge cs store_ops krs fo = (
  let (ks,rs) = krs in
  let n = List.length ks in
  let (c::nat) = if n = 0 then 0 else if n < cs|>min_node_keys then 1 else 2 in
  case c of 
  0 \<Rightarrow> (
    (* let _ = check_true (% _. stk_empty) in *)
    return fo)
  | Suc 0 \<Rightarrow> (return (D_small_node(ks,rs)))
  | _ \<Rightarrow> (
    (ks,rs)|>mk_Disk_node|>(store_ops|>store_alloc)|>bind (% r.
    return (D_updated_subtree(r)))))"



(* node steal -------------- *)

(* args are left split node context, focus, right sib; returns updated parent *)
definition node_steal_right :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM" 
where
"node_steal_right store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (k2#rest,r2#rest') \<Rightarrow> 
  case (p|>r_ks2,p|>r_ts2) of (k1#ks2,_#rs2) \<Rightarrow>   
  (ks1@[k1],rs1@[r2]) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r3.
  (rest,rest') |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4.
  p \<lparr> r_t:=r3, r_ks2:=k2#ks2, r_ts2:=r4#rs2 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"


definition node_steal_left :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM" 
where
"node_steal_left store_ops p c1 c2 = (
  let c1 = (c1 |> (% (x,y). (rev x, rev y))) in
  case c1 of (k1#rest,r1#rest') \<Rightarrow>
  case c2 of (ks2,rs2) \<Rightarrow>
  case (p|>r_ks1,p|>r_ts1) of (k2#ks1,_#rs1) \<Rightarrow>
  (rev rest,rev rest') |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r3.
  (k2#ks2,r1#rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4.
  p \<lparr> r_ks1:=k1#ks1, r_ts1:=r3#rs1, r_t:=r4 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"



(* node merge ----------------- *)

definition node_merge_right :: 
  "constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> (('k,'v,'r)fo,'t) MM"
where
"node_merge_right cs store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (ks2,rs2) \<Rightarrow> 
  case (p|>r_ks2,p|>r_ts2) of (k2#ks2,_#p_rs2) \<Rightarrow>   
  (ks1@[k2]@ks2,rs1@rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4. 
  p \<lparr> r_t:=r4, r_ks2:=ks2, r_ts2:=p_rs2 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  maybe_fixup_empty_parent_after_merge cs store_ops (ks,rs) (D_updated_subtree r4))))"


definition node_merge_left :: 
"constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> (('k,'v,'r)fo,'t) MM"
where
"node_merge_left cs store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (ks2,rs2) \<Rightarrow> 
  case (p|>r_ks1,p|>r_ts1) of (k2#ks1,_#p_rs1) \<Rightarrow>   
  (ks1@[k2]@ks2,rs1@rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4. 
  p \<lparr> r_t:=r4, r_ks1:=ks1, r_ts1:=p_rs1 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  maybe_fixup_empty_parent_after_merge cs store_ops (ks,rs) (D_updated_subtree r4))))"


(* leaf steal --------------------- *)

type_synonym ('k,'v) leaf = "('k * 'v) list"

(* parent, left, right *)
type_synonym ('k,'a) l3 = "('k,'a) rsplit_node * ('k,'a) leaf * ('k,'a) leaf"
type_synonym ('k,'a) l2 = "('k,'a) rsplit_node * ('k,'a) leaf"


definition leaf_steal_right :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r,'t) MM"  
where
"leaf_steal_right store_ops p c1 c2 = (
  case c2 of k3#k4#kvs2 \<Rightarrow> 
  case (p|>r_ks2,p|>r_ts2) of (k2#ks2,_#p_rs2) \<Rightarrow>   
  (c1@[k3]) |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r1.
  (k4#kvs2) |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r2.
  p \<lparr> r_t:=r1, r_ks2:=(fst k4)#ks2, r_ts2:=r2#p_rs2 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"


definition leaf_steal_left :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r,'t) MM"  
where
"leaf_steal_left store_ops p c1 c2 = (
  let c1 = rev c1 in
  case c1 of k2#kvs1 \<Rightarrow>
  case (p|>r_ks1,p|>r_ts1) of (k3#ks1,_#p_rs1) \<Rightarrow>   
  rev kvs1 |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r1.
  (k2#c2) |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r2.
  p \<lparr> r_t:=r2, r_ks1:=(fst k2)#ks1, r_ts1:=r1#p_rs1 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"



(* leaf merge -------------------------- *)

definition leaf_merge_right :: 
  "constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> (('k,'v,'r)fo,'t) MM"  
where
"leaf_merge_right cs store_ops p c1 c2 = (
  case (p|>r_ks2,p|>r_ts2) of (k2#ks2,_#p_rs2) \<Rightarrow>   
  (c1@c2) |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r1.
  p \<lparr> r_t:=r1, r_ks2:=ks2, r_ts2:=p_rs2 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  maybe_fixup_empty_parent_after_merge cs store_ops (ks,rs) (D_updated_subtree r1))))"

definition leaf_merge_left :: 
  "constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> (('k,'v,'r)fo,'t) MM"  
where
"leaf_merge_left cs store_ops p c1 c2 = (
  case (p|>r_ks1,p|>r_ts1) of (k2#ks1,_#p_rs1) \<Rightarrow>   
  (c1@c2) |> Disk_leaf |> (store_ops|>store_alloc) |> bind (% r1.
  p \<lparr> r_t:=r1, r_ks1:=ks1, r_ts1:=p_rs1 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  maybe_fixup_empty_parent_after_merge cs store_ops (ks,rs) (D_updated_subtree r1))))"





(* delete ----------------------------------------------------------  *)

definition step_up :: "('k,'v,'r,'t)ps1 \<Rightarrow>('k,'v,'r)u \<Rightarrow> (('k,'v,'r)u,'t) MM" where
"step_up ps1 du = (
  let (f,stk) = du in
  let store_ops = ps1|>dot_store_ops in
  let (alloc,read) = (store_ops|>store_alloc,store_ops|>store_read) in
  let cs = ps1|>dot_constants in
  case stk of [] \<Rightarrow> (impossible1 (STR ''delete, step_up'')) | p#stk' \<Rightarrow> (
  (* NOTE p is the parent *)
  (* take the result of what follows, and add the stk' component *)
  (% x. x |> fmap (% y. (y,stk'))) (case f of   
  D_updated_subtree r \<Rightarrow> (
    unsplit_node (p\<lparr>r_t:=r\<rparr>) |> mk_Disk_node |> alloc |> fmap D_updated_subtree)
  | D_small_leaf(kvs) \<Rightarrow> (
    let no_right_sibling = is_Nil' (p|>r_ks2) in
    case no_right_sibling of 
    True \<Rightarrow> (
      (* steal or merge from left *)
      let ks1 = p|>r_ks1 in
      let _ = check_true (% _. case ks1 of [] \<Rightarrow> False | _ \<Rightarrow> True) in
      let r = List.hd (p|>r_ts1) in
      r |> read |> fmap (% frm. dest_Disk_leaf frm) |> bind (% left_kvs. 
      case List.length left_kvs = cs|>min_leaf_size of
      True \<Rightarrow> leaf_merge_left cs store_ops p left_kvs kvs
      | False \<Rightarrow> leaf_steal_left store_ops p left_kvs kvs |> fmap D_updated_subtree))
    | False \<Rightarrow> (
      (* steal or merge from right *)
      let r = List.hd (p|>r_ts2) in
      r |> read |> fmap (% frm. dest_Disk_leaf frm) |> bind (% right_kvs. 
      case List.length right_kvs = cs|>min_leaf_size of
      True \<Rightarrow> leaf_merge_right cs store_ops p kvs right_kvs
      | False \<Rightarrow> leaf_steal_right store_ops p kvs right_kvs |> fmap D_updated_subtree)))
  | D_small_node(ks,rs) \<Rightarrow> (
    let no_right_sibling = is_Nil' (p|>r_ks2) in
    case no_right_sibling of 
    True \<Rightarrow> (
      (* steal or merge from left *)
      let ks1 = p|>r_ks1 in
      let _ = check_true (% _. case ks1 of [] \<Rightarrow> False | _ \<Rightarrow> True) in
      let r = List.hd (p|>r_ts1) in
      r |> read |> fmap (% frm. dest_Disk_node frm) |> bind (% (l_ks,l_rs). 
      case List.length l_ks = cs|>min_node_keys of
      True \<Rightarrow> node_merge_left cs store_ops p (l_ks,l_rs) (ks,rs)
      | False \<Rightarrow> node_steal_left store_ops p (l_ks,l_rs) (ks,rs) |> fmap D_updated_subtree))
    | False \<Rightarrow> (
      (* steal or merge from right *)
      let r = List.hd (p|>r_ts2) in
      r |> read |> fmap (% frm. dest_Disk_node frm) |> bind (% (r_ks,r_rs). 
      case List.length r_ks = cs|>min_node_keys of
      True \<Rightarrow> node_merge_right cs store_ops p (ks,rs) (r_ks,r_rs)
      | False \<Rightarrow> node_steal_right store_ops p (ks,rs) (r_ks,r_rs) |> fmap D_updated_subtree))))))"


definition delete_step :: 
  "('k,'v,'r,'t)ps1 \<Rightarrow> ('k,'v,'r)delete_state \<Rightarrow> (('k,'v,'r)delete_state,'t) MM" 
where
"delete_step ps1 s = (
  let store_ops = ps1|>dot_store_ops in
  let alloc = store_ops|>store_alloc in
  case s of 
  D_down(f,r0) \<Rightarrow> (
    case (dest_f_finished f) of
    None \<Rightarrow> (find_step ps1 f |> fmap (% f'. D_down(f',r0)))
    | Some x \<Rightarrow> (
      let (r0,k,r,kvs,stk) = x in
      (store_ops|>store_free) (r0#(r_stk_to_rs stk)) |> bind (% _.
      let something_to_delete = (? x : set (kvs|>List.map fst). key_eq (ps1|>dot_cmp) x k) in
      case something_to_delete of
      True \<Rightarrow> (
        let kvs' = kvs|>List.filter (% x. ~ (key_eq (ps1|>dot_cmp) (fst x) k)) in
        case (List.length kvs' < ps1|>dot_constants|>min_leaf_size) of
        True \<Rightarrow> (return (D_up(D_small_leaf(kvs'),stk,r0)))
        | False \<Rightarrow> (Disk_leaf(kvs') |> alloc |> fmap (% r. D_up(D_updated_subtree(r),stk,r0))))
      | False \<Rightarrow> (return (D_finished r0) ))))
  | D_up(f,stk,r0) \<Rightarrow> (
    case is_Nil' stk of
    True \<Rightarrow> (
      case f of
      D_small_leaf kvs \<Rightarrow> (Disk_leaf(kvs)|>alloc|>fmap D_finished)
      | D_small_node (ks,rs) \<Rightarrow> (mk_Disk_node(ks,rs)|>alloc|>fmap D_finished)
      | D_updated_subtree(r) \<Rightarrow> (return (D_finished r)))
    | False \<Rightarrow> (step_up ps1 (f,stk) |> fmap (% (f,stk). D_up(f,stk,r0))))
  | D_finished(r) \<Rightarrow> (return s)  (* stutter *))"


(* wellformedness --------------------------------------------------- *)

definition wf_d :: "'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v) tree \<Rightarrow> 't \<Rightarrow> ('k,'v,'r) d \<Rightarrow> bool" where
"wf_d k_ord r2f t0 s d =  assert_true (
  let (fs,r) = d in
  assert_true (wellformed_find_state k_ord r2f t0 s fs)
)"

definition wf_u :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v) tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> ('k,'v,'r)u \<Rightarrow> bool" 
where
"wf_u constants k_ord r2t t0 s k u =  assert_true (
  let (fo,stk) = u in
  let check_stack = % rstk tstk. (rstack_equal (rstk|>rstack_map (r2t s)|>no_focus) (tstk|>rstack_map Some|>no_focus)) in
  let check_wf = % ms t. (wellformed_tree constants ms k_ord t) in
  let check_focus = % fo kvs. kvs_equal (fo|> tree_to_kvs |> kvs_delete k_ord k) kvs in
  case fo of
  D_small_leaf kvs \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_leaf) in
    assert_true (check_stack stk t_stk) & 
    assert_true (check_wf ms (Leaf kvs)) &
    assert_true (check_focus t_fo kvs)
  )
  | D_small_node (ks,rs) \<Rightarrow> (
    (* FIXME don't we need some wf on Node(ks,rs)? *)
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_node) in
    let t = Node(ks,rs|>List.map (r2t s) |> List.map dest_Some) in  (* FIXME check we can dest_Some *)
    assert_true (check_stack stk t_stk) &
    assert_true (check_wf ms t) &
    assert_true (check_focus t_fo (t|>tree_to_kvs))   
  )
  | D_updated_subtree(r) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> None) in
    let t = r|>r2t s|>dest_Some in  (* FIXME check dest *)
    assert_true (check_stack stk t_stk) &
    assert_true (check_wf ms t) &
    assert_true (check_focus t_fo (t|>tree_to_kvs))   ))"


definition wf_f :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> 'r \<Rightarrow> bool" 
where
"wf_f constants k_ord r2t t0 s k r =  assert_true (
  let t' = r2t s r |> dest_Some in  (* check dest_Some *)
  assert_true (wellformed_tree constants (Some(Small_root_node_or_leaf)) k_ord t') &
  assert_true (kvs_equal ( (t0|>tree_to_kvs|>kvs_delete k_ord k)) (t'|>tree_to_kvs)))"

definition wellformed_delete_state :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> ('k,'v,'r)delete_state \<Rightarrow> bool" 
where
"wellformed_delete_state constants k_ord r2t t0 s k ds =  assert_true (
  case ds of 
  D_down d \<Rightarrow> (wf_d k_ord r2t t0 s d)
  | D_up (fo,stk,r) \<Rightarrow> (
    wf_u constants k_ord r2t t0 s k (fo,stk) & 
    (case r2t s r of None \<Rightarrow> False | Some t \<Rightarrow> tree_equal t t0))
  | D_finished r \<Rightarrow> (wf_f constants k_ord r2t t0 s k r) )"

end


