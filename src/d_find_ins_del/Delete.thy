theory Delete imports Find "$SRC/b_pre_monad/Delete_state" begin

(* FIXME merge in documentation from Delete *)

(* NOTE these are repeated from Delete_state, because otherwise they are shadowed by eg insert.fo *)
type_synonym ('k,'v,'r)fo = "('k,'v,'r) del_t"  (* focus *)
type_synonym ('k,'v,'r)u = "('k,'v,'r)fo * ('k,'r)stk"  
type_synonym ('k,'v,'r)d = "('k,'v,'r)find_state * 'r"

definition X :: "('a * 'b) \<Rightarrow> ('b * 'a)" where "
X p = (case p of (a,b) \<Rightarrow> (b,a))"

(* node steal ------------------------------------------------------- *)

(* args are left split node context, focus, right sib; returns updated parent

FIXME maybe it makes more sense to deal with the context in isolation, and return r*k*r

NOTE rs,ks as args for node_steal_xxx
 *)
definition node_steal_right :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('r s * 'k s) \<Rightarrow> 'k \<Rightarrow> ('r s * 'k s) \<Rightarrow> ('r*'k*'r,'t) MM" 
where
"node_steal_right store_ops = (
  let write = store_ops|>wrte in
  (% c1 k0 c2.
  case c1 of (rs1,ks1) \<Rightarrow> 
  case c2 of (r1#rs2,k1#ks2) \<Rightarrow> 
  \<comment> \<open> rs1 ks1 | k0  r1 k1 | rs2 ks2) *) \<close>
  Disk_node(ks1@[k0],rs1@[r1]) |> write |> bind (% left.
  Disk_node(ks2,rs2) |> write |> bind (% right.
  return (left,k1,right)))))"


definition node_steal_left :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('r s * 'k s) \<Rightarrow> 'k \<Rightarrow> ('r s * 'k s) \<Rightarrow> ('r*'k*'r,'t) MM" 
where
"node_steal_left store_ops = (
  let write = store_ops|>wrte in
  (% c1 k1 c2.
  let c1 = c1 |> (% (x,y). (rev x, rev y)) in
  case c1 of (r1#rs1,k0#ks0) \<Rightarrow>
  case c2 of (rs2,ks2) \<Rightarrow>
  \<comment> \<open> rs1 ks0 | k0 r1 k1 | rs2 ks2 \<close>
  Disk_node(rev ks0,rev rs1) |> write |> bind (% left.
  Disk_node(k1#ks2,r1#rs2) |> write |> bind (% right.
  return (left,k0,right)))))"


(* node merge ------------------------------------------------------- *)

definition node_merge_right :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k s * 'r s) \<Rightarrow> 'k \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM"
where
"node_merge_right store_ops = (
  let write = store_ops|>wrte in
  (%  c1 k0 c2.
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (ks2,rs2) \<Rightarrow> 
  Disk_node (ks1@[k0]@ks2,rs1@rs2) |> write))"

(* NOTE same as merge right *)
definition node_merge_left :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k s * 'r s) \<Rightarrow> 'k \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM"
where
"node_merge_left store_ops = node_merge_right store_ops"


(* leaf steal ------------------------------------------------------- *)

definition leaf_steal_right :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r * 'k * 'r,'t) MM"  
where
"leaf_steal_right store_ops = (
  let write = store_ops|>wrte in
  (% c1 c2.
  case c2 of kv1#kv2#rest \<Rightarrow> 
  Disk_leaf (c1@[kv1]) |> write |> bind (% left.
  Disk_leaf (kv2#rest) |> write |> bind (% right.
  return (left,(fst kv2),right)))))"


definition leaf_steal_left :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r * 'k * 'r,'t) MM"  
where
"leaf_steal_left store_ops = (
  let write = store_ops|>wrte in
  (% c1 c2.
  let c1 = rev c1 in
  case c1 of kv1#rest \<Rightarrow>
  Disk_leaf(rev rest) |> write |> bind (% left.
  Disk_leaf(kv1#c2) |> write |> bind (% right.
  return (left,(fst kv1),right)))))"


(* leaf merge ------------------------------------------------------- *)

definition leaf_merge_right :: "
  ('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r ,'t) MM" where "
leaf_merge_right store_ops = (
  let write = store_ops|>wrte in
  (% c1 c2.
  let kvs = c1@c2 in
  Disk_leaf kvs |> write))"

(* NOTE same as above *)
definition leaf_merge_left :: 
  "('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('r,'t) MM" where
"leaf_merge_left store_ops = leaf_merge_right store_ops"


(* delete ----------------------------------------------------------  *)

(* after a merge, the parent may become "small", or even have no keys at all if there
was only one key to begin with; this operation tags a node that is small, or even has no
keys at all *)
definition post_merge :: 
  "constants \<Rightarrow> ('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> ('k s * 'r s) \<Rightarrow> (('k,'v,'r)fo,'t)MM"
where
"post_merge cs store_ops krs = (
  let (ks,rs) = krs in
  case List.length ks < cs|>min_node_keys of 
  True \<Rightarrow> (return (D_small_node(ks,rs)))
  | False \<Rightarrow> (
    Disk_node(ks,rs)|>(store_ops|>wrte)|>bind (% r.
    return (D_updated_subtree(r)))))"


definition step_up :: 
  "constants \<Rightarrow> ('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow> 
  ('k,'v,'r)u \<Rightarrow> (('k,'v,'r)u,'t) MM" where
"step_up cs store_ops du = (
  let (f,stk) = du in
  let (read,write) = (store_ops|>read,store_ops|>wrte) in
  let post_merge = post_merge cs store_ops in
  case stk of [] \<Rightarrow> (impossible1 (STR ''delete, step_up'')) | p#stk' \<Rightarrow> (
  \<comment> \<open>(* NOTE p is the parent *)\<close>
  \<comment> \<open>(* take the result of what follows, and add the stk' component *)\<close>
  (% x. x |> fmap (% y. (y,stk'))) (case f of   
  D_updated_subtree r \<Rightarrow> (
    let (rks,_,krs,_) = dest_Frm p in
    unsplit_node (rks, ([r],[]), krs) |> Disk_node |> write |> fmap D_updated_subtree)
  | D_small_leaf(kvs) \<Rightarrow> (
    \<comment> \<open>NOTE stack is not empty, so at least one sibling; then a small leaf is expected to
      have min_leaf_size-1 entries \<close>
    let (rks,_,krs,_) = dest_Frm p in
    let no_right_sibling = is_Nil' (fst krs) in
    case no_right_sibling of 
    True \<Rightarrow> (
      \<comment> \<open>steal or merge from left\<close>
      let _ = check_true (% _. case snd rks of [] \<Rightarrow> False | _ \<Rightarrow> True) in
      case rks of 
      (r1#rs1,_#ks1) \<Rightarrow> 
      r1 |> read |> fmap dest_Disk_leaf |> bind (% left_kvs. 
      case List.length left_kvs = cs|>min_leaf_size of
      True \<Rightarrow> (
        leaf_merge_left store_ops left_kvs kvs |> bind (% r.
        unsplit_node ( (rs1,ks1),([r],[]),krs) |> post_merge))
      | False \<Rightarrow> (
        leaf_steal_left store_ops left_kvs kvs |> bind (% (r1,k1,r2).
        unsplit_node ((rs1,ks1), ([r1,r2],[k1]), krs) |> Disk_node
        |> write |> fmap D_updated_subtree))))
    | False \<Rightarrow> (
      \<comment> \<open>steal or merge from right\<close>
      let _ = check_true (% _. case fst krs of [] \<Rightarrow> False | _ \<Rightarrow> True) in
      case krs of
      (_#ks1,r1#rs1) \<Rightarrow>       
      r1 |> read |> fmap dest_Disk_leaf |> bind (% right_kvs. 
      case List.length right_kvs = cs|>min_leaf_size of
      True \<Rightarrow> (
        leaf_merge_right store_ops kvs right_kvs |> bind (% r.
        unsplit_node (rks,([r],[]),(ks1,rs1)) |> post_merge))
      | False \<Rightarrow> (
        leaf_steal_right store_ops kvs right_kvs |> bind (% (r1,k1,r2). 
        unsplit_node ( rks, ([r1,r2],[k1]), (ks1,rs1)) |> Disk_node
        |> write |> fmap D_updated_subtree)))))
  | D_small_node(ks,rs) \<Rightarrow> (
    let (rks,_,krs,_) = dest_Frm p in
    let no_right_sibling = is_Nil' (fst krs) in
    case no_right_sibling of 
    True \<Rightarrow> (
      \<comment> \<open>steal or merge from left\<close>
      let _ = check_true (% _. case snd rks of [] \<Rightarrow> False | _ \<Rightarrow> True) in
      case rks of 
      (r1#rs1,k1#ks1) \<Rightarrow> 
      r1 |> read |> fmap dest_Disk_node |> bind (% (l_ks,l_rs). 
      case List.length l_ks = cs|>min_node_keys of
      True \<Rightarrow> (
        node_merge_left store_ops (l_ks,l_rs) k1 (ks,rs) |> bind ( % r.
        unsplit_node ( (rs1,ks1), ([r],[]), krs ) |> post_merge))
      | False \<Rightarrow> (
        node_steal_left store_ops (l_rs,l_ks) k1 (rs,ks) |> bind (% (r1,k1,r2). 
        unsplit_node ( (rs1,ks1), ([r1,r2],[k1]), krs ) |>Disk_node
        |> write |> fmap D_updated_subtree))))
    | False \<Rightarrow> (
      \<comment> \<open>steal or merge from right\<close>
      case krs of 
      (k1#ks1,r1#rs1) \<Rightarrow> 
      r1 |> read |> fmap dest_Disk_node |> bind (% (r_ks,r_rs). 
      case List.length r_ks = cs|>min_node_keys of
      True \<Rightarrow> (
        node_merge_right store_ops (ks,rs) k1 (r_ks,r_rs) |> bind (% r. 
        unsplit_node ( rks, ([r],[]), (ks1,rs1)) |> post_merge))
      | False \<Rightarrow> (
        node_steal_right store_ops (rs,ks) k1 (r_rs,r_ks) |> bind (% (r1,k1,r2).
        unsplit_node ( rks, ([r1,r2],[k1]), (ks1,rs1)) |> (% (ks,rs). Disk_node(ks,rs))
        |> write |> fmap D_updated_subtree))))))))
"


definition delete_step :: "constants \<Rightarrow> 'k ord \<Rightarrow> ('r,('k,'v,'r)dnode,'t)store_ops \<Rightarrow>
  ('k,'v,'r)delete_state \<Rightarrow> (('k,'v,'r)delete_state,'t) MM" 
where
"delete_step cs k_cmp store_ops = (
  let write = store_ops|>wrte in
  (% s.
  case s of 
  D_down(f,r0) \<Rightarrow> (
    case dest_F_finished f of
    None \<Rightarrow> (find_step cs k_cmp store_ops f |> fmap (% f'. D_down(f',r0)))
    | Some x \<Rightarrow> (
      let (r0,k,r,kvs,stk) = x in
      \<comment> \<open> (* (store_ops|>free) (r0#(r_stk_to_rs stk)) FIXME *)\<close>
      let something_to_delete = (? x : set (kvs|>List.map fst). key_eq k_cmp x k) in
      case something_to_delete of
      True \<Rightarrow> (
        let kvs' = kvs|>List.filter (% x. ~ (key_eq k_cmp (fst x) k)) in
        case List.length kvs' < cs|>min_leaf_size of
        True \<Rightarrow> (return (D_up(D_small_leaf(kvs'),stk,r0)))
        | False \<Rightarrow> (Disk_leaf(kvs') |> write 
          |> fmap (% r. D_up(D_updated_subtree(r),stk,r0))))
      | False \<Rightarrow> (return (D_finished r0) )))
  | D_up(f,stk,r0) \<Rightarrow> (
    case is_Nil' stk of
    True \<Rightarrow> (
      case f of
      D_small_leaf kvs \<Rightarrow> (Disk_leaf(kvs)|>write|>fmap D_finished)
      | D_small_node (ks,rs) \<Rightarrow> (
        case List.length ks = 0 of
        True \<Rightarrow> return (D_finished (List.hd rs))
        | False \<Rightarrow> (Disk_node(ks,rs)|>write|>fmap D_finished))
      | D_updated_subtree(r) \<Rightarrow> (return (D_finished r)))
    | False \<Rightarrow> (step_up cs store_ops (f,stk) |> fmap (% (f,stk). D_up(f,stk,r0))))
  | D_finished(r) \<Rightarrow> (return s)  \<comment> \<open> (* stutter *)\<close>))"

end

