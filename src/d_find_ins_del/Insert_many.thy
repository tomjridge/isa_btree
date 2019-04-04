theory Insert_many
  imports "$SRC/d_find_ins_del/Post_monad" Find Insert
begin

(* im_step defns ---------------------------------------------------- *)

definition im_step_bottom :: "
constants \<Rightarrow> 
('k ord) \<Rightarrow> 
('k,'v,'leaf) leaf_ops \<Rightarrow>
('k,'r,'node) node_ops \<Rightarrow> 
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>
  ('k,'v,'r,'leaf,'frame) d \<Rightarrow> ('k*'v)s \<Rightarrow> (('k,'v,'r,'frame) u * ('k*'v)s,'t) MM" where
"im_step_bottom cs k_cmp leaf_ops node_ops frame_ops store_ops = (% d kvs0.
  let (fs,v) = d in 
  case dest_F_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,leaf,stk) \<Rightarrow> (
    let (l,u) = get_bounds frame_ops stk in
    \<comment> \<open> insert as many as possible, subject to bounds \<close>
    let step = (% s.
      let (leaf,len_leaf,kvs) = s in
      case kvs of [] \<Rightarrow> None | (k,v)#kvs \<Rightarrow> (
      let _ = check_true (% _. len_leaf \<le> (cs|>max_leaf_size)*2) in
      let test1 = len_leaf = (cs|>max_leaf_size)*2 in
      let test2 = (case u of None \<Rightarrow> False | Some u \<Rightarrow> key_le k_cmp u k) in 
      case test1 \<or> test2 of
      True \<Rightarrow> None
      | False \<Rightarrow> (
        let (leaf,old_v) = (leaf_ops|>leaf_insert) k v leaf in
        let len_leaf = (if is_None old_v then len_leaf+1 else len_leaf) in
        Some(leaf,len_leaf,kvs)
      )))
    in
    iter_step step (leaf,(leaf_ops|>leaf_length) leaf,kvs0) 
    |> (% (leaf,len_leaf,kvs).
    case len_leaf \<le> cs|>max_leaf_size of
    True \<Rightarrow> (
      Disk_leaf leaf |> (store_ops|>wrte) |> fmap (% r'. ((I1(r'),stk),kvs)))
    | False \<Rightarrow> (
      let (leaf1,k',leaf2) = (leaf_ops|>split_large_leaf) (cs|>max_leaf_size) leaf in
      Disk_leaf leaf1 |> (store_ops|>wrte) |> bind (% r1. 
      Disk_leaf leaf2 |> (store_ops|>wrte) |> fmap (% r2. ((I2(r1,k',r2),stk),kvs)))) )))"


definition im_step :: "
constants \<Rightarrow> 
('k ord) \<Rightarrow> 
('k,'v,'leaf) leaf_ops \<Rightarrow>
('k,'r,'node) node_ops \<Rightarrow> 
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>
 ('k,'v,'r,'leaf,'frame) im_state \<Rightarrow> (('k,'v,'r,'leaf,'frame) im_state, 't) MM" where
"im_step cs k_cmp leaf_ops node_ops frame_ops store_ops im = (
  let (i,kvs) = im in
  case i of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case dest_F_finished fs of 
    None \<Rightarrow> (insert_step cs leaf_ops node_ops frame_ops store_ops i |> fmap (% d. (d,kvs)))
    | Some _ \<Rightarrow> (im_step_bottom cs k_cmp leaf_ops node_ops frame_ops store_ops d kvs |> fmap (% (u,kvs). (I_up u,kvs))))
  | I_up u \<Rightarrow> (insert_step cs leaf_ops node_ops frame_ops store_ops i |> fmap (% u. (u,kvs)))
  | I_finished _ \<Rightarrow> failwith (STR ''im_step 1'')
  | I_finished_with_mutate \<Rightarrow> failwith (STR '' im_step 2'')
)"

end