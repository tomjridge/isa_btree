theory Insert
imports Find "$SRC/c_monad/Insert_state"
begin



(* defns ------------------------------------------------------------ *)

definition step_down :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down ps1 store_ops d = (
  let (fs,v) = d in
  find_step ps1 store_ops fs |> fmap (% d'. (d',v))
)"

definition step_bottom :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_bottom ps1 store_ops d = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  (* let store_ops = ps1 |> dot_store_ops in *)
  let (fs,v) = d in
  case dest_f_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    (store_ops|>store_free) (r0#(r_stk_to_rs stk)) |> bind (% _.
    let kvs' = kvs |> kvs_insert k_ord (k,v) in
    let fo = (
      case (length kvs' \<le> (cs|>max_leaf_size)) of
      True \<Rightarrow> (Disk_leaf kvs' |> (store_ops|>store_alloc) |> fmap (% r'. I1(r')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf cs kvs' in
        Disk_leaf kvs1 |> (store_ops|>store_alloc) |> bind
        (% r1. Disk_leaf kvs2 |> (store_ops|>store_alloc) |> fmap (% r2. I2(r1,k',r2)))) )
    in
    fo |> fmap (% fo. (fo,stk)))) )"


definition step_up :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_up ps1 store_ops u = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  (* let store_ops = ps1 |> dot_store_ops in *)
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> 
    (* FIXME what about trace? can't have arb here; or just stutter on I_finished in step? *)
    impossible1 (STR ''insert, step_up'') 
  | p#stk' \<Rightarrow> (
    case fo of
    I1 r \<Rightarrow> (
      let (ks,rs) = unsplit_node (p\<lparr>r_t:=r\<rparr>) in
      mk_Disk_node(ks,rs) |> (store_ops|>store_alloc) |> fmap (% r. (I1 r,stk')))
    | I2 (r1,k,r2) \<Rightarrow> (
      let (ks2,rs2) = (p|>r_ks2,p|>r_ts2) in
      let (ks',rs') = unsplit_node (p\<lparr> r_t:=r1, r_ks2:=k#ks2, r_ts2:=r2#rs2\<rparr>) in
      case (List.length ks' \<le> cs|>max_node_keys) of
      True \<Rightarrow> (
        mk_Disk_node(ks',rs') |> (store_ops|>store_alloc) |> fmap (% r. (I1 r,stk')))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node cs (ks',rs') in  
        mk_Disk_node(ks_rs1) |> (store_ops|>store_alloc) |> bind
        (% r1. mk_Disk_node (ks_rs2) |> (store_ops|>store_alloc) |> fmap 
        (% r2. (I2(r1,k,r2),stk')))) )))"


definition insert_step :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) ist \<Rightarrow> (('k,'v,'r) ist,'t) MM" where
"insert_step ps1 store_ops s = (
  (* let store_ops = ps1 |> dot_store_ops in *)
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down ps1 store_ops d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom ps1 store_ops d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 r \<Rightarrow> return (I_finished r)
      | I2(r1,k,r2) \<Rightarrow> (
        (* create a new frame *)
        (mk_Disk_node([k],[r1,r2]) |> (store_ops|>store_alloc) |> fmap (% r. I_finished r))))
    | _ \<Rightarrow> (step_up ps1 store_ops u |> fmap (% u. I_up u)))
  | I_finished f \<Rightarrow> (return s)  (* stutter *) )"



end