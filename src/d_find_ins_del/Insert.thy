theory Insert
imports Pre_insert
begin


datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r) d (* down_state *) = "('k,'v,'r)fs*'v"
type_synonym ('k,'v,'r) u (* up_state *) = "('k,'v,'r)fo*('k,'r)rstk"

datatype (dead 'k,dead 'v,dead 'r) insert_state = 
  I_down "('k,'v,'r) d"
  | I_up "('k,'v,'r) u"
  | I_finished 'r

type_synonym ('k,'v,'r) ist = "('k,'v,'r) insert_state"  

definition mk_insert_state :: "'k \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r) insert_state" where
"mk_insert_state k v r = (I_down (mk_find_state k r,v))"


definition dest_i_finished :: "('k,'v,'r) ist \<Rightarrow> 'r option" where
"dest_i_finished s = (case s of I_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"

(* defns ------------------------------------------------------------ *)

definition step_down :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k,'v,'r) d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down ps1 d = (
  let (fs,v) = d in
  find_step ps1 fs |> fmap (% d'. (d',v))
)"

definition step_bottom :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_bottom ps1 d = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  let store_ops = ps1 |> dot_store_ops in
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


definition step_up :: "('k,'v,'r,'t)ps1 \<Rightarrow> ('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_up ps1 u = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  let store_ops = ps1 |> dot_store_ops in
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


definition insert_step :: "('k,'v,'r,'t)ps1 \<Rightarrow> ('k,'v,'r) ist \<Rightarrow> (('k,'v,'r) ist,'t) MM" where
"insert_step ps1 s = (
  let store_ops = ps1 |> dot_store_ops in
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down ps1 d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom ps1 d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 r \<Rightarrow> return (I_finished r)
      | I2(r1,k,r2) \<Rightarrow> (
        (* create a new frame *)
        (mk_Disk_node([k],[r1,r2]) |> (store_ops|>store_alloc) |> fmap (% r. I_finished r))))
    | _ \<Rightarrow> (step_up ps1 u |> fmap (% u. I_up u)))
  | I_finished f \<Rightarrow> (return s)  (* stutter *) )"


(* wellformedness --------------------------------------------------- *)

definition wf_d :: "'k ord \<Rightarrow> ('k,'v,'r,'t) r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> ('k,'v,'r)d \<Rightarrow> bool" where
"wf_d k_ord r2t t0 s d =  assert_true (
  let (fs,v) = d in
  wellformed_find_state k_ord r2t t0 s fs)"


definition wf_u :: "('k,'v,'r,'t) r2t \<Rightarrow> 'k ord \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v,'r)u \<Rightarrow> bool" where
"wf_u r2t k_ord t0 s k v u =  assert_true (
  (* need to check the stack and the focus *)
  let check_focus = % r t. wf_store_tree r2t s r t in
  let check_stack = % rstk tstk. 
    rstack_equal (rstk|>rstack_map (r2t s)|>no_focus) (tstk|>rstack_map Some|>no_focus) 
  in
  let (fo,stk) = u in
  case fo of
  I1 r \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    assert_true (check_stack stk t_stk) &
    (* FIXME need wf_tree r , and below *)
    (case (r2t s r) of 
    None \<Rightarrow> assert_true (False)
    | Some t' \<Rightarrow> assert_true (
      kvs_equal (t' |> tree_to_kvs) (t_fo|>tree_to_kvs|>kvs_insert k_ord (k,v)))))
  | I2 (r1,k',r2) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    assert_true (check_stack stk t_stk) &
    (case (r2t s r1, r2t s r2) of
      (Some t1, Some t2) \<Rightarrow> (
        let (l,u) = rstack_get_bounds t_stk in
        let (ks1,ks2) = (t1|>tree_to_keys,t2|>tree_to_keys) in
        assert_true (check_keys k_ord l ks1 (Some k')) &
        assert_true (check_keys k_ord (Some k') ks2 u) &
        assert_true (kvs_equal (t_fo|>tree_to_kvs|>kvs_insert k_ord (k,v)) (t1|>tree_to_kvs @ (t2|>tree_to_kvs))))
      |(_,_) \<Rightarrow> False )))"


definition wf_f :: "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'r \<Rightarrow> bool" where
"wf_f cs k_ord r2t t0 s k v r =  assert_true (
  case r2t s r of
  None \<Rightarrow> False
  | Some t' \<Rightarrow> (
    wellformed_tree cs (Some(Small_root_node_or_leaf)) k_ord t' &
    kvs_equal ( (t0|>tree_to_kvs|>kvs_insert k_ord (k,v))) (t'|>tree_to_kvs) ))"


definition wellformed_insert_state :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v,'r)ist \<Rightarrow> bool" 
where
"wellformed_insert_state cs k_ord r2t t0 s k v is = assert_true (
  case is of 
  I_down d \<Rightarrow> (wf_d k_ord r2t t0 s d)
  | I_up u \<Rightarrow> (wf_u r2t k_ord t0 s k v u)
  | I_finished r \<Rightarrow> (wf_f cs k_ord r2t t0 s k v r) )"

(* don't bother with wf_trans *)

end