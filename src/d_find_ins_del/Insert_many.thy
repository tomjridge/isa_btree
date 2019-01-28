theory Insert_many
imports Find "$SRC/c_monad/Insert_many_state"
begin

(* NOTE following synonymys copied from Insert_many_state *)
type_synonym ('k,'v,'r) fo = "('k,'v,'r) im_fo"

type_synonym ('k,'v,'r) d = "('k,'v,'r)fs * ('v * ('k*'v)s)"

type_synonym ('k,'v,'r) u = "('k,'v,'r)fo*('k,'r)rstk"


(* defns ------------------------------------------------------------ *)

definition step_down :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r)d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down ps1 store_ops d = (
  let (fs,v) = d in
  find_step ps1 store_ops fs |> fmap (% d'. (d',v))
)"

(* insert kv, and as many from new as possible subject to lu bound and max size of 2*max_leaf_size; 
kv<new, and new are sorted in order; return the remaining new that were not inserted
*)
definition kvs_insert_2 :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> 'k option \<Rightarrow> ('k*'v) \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s \<Rightarrow> ('k*'v)s * ('k*'v)s" 
where
"kvs_insert_2 cs' k_ord u kv new existing = (
  let cs = cs' in
  let step = (% s. 
    let (acc,new') = s in
    case (length acc \<ge> 2 * cs|>max_leaf_size) of
    True \<Rightarrow> None
    | False \<Rightarrow> (
      case new' of
      [] \<Rightarrow> None
      | (k,v)#new'' \<Rightarrow> (
        let test = % k u.
          (* (check_keys (Params.the_kv_ops|>compare_k) None {k} u) *) (* FIXME equality on keys in generated code :( *)
          case u of None \<Rightarrow> True | Some u \<Rightarrow> key_lt k_ord k u
        in
        case test k u of  
        True \<Rightarrow> (Some(kvs_insert k_ord (k,v) acc,new''))
        | False \<Rightarrow> (None))))
  in
  iter_step step (existing,new))"

definition step_bottom :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_bottom ps1 store_ops d = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  (* let store_ops = ps1|>dot_store_ops in *)
  let (fs,(v,kvs0)) = d in
  case dest_f_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    (store_ops|>store_free) (r0#(r_stk_to_rs stk)) |> bind 
    (% _.
    let (l,u) = rstack_get_bounds stk in
    let (kvs',kvs0') = kvs_insert_2 cs k_ord u (k,v) kvs0 kvs in
    let fo = (
      case (length kvs' \<le> cs|>max_leaf_size) of
      True \<Rightarrow> (Disk_leaf kvs' |> (store_ops|>store_alloc) |> fmap (% r'. IM1(r',kvs0')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf cs kvs' in
        Disk_leaf kvs1 |> (store_ops|>store_alloc) |> bind
        (% r1. Disk_leaf kvs2 |> (store_ops|>store_alloc) |> fmap (% r2. IM2((r1,k',r2),kvs0')))) )
    in
    fo |> fmap (% fo. (fo,stk))))
)"

definition step_up :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_up ps1 store_ops u = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  (* let store_ops = ps1|>dot_store_ops in *)
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible1 (STR ''insert, step_up'') (* FIXME what about trace? can't have arb here; or just stutter on I_finished in step? *)
  | x#stk' \<Rightarrow> (
    case fo of
    IM1 (r,kvs0) \<Rightarrow> (
      let (ks,rs) = unsplit_node (x\<lparr>r_t:=r\<rparr>) in
      mk_Disk_node(ks,rs) |> (store_ops|>store_alloc) |> fmap (% r. (IM1 (r,kvs0),stk')))
    | IM2 ((r1,k,r2),kvs0) \<Rightarrow> (
      let (ks2,rs2) = (x|>r_ks2,x|>r_ts2) in
      let (ks',rs') = unsplit_node (x\<lparr> r_t:=r1, r_ks2:=k#ks2, r_ts2:=r2#rs2\<rparr>) in
      case (List.length ks' \<le> cs|>max_node_keys) of
      True \<Rightarrow> (
        mk_Disk_node(ks',rs') |> (store_ops|>store_alloc) |> fmap (% r. (IM1 (r,kvs0),stk')))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node cs (ks',rs') in  (* FIXME move split_node et al to this file *)
        mk_Disk_node(ks_rs1) |> (store_ops|>store_alloc) |> bind
        (% r1. mk_Disk_node (ks_rs2) |> (store_ops|>store_alloc) |> fmap 
        (% r2. (IM2((r1,k,r2),kvs0),stk'))))
    )
  )
)"

definition insert_step :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) imst \<Rightarrow> (('k,'v,'r) imst, 't) MM" where
"insert_step ps1 store_ops s = (
  let (cs,k_ord) = (ps1|>dot_constants,ps1|>dot_cmp) in
  (* let store_ops = ps1|>dot_store_ops in *)
  case s of 
  IM_down d \<Rightarrow> (
    let (fs,(v,kvs0)) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down ps1 store_ops d |> fmap (% d. IM_down d))
    | Some _ \<Rightarrow> step_bottom ps1 store_ops d |> fmap (% u. IM_up u))
  | IM_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      IM1 (r,kvs0) \<Rightarrow> return (IM_finished (r,kvs0))
      | IM2((r1,k,r2),kvs0) \<Rightarrow> (
        (* create a new frame *)
        (mk_Disk_node([k],[r1,r2]) |> (store_ops|>store_alloc) |> fmap (% r. IM_finished (r,kvs0)))))
    | _ \<Rightarrow> (step_up ps1 store_ops u |> fmap (% u. IM_up u)))
  | IM_finished f \<Rightarrow> (return s)  (* stutter *)
)"

end