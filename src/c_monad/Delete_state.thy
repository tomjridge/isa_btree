theory Delete_state
imports Find_state
begin


(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* delete ----------------------------------------------------------- *)

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