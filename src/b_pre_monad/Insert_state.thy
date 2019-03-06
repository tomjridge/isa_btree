theory Insert_state
imports Constants_and_size_types Find_state
begin

datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r,'leaf,'frame) d (* down_state *) = "('k,'r,'leaf,'frame)find_state*'v"
type_synonym ('k,'v,'r,'frame) u (* up_state *) = "('k,'v,'r)fo*'frame list"

datatype (dead 'k,dead 'v,dead 'r,'leaf, 'frame) insert_state = 
  I_down "('k,'v,'r,'leaf,'frame) d"
  | I_up "('k,'v,'r,'frame) u"
  | I_finished 'r
  | I_finished_with_mutate


definition make_initial_insert_state :: "'r \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k,'v,'r,'leaf,'frame) insert_state" where
"make_initial_insert_state r k v = (
  let f = make_initial_find_state k r in
  I_down(f,v))"


definition split_leaf :: "constants \<Rightarrow> ('k*'v) s \<Rightarrow> ('k*'v)s * 'k * ('k*'v) s" where "
split_leaf cs kvs = (
  let _ = assert_true True in
  let min = cs|>min_leaf_size in 
  iter_step (% (kvs,kvs',len_kvs').
    case len_kvs' \<le> min of
    True \<Rightarrow> None
    | False \<Rightarrow> (
      case kvs' of 
      [] \<Rightarrow> impossible1 (STR ''split_leaf'')
      | (k,v)#kvs' \<Rightarrow> Some((k,v)#kvs,kvs',len_kvs'-1)))
    ([],kvs,List.length kvs)
  |> (% (kvs,kvs',_). (List.rev kvs,List.hd kvs'|>fst, kvs')))
"

(* NOTE for both split_node and split_leaf, we may know the order is dense, and all keys have values; in which case we can split
with a full left leaf/node *)
definition split_node :: 
  "constants \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" 
where
"split_node cs n = (
  let (ks,rs) = n in
  let l = List.length ks  div 2 in
  let l = max (cs|>min_node_keys) l in
  iter_step (% (ks,rs,ks',rs').
    case (ks',rs') of 
    (k'#ks',r'#rs') \<Rightarrow> (
      case List.length ks < l of
      True \<Rightarrow> Some(k'#ks,r'#rs,ks',rs')
      | False \<Rightarrow> None)
    | _ \<Rightarrow> (impossible1 (STR ''split_node'')))
    ([],[],ks,rs)
  |> (% (ks,rs,ks',rs').
    case (ks',rs') of
    (k'#ks',r'#rs') \<Rightarrow> (
      (List.rev ks,List.rev(r'#rs)),
      k',
      (ks',rs'))))"



end


(*

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"

(* insert ----------------------------------------------------------- *)

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

*)
