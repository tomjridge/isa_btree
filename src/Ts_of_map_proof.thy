(* [[file:~/workspace/agenda/myTasks.org::*proof%20ts_to_map_invariant][proof\ ts_to_map_invariant\ \[2/5\]:1]] *)
theory Ts_of_map_proof
imports Key_lt_order Find_tree_stack Insert_tree_stack (*Andrea_proof*)
begin
lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma map_addE1: "map_le f g --> (f++g = g)"
apply (simp add:map_le_def)
apply (simp add:map_add_def) 
apply rule+
 apply (case_tac " g x",force,force)
done

lemma map_addE2: "map_le f g --> (g++f = g)"
apply (simp add:map_le_def)
apply (simp add:map_add_def) 
apply rule+
apply (case_tac " f x",force,force)
done

lemma distinct_keys_in_leaf:
"!  ms. total_order_key_lte --> wellformed_tree ms (Leaf(kvs)) --> distinct (map fst (List.concat (tree_to_leaves (Leaf(kvs)))))"
apply simp
apply rule+
apply (erule exE)
apply (subgoal_tac "keys_ordered (Leaf kvs)") prefer 2 apply (force simp add:wellformed_tree_def)
apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan Let_def atLeast0LessThan lessThan_def check_keys_def)
apply (thin_tac "wellformed_tree ms (Leaf kvs)")
apply (induct kvs,force)
(*(a # kvs)*)
apply simp
apply (subgoal_tac "\<forall>i<length (kvs). key_lt (fst a) (fst (kvs ! i))") prefer 2
 apply (subgoal_tac "\<forall>i<length (a#kvs) - 1. key_lt (fst ((a#kvs)!0)) (fst ((a#kvs) ! Suc i))")
 prefer 2
  apply rule+
  apply (subgoal_tac "(a#kvs) ~= []") prefer 2 apply (force)
  apply (subgoal_tac "!i : {0..<length (a#kvs) - Suc 0}. key_lt (fst ((a#kvs) ! i)) (fst ((a#kvs) ! Suc i))") prefer 2 apply force 
  apply (smt One_nat_def Suc_mono atLeastLessThan_iff hd_smallest_in_list_sorted_by_key_lt length_Cons length_map length_tl less_Suc_eq list.sel(3) list.size(3) neq0_conv nth_map)
 apply force
apply (subgoal_tac "\<forall>i<length kvs - 1. key_lt (fst ((kvs) ! i)) (fst (kvs ! Suc i))")
prefer 2
 apply (metis Suc_diff_1 Suc_mono diff_0_eq_0 less_nat_zero_code neq0_conv nth_Cons_Suc)
apply (thin_tac "\<forall>i<length kvs. key_lt (fst ((a # kvs) ! i)) (fst (kvs ! i))")
apply rule
 apply (metis imageE in_set_conv_nth key_lt_implies_neq)

 apply (case_tac "kvs",force+)
done

lemma distinct_kv_in_tree:
"!  ms. total_order_key_lte --> wellformed_tree ms t --> distinct (List.concat (tree_to_leaves t))"
apply rule+
apply (subgoal_tac "keys_consistent t") prefer 2 apply (force simp add:wellformed_tree_def)
apply (subgoal_tac "! kvs. t = Leaf kvs --> distinct (map fst (List.concat (tree_to_leaves t)))") prefer 2 apply (metis distinct_keys_in_leaf)
apply (thin_tac "wellformed_tree ms t")
apply (induct t rule:Tree.induct) prefer 2
 apply (metis distinct_zipI1 zip_map_fst_snd)
 
 
 apply (case_tac x)
 apply (rename_tac ks rs)
 apply simp
 apply (simp add:snds_def sndsp.simps del:tree_to_leaves.simps)
 apply (simp add:rev_apply_def)
 apply (subgoal_tac "keys_ordered (Node(ks,rs))") prefer 2 apply (force intro:FIXME)
 apply (induct_tac rs) (*FIXME I am not sure it is allowed*)
 apply force
 (*inductive step on rs*)
 apply (rename_tac h tl)
 apply simp
 apply (subgoal_tac "h : set rs") prefer 2  apply (force intro:FIXME)
 apply rule+
  (* distinct concat tree_to_leaves h *)
  apply (subgoal_tac "keys_consistent h") prefer 2 apply (force intro:FIXME)
  apply (subgoal_tac "\<forall>kvs. h = Leaf kvs \<longrightarrow> distinct (map fst kvs)") prefer 2 apply (force intro:FIXME)
  apply force
  
  (*this should be solvable with keys_consistent*)
  apply (force intro:FIXME)
sorry

lemma distinct_keys_in_leaves:
"!  ms. total_order_key_lte --> wellformed_tree ms t --> distinct (map fst (List.concat (tree_to_leaves t)))"
apply rule+
apply (subgoal_tac "distinct (List.concat (tree_to_leaves t))") prefer 2 apply (simp add:distinct_kv_in_tree del:tree_to_leaves.simps)
apply (unfold distinct_map inj_on_def id_def)
apply rule+
 apply force
apply rule+
 apply force
apply clarsimp
apply (subgoal_tac "(aa, b) = (aa,ba)") prefer 2
 apply (subgoal_tac "x ~= xa --> (inter (set x) (set xa)) = {}") prefer 2 apply (fast intro:FIXME)
 (*probably better to show directly that keys are unique?*)
 apply (fast intro:FIXME)
apply force
done

lemma map_le_subtrees:
"! t ks rs ms. 
let pt = (Node(ks,rs)) in
(
total_order_key_lte -->
wellformed_tree ms pt -->
t : set rs -->
map_le (tree_to_map t) (tree_to_map pt))"
apply (simp add:Let_def)
apply rule+
apply (erule exE)
apply (subgoal_tac "distinct (map fst (List.concat (tree_to_leaves (Node(ks,rs)))))")
prefer 2
 apply (simp add:wellformed_context_1_def)
 using distinct_keys_in_leaves apply force
apply (subgoal_tac "? xs ys. rs = xs@t#ys")
prefer 2
 using split_list apply fast
apply (erule exE)+
apply (simp add:rev_apply_def map_le_def tree_to_map_def)
apply rule+
apply (rename_tac "key")
apply (subgoal_tac "~ key : dom(map_of (concat (concat (map tree_to_leaves ys)))) & ~ key : dom(map_of (concat (concat (map tree_to_leaves xs))))")
prefer 2
 apply (simp add:dom_def map_of_eq_None_iff)
 apply (simp add:keys_def rev_apply_def keys_1_def)
 apply (erule conjE)+
 apply (subgoal_tac "? xsks. fst ` (\<Union>x\<in>set xs. \<Union>x\<in>set (case x of Node (l, cs) \<Rightarrow> cs |> map tree_to_leaves |> concat | Leaf l \<Rightarrow> [l]). set x) = xsks") prefer 2 apply force
 apply (erule exE)
 apply simp
 apply (subgoal_tac "? ysks. fst ` (\<Union>x\<in>set ys. \<Union>x\<in>set (case x of Node (l, cs) \<Rightarrow> cs |> map tree_to_leaves |> concat | Leaf l \<Rightarrow> [l]). set x) = ysks") prefer 2 apply force
 apply (erule exE)
 apply simp
 apply (blast)
apply (simp add:map_add_dom_app_simps(1) map_add_dom_app_simps(3))
done

lemma ctx_map_le: 
"
1 < length ctx -->
wellformed_context ctx -->
(
let (_,((ks,rs),_),_) = hd ctx in
let ctx' = tl ctx in
map_le (tree_to_map (Node(ks,rs))) (ctx_to_map ctx'))
"

apply rule+
apply (simp add:Let_def)
apply (induct ctx,force)
apply (rename_tac ctx_h ctx_t)
apply simp
apply (case_tac ctx_t,force)
apply (rename_tac ctx_h1 ctx_t1)
apply simp
apply (subgoal_tac "? l ks rs i u. ctx_h = (l,((ks,rs),i),u)") prefer 2 apply force
apply (erule exE)+
apply simp
apply (subgoal_tac "? l1 ks1 rs1 i1 u1. ctx_h1 = (l1,((ks1,rs1),i1),u1)") prefer 2 apply force
apply (erule exE)+
apply (subgoal_tac "ctx_to_map (ctx_h1 # ctx_t1) = (tree_to_map (Node(ks1,rs1)) ++ ctx_to_map ctx_t1)")
prefer 2
 apply (force intro:FIXME)
apply simp
apply (subgoal_tac "map_le (tree_to_map (Node (ks, rs))) (tree_to_map (Node (ks1, rs1)))")
prefer 2
 apply (force intro:FIXME)
(*let's simplify the inductive hp*)
apply (case_tac ctx_t1)
 (*ctx_t1 = []*)
 apply (force simp add:ctx_to_map_def)

 (*ctx_t1 ~= []*)
 apply (simp)
 using map_addE1 map_le_trans apply fastforce
done

(*begin findmapts invariant*)
definition invariant_find_map_fts :: "bool" where
"invariant_find_map_fts = (
!fts.
let fts' = step_fts fts in
let m_eq_m' = (
 let m = fts_to_map fts in
 (case fts' of None => True
 | Some fts' =>
 let m' = fts_to_map fts' in
 m = m'))
in
total_order_key_lte -->
wellformed_fts fts -->
(case fts' of None => True | Some fts' => wellformed_fts fts') -->  (*FIXME: remove! this is given by Insert_step_up_proof*)
m_eq_m')
"
(*end findmapts invariant*)


lemma invariant_find_map_fts: "invariant_find_map_fts"
apply (simp add:invariant_find_map_fts_def Let_def)
apply rule+
apply (case_tac "step_fts fts",force)
apply simp
apply (rename_tac fts')
apply (simp add:step_fts_def)
apply (subgoal_tac "? f ctx. (Tree_stack((Focus f),ctx)) = fts") prefer 2 apply (case_tac fts,rename_tac fc,simp,case_tac fc,rename_tac f ctx,simp,case_tac f,force)
apply (erule exE)+
apply (subgoal_tac "? k t. dest_f_tree_stack (Tree_stack (Focus f, ctx)) = (k,t,ctx)") prefer 2 apply (simp add:dest_f_tree_stack_def,case_tac f,force)
apply (erule exE)+
apply simp
apply (subgoal_tac "? lb rb. ((case ctx of [] \<Rightarrow> (None, None) | (lb, xb, xc) # xa => (lb, xc)) = (lb,rb))") prefer 2 apply force
apply (erule exE)+
apply simp
apply (case_tac "t") prefer 2 apply force
apply simp
apply (rename_tac ksrs)
apply (case_tac ksrs)
apply (rename_tac ks rs)
apply (simp add:Let_def)
apply (subgoal_tac "? l u. get_lower_upper_keys_for_node_t ks lb (search_key_to_index ks k) rb = (l,u)") prefer 2 apply force
apply (erule exE)+
apply simp
apply (thin_tac "ksrs=_")
apply (thin_tac "t=_")
apply simp
apply (subgoal_tac "(fts_to_tree fts) = (fts_to_tree fts')")
prefer 2
 apply (drule_tac t="fts" in sym)
 apply (drule_tac t="fts'" in sym)
 apply simp
 apply (case_tac ctx)
  apply (force simp add:list_replace_1_at_n_def dest_f_tree_stack_def)+
apply (force simp add:fts_to_map_def rev_apply_def)
done

definition invariant_find_map_fts1 :: "bool" where
"invariant_find_map_fts1 = (
!fts.
let fts' = step_fts fts in
let m_eq_m' = (
 let m = fts_to_map1 fts in
 (case fts' of None => True
 | Some fts' =>
 let m' = fts_to_map1 fts' in
 m = m'))
in
total_order_key_lte -->
wellformed_fts fts -->
(case fts' of None => True | Some fts' => wellformed_fts fts') -->  (*FIXME: remove! this is given by Insert_step_up_proof*)
m_eq_m')
"
lemma invariant_find_map_fts1: "invariant_find_map_fts1"
apply (simp add:invariant_find_map_fts1_def Let_def)
apply rule+
apply (case_tac "step_fts fts",force)
apply simp
apply (rename_tac fts')
apply (simp add:step_fts_def)
apply (subgoal_tac "? k t ctx. dest_f_tree_stack fts = (k,t,ctx)")
prefer 2
 apply (case_tac fts)
 apply (rename_tac ts)
 apply (case_tac ts)
 apply (rename_tac f ctx)
 apply (case_tac f)
 apply (force simp add:dest_f_tree_stack_def)
apply (erule exE)+
apply simp
apply (subgoal_tac "? lb rb. ((case ctx of [] \<Rightarrow> (None, None) | (lb, xb, xc) # xa => (lb, xc)) = (lb,rb))") prefer 2 apply force
apply (erule exE)+
apply simp
apply (case_tac "t") prefer 2 apply force
apply simp
apply (rename_tac ksrs)
apply (case_tac ksrs)
apply (rename_tac ks rs)
apply (simp add:Let_def)
apply (subgoal_tac "? l u. get_lower_upper_keys_for_node_t ks lb (search_key_to_index ks k) rb = (l,u)") prefer 2 apply force
apply (erule exE)+
apply simp
apply (thin_tac "ksrs=_")
apply (thin_tac "t=_")
apply (simp add:fts_to_map1_def)
apply (subgoal_tac "? t' ctx'. dest_f_tree_stack fts' = (k,t',ctx')")
prefer 2
 apply (case_tac fts)
 apply (rename_tac ts)
 apply (case_tac ts)
 apply (rename_tac f ctx)
 apply (case_tac f)
 apply (force simp add:dest_f_tree_stack_def)
apply (erule exE)+
apply (simp add:rev_apply_def)
apply (subgoal_tac "? m_kvs. tree_to_map t' = m_kvs") prefer 2 apply force
apply (erule exE)
apply (subgoal_tac "? ctx'_h.  (l,((ks,rs),(search_key_to_index ks k)),u) = ctx'_h") prefer 2 apply force
apply (erule exE)
apply (subgoal_tac "ctx' =ctx'_h#ctx")
prefer 2
 apply (drule_tac t="ctx'_h" in sym)
 apply (drule_tac t="fts'" in sym)
 apply (force simp add:dest_f_tree_stack_def)
apply (subgoal_tac "? map_of_ctx. (ctx_to_map ctx) = map_of_ctx") prefer 2 apply force
apply (erule exE)
apply simp
apply (subgoal_tac "? map_of_ctx'_h. tree_to_map (Node(ks,rs)) = map_of_ctx'_h") prefer 2 apply force
apply (erule exE)
apply simp
apply (subgoal_tac "ctx ~= [] --> ctx_to_map ctx' = map_of_ctx'_h++(map_of_ctx)")
prefer 2
 apply (case_tac ctx) apply force
 apply simp
 apply (rename_tac ctx_h ctx_t)
 apply (subgoal_tac "map_le map_of_ctx'_h map_of_ctx")
 prefer 2
  apply (subgoal_tac "wellformed_context ctx'") prefer 2 apply (force simp add:wellformed_fts_def)
  apply (subgoal_tac "1 < length ctx'") prefer 2 apply force
  using ctx_map_le apply (fastforce)
 apply (subgoal_tac "ctx_to_map ctx' = map_of_ctx ++ map_of_ctx'_h") prefer 2 apply (force simp add: tree_to_map_def ctx_to_map_def)
 apply (metis map_le_iff_map_add_commute map_le_map_add map_le_trans)
apply (simp add:rev_apply_def)
apply (subgoal_tac "m_kvs ++ map_of_ctx'_h = map_of_ctx'_h")
prefer 2
 apply (subgoal_tac "map_le m_kvs map_of_ctx'_h")
 prefer 2
  (*this demonstration should be equivalent to the other subgoal about map_le*)
  (*wellformed_fts_1 tells us that t' belongs to the context*)
  (*probably worth creating a fake ctx head to reuse the ctx_map_le lemma, nope because we would not know this fake is wf_ctx *)
  (*we need a predicate that is more general, something like:
    ! t. wf_tree t --> ! subtree. map_le msubtree mt
  can I reuse this for ctx? I think so, since all I have to do is showing that ctx heads are subnodes.
  *)
  apply (subgoal_tac "? ms. (if ctx = [] then Some Small_root_node_or_leaf else None) = ms") prefer 2 apply force
  apply (erule exE)+
  apply (subgoal_tac "t' : set rs & wellformed_tree ms (Node(ks,rs))")
  prefer 2
   apply (simp add:wellformed_fts_def)
   apply (simp add:wellformed_fts_focus_def)
   apply (simp add:wellformed_fts_1_def)
   apply (drule_tac t=ctx'_h in sym)
   apply simp
   apply (subgoal_tac "search_key_to_index ks k < length rs")
   prefer 2
    apply (simp add:search_key_to_index_def)
    apply (subgoal_tac "length ks = (length rs -1) & length rs ~= 0")
    prefer 2 
     (*wf_tree Node(ks,rs)*)
     apply (force intro:FIXME)
    apply (simp add:Let_def)
    apply (case_tac "find (\<lambda>x. key_lt k (ks ! x)) [0..<length rs - Suc 0]",force)
    apply simp
    apply (simp add:find_Some_iff)
    apply (erule exE)+
    apply force
   apply force
  using map_le_subtrees
  apply (drule_tac x="t'" in spec)
  apply (drule_tac x="ks" in spec)
  apply (drule_tac x="rs" in spec)
  apply (drule_tac x="ms" in spec)
  apply force
 apply (force simp add: map_addE1)
apply (case_tac "ctx")
apply (force simp add:tree_to_map_def ctx_to_map_def rev_apply_def)+
done


(*begin stepupmapts invariant*)
definition invariant_step_up_map_its :: "bool" where
"invariant_step_up_map_its = (
!its.
let its' = step_up its in
let m_eq_m' = (
 let m = its_to_map its in
 (case its' of None => True
 | Some its' =>
 let m' = its_to_map its' in
 m = m'))
in
total_order_key_lte -->
wellformed_ts its -->
(case its' of None => True | Some its' => wellformed_ts its') -->  (*FIXME: remove! this is given by Insert_step_up_proof*)
m_eq_m')
"
(*end stepupmapts invariant*)

lemma invariant_step_up_map_its: "invariant_step_up_map_its"
apply (simp add:invariant_step_up_map_its_def Let_def)
apply rule+
apply (case_tac "step_up its",force)
apply simp
apply (rename_tac ts)
apply (simp add:step_up_def)
apply (subgoal_tac "? f ctx. its = Tree_stack (Focus f, ctx)")
prefer 2
 apply (case_tac its)
 apply (rename_tac fctx)
 apply (case_tac fctx)
 apply (rename_tac tf ctx)
 apply (case_tac tf,force)
apply (erule exE)+
apply (simp add:dest_ts_def)
apply (case_tac ctx,force)
apply (rename_tac ctx_h ctx_t)
apply simp
apply (subgoal_tac "? l ks rs i u. ctx_h = (l,((ks,rs),i),u)") prefer 2 apply force
apply (erule exE)+
apply simp
apply (drule_tac t = ts in sym)
apply (subgoal_tac "? f' . (update_focus_at_position (ks, rs) i f) = f' ") prefer 2 apply (force)
apply (erule exE)
apply (force simp add:its_to_map_def dest_ts_def rev_apply_def)
done

(*begin stepbottommapts invariant*)
definition invariant_step_bottom_map_its :: "bool" where
"invariant_step_bottom_map_its = (
!fts k v.
let its = step_bottom fts v in
let m_eq_m' = (
 let m = fts_to_map fts in
 (case its of None => True
 | Some its =>
 let m' = its_to_map its in
 m' = m(k \<mapsto> v)))
in
total_order_key_lte -->
wellformed_fts fts -->
(case its of None => True | Some its => wellformed_ts its) -->  (*FIXME: remove! this is given by Insert_step_bottom_proof*)
m_eq_m')
"
(*end stepbottommapts invariant*)

definition invariant_step_bottom_map_its1 :: "bool" where
"invariant_step_bottom_map_its1 = (
!fts k v.
let its = step_bottom fts v in
let m_eq_m' = (
 let m = fts_to_map1 fts in
 (case its of None => True
 | Some its =>
 let m' = its_to_map1 its in
 m' = m(k \<mapsto> v)))
in
total_order_key_lte -->
wellformed_fts fts -->
(case its of None => True | Some its => wellformed_ts its) -->  (*FIXME: remove! this is given by Insert_step_bottom_proof*)
m_eq_m')
"

lemma invariant_step_bottom_map_its1: "invariant_step_bottom_map_its1"
apply (simp add:invariant_step_bottom_map_its1_def Let_def)
apply rule+
apply (case_tac "step_bottom fts v",force)
apply (rename_tac its)
apply (subgoal_tac "? k f ctx. Tree_stack(Focus f,ctx) = fts") prefer 2 apply (force intro:FIXME)
apply (erule exE)+
apply (simp add:step_bottom_def)
apply (subgoal_tac "dest_f_tree_stack fts = (k, snd f, ctx)") prefer 2 apply (force intro:FIXME)
apply simp
apply (case_tac "snd f",force)
apply (rename_tac kvs)
apply (simp add:Let_def)
apply (subgoal_tac "? kvs2. list_ordered_insert (\<lambda>x. key_lt (fst x) k) (k, v) kvs (\<exists>a b. find (\<lambda>x. key_eq k (fst x)) kvs = Some (a, b)) = kvs2 ") prefer 2 apply force
apply (erule exE)
apply (simp add:fts_to_map1_def its_to_map1_def)
(*this can be solved by case_tac ts, case_tac ctx, ctx_map_le and map_le_subtrees*)
(*FIXME the only big problem is that I still do not know how to show that keys are distinct in a node*)
sorry

lemma invariant_step_bottom_map_its: "invariant_step_bottom_map_its"
apply (simp add:invariant_step_bottom_map_its_def Let_def)
apply rule+
apply (case_tac "step_bottom fts v",force)
apply (rename_tac its)
apply (subgoal_tac "? k f ctx. Tree_stack(Focus f,ctx) = fts") prefer 2 apply (force intro:FIXME)
apply (erule exE)+
apply (simp add:step_bottom_def)
apply (subgoal_tac "dest_f_tree_stack fts = (k, snd f, ctx)") prefer 2 apply (force intro:FIXME)
apply simp
apply (case_tac "snd f",force)
apply (rename_tac kvs)
apply (simp add:Let_def)
apply (subgoal_tac "? kvs2. list_ordered_insert (\<lambda>x. key_lt (fst x) k) (k, v) kvs (\<exists>a b. find (\<lambda>x. key_eq k (fst x)) kvs = Some (a, b)) = kvs2 ") prefer 2 apply force
apply (erule exE)
apply (subgoal_tac "? some_keys some_other_keys. its_to_map its = map_of (some_keys@kvs2@some_other_keys) 
  ")
prefer 2
 apply (simp add:its_to_map_def rev_apply_def tree_to_map_def)
 apply (case_tac "(\<exists>a b. find (\<lambda>x. key_eq k (fst x)) kvs = Some (a, b)) \<or> length kvs < max_leaf_size")
  apply simp
  apply (drule_tac t=its in sym)
  apply simp
  apply (force intro:FIXME)
  apply (force intro:FIXME)
apply (erule exE)+
apply (subgoal_tac "fts_to_map fts = map_of (some_keys@kvs@some_other_keys)")
prefer 2
 (*FIXME the solution should be equivalent to the previous subgoal,
 I need to change the fts_to_tree def
 *)
 apply (force intro:FIXME)
apply (simp add:list_ordered_insert_def Let_def)
apply (subgoal_tac "map_of kvs2 = map_of kvs (k \<mapsto> v)")
prefer 2
 (*here I need the distinct*)
 apply (force intro:FIXME)
apply simp
apply (subgoal_tac "k ~: dom (map_of some_keys)")
prefer 2
 (*here I need the distinct*)
 
 apply (force intro:FIXME)
apply (simp add: map_add_upd_left)
done

(*begin find map invariant*)
definition invariant_find_map :: "bool" where
"invariant_find_map  = (
! fts v.
let m = fts_to_map fts in
let (k,f,ctx) = dest_f_tree_stack fts in
let focus_leaves = (concat (tree_to_leaves f)) in
let k_in_map_and_f =
 if m k = Some v 
 then  (k,v) : set (focus_leaves)
 else (k,v) ~: set (focus_leaves)
in
total_order_key_lte -->
wellformed_fts fts -->
k_in_map_and_f
)"
(*end find map invariant*)

lemma invariant_find_map: "invariant_find_map"
apply (simp add:invariant_find_map_def)
apply clarsimp
apply (rename_tac f ctx)
apply (rule)
 (*fts_to_map fts k = Some v \<longrightarrow> (\<exists>x\<in>set (case f of Node (l, cs) \<Rightarrow> cs |> map tree_to_leaves |> concat | Leaf l \<Rightarrow> [l]). (k, v) \<in> set x)*)
 apply clarsimp
 (*it seems that map_of_eq_Some_iff could be useful, but I need distinct on the keys.
   Also wf_fts1 tells us that the key is in the focus.
 *)
 apply (simp add:fts_to_map_def rev_apply_def)
 apply (force intro:FIXME)

 (*fts_to_map fts k \<noteq> Some v \<longrightarrow> (\<forall>x\<in>set (case f of Node (l, cs) \<Rightarrow> cs |> map tree_to_leaves |> concat | Leaf l \<Rightarrow> [l]). (k, v) \<notin> set x)*)
 apply (force intro:FIXME)
done
end
(* proof\ ts_to_map_invariant\ \[2/5\]:1 ends here *)
