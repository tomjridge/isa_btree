theory Find_proof
imports Find_tree_stack
begin

definition invariant_wf_fts :: "bool" where
"invariant_wf_fts == (
! fts.
 wellformed_fts fts -->
(
let fts' = step_fts fts in
case fts' of None => True
| Some fts' => wellformed_fts fts'
))"

lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma invariant_wf_fts: "invariant_wf_fts"
apply (simp add:invariant_wf_fts_def)
apply clarify
apply (case_tac "step_fts fts",force)
(*step_fts = Some fts'*)
apply simp
apply (rename_tac fts')
apply (simp add:step_fts_def dest_fts_state_def)
apply (case_tac fts,simp)
apply (case_tac x,simp)
apply (rename_tac k node_or_leaf ctx)
apply (thin_tac "x=_")
apply simp
apply (case_tac "case ctx of [] \<Rightarrow> (None, None) | (lb, xb, xc) # xa \<Rightarrow> (lb, xc)")
apply simp
apply (rename_tac lb rb)
apply (case_tac node_or_leaf)
prefer 2
 (*node_or_leaf = Leaf _*)
 apply force

 (*node_or_leaf = Node (ks,rs)*)
 apply (case_tac x1,simp)
 apply (thin_tac "x1=_")
 apply (rename_tac ks rs)
 apply (simp add:Let_def)
 apply (subgoal_tac "? index. search_key_to_index ks k = index") prefer 2 apply (force simp add:search_key_to_index_def Let_def)
 apply (erule exE)
 apply simp
 apply (case_tac "get_lower_upper_keys_for_node_t ks lb index rb")
 apply simp
 apply (rename_tac l u)
 apply (simp add:wellformed_fts_def dest_fts_state_def)
 apply (drule_tac t="fts'" in sym,simp)
 apply (subgoal_tac "length rs = length ks + 1") prefer 2 apply (force simp add:wellformed_fts_focus_def wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
 apply (subgoal_tac "index < length rs")
 prefer 2
  apply (simp add:search_key_to_index_def Let_def, case_tac " List.find (\<lambda>x. key_lt k (ks ! x)) [0..<length ks]",force,simp)
  apply (smt diff_zero find_Some_iff length_upt less_Suc_eq less_diff_conv nth_upt zero_less_diff)
 apply (subgoal_tac "? child. rs ! index =  child") prefer 2 apply force
 apply (erule exE)
 apply simp
 apply (subgoal_tac "child : set rs") prefer 2 apply force 
 apply (subgoal_tac "wellformed_fts_focus (Rmbs False) (rs ! index) ")
 prefer 2
  apply (simp add:wellformed_fts_focus_def wellformed_tree_def)
  apply (subgoal_tac "wf_size (Rmbs False) child") prefer 2 apply (case_tac "ctx = []",(force simp add:Let_def wf_size_def forall_subtrees_def rev_apply_def list_all_iff)+)
  apply (subgoal_tac "wf_ks_rs child") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "balanced child") prefer 2 apply (force simp add:balanced_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "keys_consistent child") prefer 2 apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "keys_ordered child") prefer 2 apply (force simp add:keys_ordered_def forall_subtrees_def rev_apply_def list_all_iff)
  apply force
 apply simp
 apply (case_tac ctx)
 (*ctx = [] *)
 apply (simp add:wellformed_context_1_def Let_def wellformed_fts_focus_def subtree_indexes_def check_keys_def get_lower_upper_keys_for_node_t_def)
 apply rule
  apply (case_tac l) apply force
  apply simp
  apply (subgoal_tac "a = (ks ! (index - 1))") prefer 2 apply (metis option.distinct(1) option.inject)
  apply simp
  apply (simp add:wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def check_keys_def)
  apply (simp add:keys_def rev_apply_def keys_1_def)
  (*ERROR IN DEFINITIONS*)
  apply (fast intro:FIXME)

  apply (case_tac u) apply force
  apply (fast intro:FIXME)

  (*ctx = a#list*)
  apply simp
  apply (fast intro:FIXME)

 (*apply (force simp add:dest_fts_state_def wellformed_fts_1_def)*)
done
end
