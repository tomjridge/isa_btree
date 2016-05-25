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
 apply (case_tac "ctx")
  (*ctx = []*)
  apply (simp add:wellformed_fts_focus_def)
  (*FIXME*)
  apply (force intro:FIXME)
  (*ctxt = hd_ctx#tl_ctx*)
  apply (rename_tac hd_ctx tl_ctx)
  apply simp
  (*FIXME*)
sorry
end
