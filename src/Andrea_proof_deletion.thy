theory Andrea_proof_deletion
imports Delete_tree_stack Key_lt_order
begin

(*begin insert up invariant*)
definition invariant_wf_del_ts :: "bool" where
"invariant_wf_del_ts == (
! ts.
  wellformed_del_ts ts --> 
(
let ts' = step_del_tree_stack ts in
case ts' of 
None => True
| Some ts' => (
wellformed_del_ts ts'
)
))
"

lemma wellformed_context_hereditary: "wellformed_context (x#xs) ==> wellformed_context xs"
apply (case_tac xs,auto)
done


lemma invariant_wf_ts: "invariant_wf_del_ts"
apply (subgoal_tac "1 <= min_leaf_size & 1 <= min_node_keys & (max_node_keys = 2 * min_node_keys | max_node_keys = Suc (2 * min_node_keys))") prefer 2 apply (force intro:FIXME) (* further hypothesis*)
(*we need that keys can be ordered*)
apply (subgoal_tac "total_order_key_lte") prefer 2 apply (force intro:FIXME)

apply (simp add:invariant_wf_del_ts_def)
apply(intro allI impI)
apply(case_tac ts)
apply(case_tac x)
apply(rename_tac f stk)
apply (case_tac "step_del_tree_stack ts") apply force
apply(simp add: step_del_tree_stack_def dest_del_ts_def)
apply(case_tac stk) apply(force)
apply (rename_tac hd_stk remaining_stk)
apply (subgoal_tac "? lb n i rb. hd_stk = (lb,(n,i),rb)") prefer 2 apply force
apply (erule exE)+
apply (simp)
apply (thin_tac "x=_")
apply (thin_tac "hd_stk=_")
apply(simp add: wellformed_del_ts_def dest_del_ts_def)
apply(elim conjE)
apply (case_tac n,rename_tac ks rs)
apply simp
apply (thin_tac "n=_")
apply (case_tac a)
apply simp
apply (case_tac x)
apply (rename_tac ks rs)
apply simp
apply (rename_tac f' stk')
apply rule
 (*begin wf_focus subproof*)
 apply (simp add:wellformed_del_focus_def)
 apply (case_tac "remaining_stk")
  (*remaining_stk = []  -- we are in root*)
  apply simp
  apply (case_tac f)
   (*f = DUp*)
   apply force

   (*f = DUp_after_stealing*)
   apply simp
   apply (case_tac x2)
   apply (rename_tac "stealing" "stolen" "key" "wsr")
   apply simp
   apply (subgoal_tac "? tree . f' = DUp tree") prefer 2 apply (case_tac "wsr",rename_tac b, case_tac "b") apply force apply force
   apply (erule exE)
   apply simp
   apply (subgoal_tac "n = (ksa,rsa)") prefer 2 apply (fast intro:FIXME)
   apply (case_tac "wsr",rename_tac b, case_tac "b")
    (*b = True *)
    apply (case_tac n) apply simp
    apply (erule conjE)
    apply (drule_tac t="tree" in sym)
    apply clarsimp
    apply (fast intro:FIXME)
   
    (*b = False*)
    apply (fast intro:FIXME)
   (*f = DDelete*)
   apply (fast intro:FIXME)

  (*remaining_stk ~= [] -- we are somewhere into the tree*)
  apply (fast intro:FIXME)
 (*end wf_focus subproof*)
apply rule
 (*begin wf_context subproof*)
 apply (fast intro:FIXME)
 (*end wf_context subproof*)
(*begin wf_ts1 subproof*)
apply (fast intro:FIXME)
(*end wf_ts1 subproof*)
done
(*end insert up invariant*)

end