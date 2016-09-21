theory Find_proof
imports Key_value_proof Find_tree_stack
begin

(*begin find invariant*)
definition invariant_wf_fts :: "bool" where
"invariant_wf_fts == (
! fts.
let wellformed_fts' =
(
let fts' = step_fts fts in
case fts' of None => True
| Some fts' => wellformed_fts fts'
)
in
 total_order_key_lte -->
 wellformed_fts fts --> wellformed_fts'
)"
(*end find invariant*)

(* FIXME andrea: this is a very important lemma ! ! ! *)
lemma wellformed_tree_children: "wellformed_tree x (Node(ks,rs)) \<longrightarrow> (! r : set(rs). wellformed_tree None r)"
  apply(force intro: FIXME)
  done

lemma wellformed_context_cons: "wellformed_context (x#xs) = (
  case xs of 
  Nil \<Rightarrow> wellformed_context_1 (Some Small_root_node_or_leaf) x
  | x2#xs \<Rightarrow> "
  apply(case_tac xs)
  apply(subgoal_tac "? lb ls rs i rb. x = (lb,((ls,rs),i),rb)") prefer 2 apply(force intro:FIXME)
  apply(elim exE)
  apply(simp)

(* FIXME move to lib_proof *)
lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma keys_Cons: 
"keys (Node (l, cs)) = l@((List.map keys cs) |> List.concat)"
apply (simp add:keys_def rev_apply_def keys_1_def)
apply (induct cs) apply (force simp add:keys_def rev_apply_def)+
done

(* intuitively, we examine all the possible cases... *)
lemma invariant_wf_fts: "invariant_wf_fts"
apply (simp add:invariant_wf_fts_def)
apply clarify
apply(simp add: step_fts_def)
apply(simp add: dest_f_tree_stack_def)
apply(subgoal_tac "? k t ctx. fts = Tree_stack (Focus(k,t),ctx)") prefer 2 apply(force intro: FIXME)
apply(elim exE)
apply(simp)
apply(thin_tac "fts=_")
apply(case_tac " case ctx of [] \<Rightarrow> (None, None) | (lb, xb, xc) # xa \<Rightarrow> (lb, xc)")
apply(rename_tac lb rb)
apply(simp)


apply(subgoal_tac "? ks rs x. t = Node(ks,rs) \<or> t = Leaf(x)") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(erule disjE)
 (* t = Node(ks,rs) *)
 apply(simp)
 apply(thin_tac "t=_")
 apply(simp add: Let_def)
 apply(subgoal_tac "? l u. get_lower_upper_keys_for_node_t ks lb (search_key_to_index ks k) rb = (l,u)") prefer 2 apply(force intro:FIXME)
 apply(elim exE)
 apply(simp)
 apply(simp add: wellformed_fts_def dest_f_tree_stack_def)
 apply(intro conjI)
  (* wellformed_fts_focus rs!x since wf_fts_1 Node(_,rs) *)
  apply(simp add: wellformed_fts_focus_def)
  apply(simp add: wellformed_fts_1_def) (* need that wellformed_tree_children *)
  apply(subgoal_tac "? r. r : set(rs) &  (rs ! search_key_to_index ks k) = r") prefer 2 apply(force intro:FIXME)
  apply(elim exE, simp)
  using wellformed_tree_children apply blast

  (* wellformed_context FIXME need lemma about wellformed_context_cons*)
  apply(force intro: FIXME)

  (* wellformed_fts_1 *)
  apply(simp add: wellformed_fts_1_def dest_f_tree_stack_def)
  apply(elim conjE)
  (* need to show check_keys l [k] x *)
  apply(case_tac "ctx")
   apply(simp)
   apply(force intro: FIXME) (* lemma *)

   apply(simp)
   apply(subgoal_tac "? a1 ks2 rs2 n2 a4. a = (a1,((ks2,rs2),n2),a4)") prefer 2 apply(force intro: FIXME)
   apply(elim exE)
   apply(simp)
   (* FIXME lemma about get_lower_upper_keys *)
   apply(force intro: FIXME)


 (* t = Leaf *)   
 apply(force)
done

end
