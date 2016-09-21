theory Find_proof
imports Key_value_proof Find_tree_stack
begin

(*begin find invariant*)
definition invariant_wf_fts :: "bool" where
"invariant_wf_fts = (
  total_order_key_lte --> (
  ! fts.
  let wellformed_fts' = (
    let fts' = step_fts fts in
    case fts' of None => True | Some fts' => wellformed_fts fts')
  in
 wellformed_fts fts --> wellformed_fts'))
"
(*end find invariant*)

(* FIXME andrea: this is a very important lemma ! ! ! *)
lemma wellformed_tree_children: "wellformed_tree x (Node(ks,rs)) \<longrightarrow> (! r : set(rs). wellformed_tree None r)"
  apply(force intro: FIXME)
  done


(*
lemma wellformed_context_cons: "wellformed_context (x#xs) = (wellformed_context_1 (x#xs) & wellformed_cnodewellformed_context xs)"
  apply(simp)
  done
*)

(* FIXME move *)
lemma keys_Cons: 
"keys (Node (l, cs)) = l@((List.map keys cs) |> List.concat)"
apply (simp add:keys_def rev_apply_def keys_1_def)
apply (induct cs) apply (force simp add:keys_def rev_apply_def)+
done

(* intuitively, we examine all the possible cases... *)
lemma invariant_wf_fts: "invariant_wf_fts"
apply (simp add:invariant_wf_fts_def)
apply(intro impI allI)
apply(simp add: step_fts_def)
apply(subgoal_tac "? k t ts. fts = Fts_state(k,t,ts)") prefer 2 apply(force intro: FIXME)
apply(elim exE, simp)
apply(simp add: dest_fts_state_t_def)
apply(subgoal_tac "(? ks rs. t = Node(ks,rs)) | (? kvs. t = Leaf kvs)") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* t = Node(ks,rs) *)
 apply(elim exE, simp)
 apply(subgoal_tac "? i. search_key_to_index ks k = i") prefer 2 apply(force)
 apply(elim exE, simp)
 apply(subgoal_tac "
   ? xtra. (get_lu_for_child_with_parent_default (get_parent_bounds ts) ((ks, rs), i) = xtra)") prefer 2 apply(force)
 apply(elim exE, simp)
 apply(subgoal_tac "? l0 u0. xtra = (l0,u0)") prefer 2 apply(force intro: FIXME)
 apply(elim exE)
 apply(simp)
 apply(thin_tac "t=_")
 apply(thin_tac "xtra = _")
 apply(subgoal_tac "i : set(subtree_indexes (ks,rs))") prefer 2 apply(force intro:FIXME)
 apply(subgoal_tac "? r. r : set(rs) &  (rs ! i) = r") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE, simp)
 apply(simp add: wellformed_fts_def)
 apply(simp add: dest_fts_state_t_def)
 apply(elim conjE)
 apply(intro conjI)
  (* wellformed_fts_focus rs!x since wf_fts_1 Node(_,rs) *)
  apply(simp add: wellformed_fts_focus_def)
  (* since Node(ks,rs) is wellformed, so too is rs!i *)
  apply(subgoal_tac "? ms. wellformed_tree ms (Node(ks,rs))") prefer 2 apply(force)
  apply(elim exE)
  using wellformed_tree_children apply blast

  (* want wellformed_cnode *)
  apply(simp add: wellformed_cnode_def dest_cnode_t_def)
  apply(rule conjI)
   (* want wellformed_tree *)
   apply(subgoal_tac "ts = Nil | (? cn2 rest. ts = cn2#rest)") prefer 2 apply(force intro: FIXME)
   apply(elim disjE)
    apply(simp)
    apply(force simp add: wellformed_fts_focus_def)

    apply(elim exE, simp)
    apply(force simp add: wellformed_fts_focus_def)

   (* check_keys l0 (keys r) u0 ; suppose pb is a bound for rs, then lget_lu_with_def is a bound for rs!i *)
    apply(force intro: FIXME)

  (* want wellformed_fts_1 k,r,cn1#ts *)
  apply(simp add: wellformed_fts_1_def dest_fts_state_t_def dest_cnode_t_def)
  (* want check_keys l0 [k] u0 - this comes from the fact that k is the search key, and this is bounded *)
  (* FIXME need lemma about get_lu_for_child *)
  apply(force intro: FIXME)

 (* Leaf *)
 apply(force)
done

end
