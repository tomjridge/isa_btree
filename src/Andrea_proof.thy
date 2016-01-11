theory Andrea_proof
imports Insert_tree_stack
begin

definition invariant_wf_ts :: "bool" where
"invariant_wf_ts == (
! ts.
wellformed_ts ts \<longrightarrow> 
(
let ts' = step_tree_stack ts in
case ts' of 
None \<Rightarrow> True
| Some ts' \<Rightarrow> (
wellformed_ts ts'
)
))
"

lemma fst_snd_simps: "((a,b)|>fst = a) & ((a,b)|>snd = b)"
apply(simp add:rev_apply_def)
done
  

lemma wellformed_context_hereditary: "wellformed_context (x#xs) \<Longrightarrow> wellformed_context xs"
apply (case_tac xs)
 apply (force simp add:wellformed_context_def)+
done

lemma list_all_update: "list_all P l \<Longrightarrow> P a \<Longrightarrow> list_all P (l[i := a]) "
by (metis length_list_update list_all_length nth_list_update_eq nth_list_update_neq) 
 
  

lemma invariant_wf_ts: "invariant_wf_ts"
apply(simp add: invariant_wf_ts_def)
apply(intro allI impI)
apply(case_tac ts)
apply(case_tac x)
apply(rename_tac f stk)
apply(simp add: step_tree_stack_def dest_ts_def)
apply(case_tac stk) apply(force)
apply(rename_tac ni stk)
apply(case_tac ni)
apply(rename_tac n i)
apply(simp)
apply(thin_tac "ts = _")
apply(thin_tac "x = _")
apply(thin_tac "stka = _")
apply(thin_tac "ni = _")
apply(simp add: wellformed_ts_def)
apply(simp add: dest_ts_def)
apply(elim conjE)
apply(case_tac n)
apply(rename_tac ks rs)
apply(simp)
apply(subgoal_tac " wellformed_focus (update_focus_at_position (ks, rs) i f) (stk = []) \<and>
       wellformed_context stk")
prefer 2
(* begin subproof *)
apply(intro conjI)
 (* wf_focus *)
 apply(simp add: wellformed_focus_def )
 apply(case_tac f)
  (* inserting_one *) (*A: this case is easier, because the stepped focus can be only insert_one *)
  apply(rename_tac t)
  apply(simp)
  apply(simp add: update_focus_at_position_def)
  apply(subgoal_tac "wellformed_tree (Rmbs (stk=[])) (Node (ks,rs))") (* A: given that the tree without update is wf, we just need to check that rs was wf (replacing an element will leave it as before)*)
  prefer 2
   apply(simp add: wellformed_context_def)
   apply (subgoal_tac "\<exists> ks' rs' i'. (if stk = [] then ((ks, rs), i) else last stk) = ((ks', rs'), i')")
   prefer 2
    apply force
   apply (elim exE)+
   apply simp
   apply (elim conjE)
   apply (case_tac stk)
    (*stk = [] *)
    apply simp
   
    (* stk \<noteq> [] *)
    apply simp
    apply (elim conjE)
    apply (simp add:wellformed_context_1_def)

  apply(simp add: wellformed_tree_def)
  apply(elim conjE)
  apply (simp add:list_replace_1_at_n_def dest_Some_def)
  apply(intro conjI)
   apply(simp add: wf_size_def)
   apply(force intro:FIXME)
   
   apply(force intro:FIXME)

   apply(force intro:FIXME)

   (* keys_consistent; but this follows from wf_ts *)
   apply(force intro:FIXME)

   (* keys ordered *)
   apply(force intro:FIXME)

  (* inserting_two *)
  apply(simp)
  apply(case_tac x2)
  apply(rename_tac tleft k0 tr)
  apply(simp add: update_focus_at_position_def)
  apply(elim conjE)
  apply(thin_tac "x2 = _")
  apply(subgoal_tac "? ks2.  list_insert_at_n (n |> fst) i [k0] = ks2") prefer 2 apply(force)
  apply(subgoal_tac "? rs2. list_replace_at_n (n |> snd) i [tleft, tr] |> dest_Some = rs2") prefer 2 apply(force)
  apply(elim exE)
  apply(simp add: Let_def)
  apply(case_tac "length ks2 \<le> max_node_keys")
   apply(simp)
   apply(force intro: FIXME)

   apply(simp)
   apply(simp add: split_node_def)
   apply(force intro: FIXME)
  

 (* wf_context *)
 apply(force intro: wellformed_context_hereditary)
(* end subproof *)
apply(elim conjE)

apply(simp)
(* wf_ts_1 *)
apply(simp add: update_focus_at_position_def)
apply(case_tac f)
 (* i1 *)
 apply(simp)
 apply(force intro: FIXME)

  (* i2 FIXME may be worth combining with other i2 cases? *)
 apply(simp)
 apply(subgoal_tac "? tleft k0 tr. x2 = (tleft,k0,tr)") prefer 2 apply(force)
 apply(elim exE)
 apply(simp)
 apply(subgoal_tac "? ks2. list_insert_at_n (n |> fst) i [k0]  = ks2") prefer 2 apply(force)
 apply(subgoal_tac "? rs2. list_replace_at_n (n |> snd) i [tleft, tr] |> dest_Some = rs2") prefer 2 apply(force)
 apply(elim exE)
 apply(simp add: Let_def fst_snd_simps)

 apply(force intro: FIXME)
done


end