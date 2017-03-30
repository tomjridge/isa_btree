theory 
Find_proof_4 imports 
Find_tree_stack begin


lemma wf_child: "
  p|>f_t = (ks,rs) \<Longrightarrow>
  wf_core k0 (Node(ks,rs)|>tree_to_keys) p \<Longrightarrow>
  mk_child p = c \<Longrightarrow>
  wf_core k0 (c|>f_t|>tree_to_keys) c
"
sorry


lemma wf_new_fts: "
wellformed_fts k0 (f, ts) \<Longrightarrow>
       f |> dest_core = (k0, xs, l, Node (ks, rs), u, zs) \<Longrightarrow>
       wellformed_fts k0 (mk_child (f |> with_t (\<lambda>_. (ks, rs))), f |> with_t (\<lambda>_. (ks, rs)) # ts)
"   
apply(simp add: wellformed_fts_def)
apply(elim conjE)
apply(subgoal_tac "? p. (f|>with_t (% _. (ks,rs))) = p") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(simp)
apply(subgoal_tac "p|>dest_core = (k0,xs,l,(ks,rs),u,zs)") prefer 2 apply(force intro:FIXME)
apply(subgoal_tac "? c. mk_child p = c") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(simp)
apply(subgoal_tac "wf_core k0 (c|>f_t|>tree_to_keys) c") prefer 2 apply(force intro:FIXME)
apply(intro conjI)
 (* wf_ts p#ts *)
 apply(simp add: wellformed_ts_def_2)
 apply(intro conjI)
  apply(simp add: wf_nf_def)
  apply(simp add: wellformed_fts_focus_def Let_def)
  apply(elim conjE)
  apply(drule_tac t=p in sym)
  apply(simp)
  apply(force simp add: wf_core_def)
  
  (* p is from f, the previous focus; but wf_fts_1, so p#ts is wf *)
  apply(simp add: wellformed_fts_1_def)
  apply(case_tac ts) apply(force)
  apply(rename_tac y ys)
  apply(simp)
  apply(force simp add: mk_next_frame_def Let_def)
  
 (* wf_fts_focus *)
 apply(simp add: wellformed_fts_focus_def Let_def)
 (* lemma: mk_child has a wf tree *)
 apply(force intro:FIXME)
 
 (* wf_fts_1 *)
 apply(force simp add: wellformed_fts_1_def)
done

lemma invariant_wf_fts: "invariant_wf_fts_lem"
apply(simp add: invariant_wf_fts_lem_def)
apply(simp add: invariant_def)
apply(intro allI impI)
apply(rename_tac f ts f' ts')
apply(simp add: fts_trans_def)
apply(subgoal_tac "? k xs l t u zs. f|>dest_core = (k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(subgoal_tac "k=k0") prefer 2 apply(force intro: FIXME)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. (t = Node(ks,rs)))") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* Leaf *)
 apply(elim exE)
 apply(force simp add: step_fts_def)
(* Node(ks,rs) *)
apply(elim exE)
(* unfolding of step_fts let bindings *)
apply(simp)
apply(simp add: step_fts_def Let_def)
apply(elim conjE)
apply(drule_tac t = f' in sym)
apply(simp)
apply(drule_tac t = ts' in sym)
apply(simp)
using wf_new_fts apply(force)
done

lemma invariant_focus_to_leaves: " 
wellformed_fts k0 (f, ts) \<Longrightarrow>
       wellformed_fts k0 (f', ts') \<Longrightarrow>
       f |> dest_core = (k, xs, l, Node (ks, rs), u, zs) \<Longrightarrow>
       t = Node (ks, rs) \<Longrightarrow> mk_child (f |> with_t (\<lambda>_. (ks, rs))) = f' \<Longrightarrow> f |> with_t (\<lambda>_. (ks, rs)) # ts = ts' \<Longrightarrow> 
       focus_to_leaves f' = focus_to_leaves f
"
apply(subgoal_tac "(f |> with_t (% _. (ks,rs))) |> dest_core = (k,xs,l,(ks,rs),u,zs)") prefer 2 apply(force intro: FIXME)
apply(simp add: mk_child_def)
(* decompose based on split_node *)
apply(subgoal_tac "? i. search_key_to_index ks k = i") prefer 2 apply(force)
apply(elim exE)
apply(simp add: split_node_def)
apply(force intro: FIXME)
done

lemma lem_2: "! P Q.
((% fts. wellformed_fts k0 fts) = P) \<longrightarrow>
((% fts. focus_to_leaves (fst fts) = ls) = Q) \<longrightarrow>
invariant_assuming fts_trans P Q"
apply(simp add: invariant_assuming_def)
apply(simp add: invariant_def)
apply(intro allI impI)
apply(elim exE conjE)
apply(rename_tac f ts f' ts')
apply(simp add: fts_trans_def)
apply(clarsimp)
apply(subgoal_tac "? k xs l t u zs. f|>dest_core = (k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. (t = Node(ks,rs)))") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* Leaf *)
 apply(elim exE)
 apply(force simp add: step_fts_def)
(* Node(ks,rs) *)
apply(elim exE)
(* unfolding of step_fts let bindings *)
(* focus_to_leaves f' = focus_to_leaves f ; the main lemma *)
apply(simp add: step_fts_def Let_def)
apply(elim conjE)
using invariant_focus_to_leaves apply(force)
done

lemma invariant_leaves: "invariant_leaves_lem"
using lem_2 sorry

end