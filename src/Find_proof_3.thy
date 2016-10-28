theory 
Find_proof_3 imports 
Find_tree_stack begin

lemma invariant_wf_fts: "invariant_wf_fts_lem"
apply(simp add: invariant_wf_fts_lem_def)
apply(simp add: invariant_def)
apply(intro allI impI)
apply(rename_tac f ts f' ts')
apply(simp add: fts_trans_def)
apply(subgoal_tac "? k xs l t u zs. f|>dest_fts_focus|>dest_core = (k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
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
apply(subgoal_tac "
   (?  i.  (search_key_to_index ks k = i) &
   (? cn. ((
      let core = mk_core (k,xs,l,t,u,zs) in
      let ksrsi = (| cc_ks=ks,cc_rs=rs,cc_i=i |) in
      (core,ksrsi)) = cn) &
    (? ts2. ((cn # ts) = ts2)) &
    (* new focus ----- *)
    (? isx isy. ((from_to 0 (i-1), i, from_to (i+1) (ks_to_max_child_index ks)) = (isx,i,isy)) &
    (? tsx t2 tsy. ((indexes_to_trees rs isx, rs!i, indexes_to_trees rs isy) = (tsx,t2,tsy)) & 
    (? xs' zs'. (
      (tsx |> List.map tree_to_leaves |> List.concat, tsy |> List.map tree_to_leaves |> List.concat) = (xs',zs'))
    &  
    (? l2 u2. cnode_to_bound cn  = (l2,u2)))))))
  ") prefer 2 apply(force)
apply(elim exE conjE)
apply(simp add: step_fts_def)
apply(elim conjE)
apply(drule_tac t = ts' in sym)
apply(simp)
apply(simp (no_asm) add: wellformed_fts_def)
apply(intro conjI)
 (* 3 subgs *)
 (* wf_ts ts' *)
 apply(simp add: wellformed_ts_def_2)
 apply(intro conjI)
  (* wf_cnode *)
  apply(drule_tac t=cn in sym)
  apply(simp)
  apply(simp add: wellformed_cnode_def)
  (* wf_core f *)
  (* should follow from wf_fts *)
  apply(simp add: wellformed_fts_def)
  apply(simp add: wellformed_fts_focus_def)
  apply(force simp add: wellformed_core_def)
   
  (* wf_ts ts*)
  (* from wf_fts *)
  apply(force simp add: wellformed_fts_def)
   
 (* wf_fts_focus f' *)
 apply(drule_tac t=f' in sym)
 apply(simp)
 apply(simp add: wellformed_fts_focus_def)
 (* wf_core f' *)
 apply(simp add: wellformed_core_def)
 apply(intro conjI)
  (* wf_tree t2 *)
  (* ts = rs ! i, and use wf_focus f *)
  apply(simp add: wellformed_fts_def) apply(elim conjE)
  apply(simp add: wellformed_fts_focus_def)
  apply(simp add: wellformed_core_def)
  (* now have wf_tree Node(ks,rs) *)
  apply(force intro: FIXME )
  
  (* ck2 xs@xs' etc; the difficult part *)
  apply(force intro: FIXME)
  
 (* wellformed_fts_1 f' *)
 apply(simp add: wellformed_fts_1_def)
 apply(drule_tac t=cn in sym)
 apply(simp)
 apply(drule_tac t=f' in sym)
 apply(force)
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
apply(subgoal_tac "? k xs l t u zs. f|>dest_fts_focus|>dest_core = (k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
apply(elim exE)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. (t = Node(ks,rs)))") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* Leaf *)
 apply(elim exE)
 apply(force simp add: step_fts_def)
(* Node(ks,rs) *)
apply(elim exE)
(* unfolding of step_fts let bindings *)
apply(subgoal_tac "
   (?  i.  (search_key_to_index ks k = i) &
   (? cn. ((
      let core = mk_core (k,xs,l,t,u,zs) in
      let ksrsi = (| cc_ks=ks,cc_rs=rs,cc_i=i |) in
      (core,ksrsi)) = cn) &
    (? ts2. ((cn # ts) = ts2)) &
    (* new focus ----- *)
    (? isx isy. ((from_to 0 (i-1), i, from_to (i+1) (ks_to_max_child_index ks)) = (isx,i,isy)) &
    (? tsx t2 tsy. ((indexes_to_trees rs isx, rs!i, indexes_to_trees rs isy) = (tsx,t2,tsy)) & 
    (? xs' zs'. (
      (tsx |> List.map tree_to_leaves |> List.concat, tsy |> List.map tree_to_leaves |> List.concat) = (xs',zs'))
    &  
    (? l2 u2. cnode_to_bound cn  = (l2,u2)))))))
  ") prefer 2 apply(force)
apply(elim exE conjE)
apply(simp add: focus_to_leaves_def)
apply(simp add: step_fts_def)
apply(elim conjE)
apply(drule_tac t=f' in sym)
apply(simp)
apply(simp add: mk_core_def dest_fts_focus_def rev_apply_def dest_core_def)
apply(simp add: cnode_to_bound_def)
apply(simp add: index_to_bound_def)
apply(subgoal_tac "rs = tsx@[t2]@tsy") prefer 2 apply(force intro: FIXME)
apply(simp)
done



lemma invariant_leaves: "invariant_leaves_lem"
using lem_2 sorry

end