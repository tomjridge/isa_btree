theory Find_proof_2 imports Find_tree_stack begin


declare  wellformed_ts.simps[simp del]

(*
declare wellformed_context_def_2[simp del] (* not a simp? - may expand too far? or use anyway? *)
*)

declare ts_to_ms_def_2[simp] (* likely a simp *)
declare dest_fts_focus_def_2[simp] (* surely a simp *)
declare dest_cnode_t_def_2[simp]

lemma tree_to_leaves_node_eq: "Node(ks,rs) |> tree_to_leaves = rs|>(List.map tree_to_leaves)|>List.concat"
apply(force intro:FIXME)
done


lemma "lem9"
apply(simp add: lem9_def)
apply(intro allI impI)
apply(simp (no_asm) add: fts_invariant_def)
apply(intro allI impI, elim conjE)
apply(rename_tac f ts f' ts')
apply(intro conjI)
 apply(force simp: fts_invariant_def)
 
 (* focus_to_check_keys_2 *)
 apply(simp add: focus_to_check_keys_2_def)
 apply(subgoal_tac "?  k xs l t u zs. f = Focus(k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
 apply(elim exE, simp)
 apply(subgoal_tac "? k' xs' l' t' u' zs'. f' = Focus(k',xs',l',t',u',zs')") prefer 2 apply(force intro:FIXME)
 apply(elim exE, simp)
 apply(simp add: step_fts_def)
 apply(case_tac t) prefer 2 apply(force)
 apply(simp)
 apply(case_tac x1) apply(simp) apply(rename_tac ks rs)
 apply(subgoal_tac "
   ? i cn ts2 t2 l2 u2.
   (search_key_to_index ks k = i) &
    (Cnode(xs,l,ks,rs,i,u,zs) = cn) &
    ((cn # ts2) = ts) &
    (rs!i = t2) &
    (cnode_to_bound cn = (l2,u2)) 

") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE)
 apply(simp add: Let_def)
 apply(elim conjE)
 apply(simp add: check_keys_2_def)
 (* and these are all fairly easy - see lem 7 below *)
 apply(force intro:FIXME)
 
 
 (* focus_to_leaves - this requires much the same sort of reasoning, so FIXME we should be able to combine with above? *)
 apply(subgoal_tac "?  k xs l t u zs. f = Focus(k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
 apply(elim exE, simp)
 apply(subgoal_tac "? k' xs' l' t' u' zs'. f' = Focus(k',xs',l',t',u',zs')") prefer 2 apply(force intro:FIXME)
 apply(elim exE, simp)
 apply(simp add: focus_to_leaves_def)
 apply(drule_tac t=ls in sym) apply(simp)
 apply(clarsimp)
 apply(simp add: step_fts_def)
 apply(case_tac t) prefer 2 apply(force)
 apply(simp)
 apply(case_tac x1) apply(simp) apply(rename_tac ks rs)
 apply(subgoal_tac "
   ? i cn ts2 t2 l2 u2.
   (search_key_to_index ks k = i) &
    (Cnode(xs,l,ks,rs,i,u,zs) = cn) &
    ((cn # ts2) = ts) &
    (rs!i = t2) &
    (cnode_to_bound cn = (l2,u2)) 

") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE)
 apply(simp add: Let_def)
 apply(elim conjE)
 apply(drule_tac t=i in sym) apply(simp)
 (* and this is just a lemma about tree_to_leaves on a node *)
 apply(simp add: tree_to_leaves_node_eq)
 apply(drule_tac t=xs' in sym) apply(simp)
 apply(drule_tac t=zs' in sym) apply(simp)
 apply(drule_tac s=i in sym) apply(simp)
 apply(drule_tac t=t' in sym) apply(simp)
 apply(subgoal_tac "rs |> map tree_to_leaves = (
   let rsi = % i. rs!i in
   let xs = (from_to 0 (i-1))|> List.map rsi in
   let ys = [i] |> List.map rsi in
   let zs = (from_to (i+1) (ks_to_max_child_index ks)) |> List.map rsi in
   (xs@ys@zs) |> map tree_to_leaves)")
  prefer 2 apply(force intro: FIXME)
 apply(simp add: Let_def)
 apply(simp add: rev_apply_def)
 apply(simp add: indexes_to_leaves_def)
 apply(simp add: rev_apply_def)
 apply(subgoal_tac "tree_to_leaves o (op ! rs) = (% j. let r = tree_to_leaves (rs!j) in r)") prefer 2 apply(force intro: FIXME)
 apply(force)
 done

lemma "lem7"
apply(simp add: lem7_def) 
apply(intro allI)
apply(intro impI)
apply(rule)
apply(rule_tac nat_induct)
 apply(simp)
 apply(elim conjE)
 apply(drule_tac t="f 0" in sym)
 apply(simp)
 apply(simp add: tree_to_fts_def)
 apply(elim conjE)
 apply(drule_tac t="f0" in sym)
 apply(simp)
 apply(intro impI)
 apply(simp add: check_keys_2_def rev_apply_def leaves_to_map_def check_keys_def)
 apply(force intro:FIXME)
 
 apply(rename_tac na n)
 apply(elim conjE)
 apply(case_tac "f n")
  apply(simp)
  apply(subgoal_tac "f (Suc n) = None") prefer 2 apply(force intro: FIXME)
  apply(force)
 apply(simp)
 apply(rename_tac fn)
 apply(case_tac "f (Suc n)") apply(force)
 apply(rename_tac fn')
 apply(simp)
 apply(case_tac fn')
 apply(rename_tac f_n' ts_n')
 apply(simp)
 apply(simp add: tree_to_fts_def) apply(elim conjE)
 apply(drule_tac t=f0 in sym)
 apply(simp)
 apply(subgoal_tac "? k' xs' l' t' u' zs'. f_n' = Focus(k',xs',l',t',u',zs')") prefer 2 apply(force intro:FIXME)
 apply(elim exE)
 apply(simp)
 apply(intro impI)
 apply(subgoal_tac "step_fts fn = Some fn'") prefer 2 apply(force intro: FIXME)
 apply(simp)
 apply(subgoal_tac "? f_n ts_n. fn = (f_n,ts_n)") prefer 2 apply(force intro:FIXME)
 apply(elim exE, simp)
 apply(subgoal_tac "? k xs l t u zs. f_n = Focus(k,xs,l,t,u,zs)") prefer 2 apply(force intro:FIXME)
 apply(elim exE)
 apply(simp)
 apply(simp add: check_keys_2_def)
 apply(simp add: step_fts_def)
 apply(erule impE) apply(force intro:FIXME)
 apply(elim conjE)
 apply(case_tac t) prefer 2 apply(force)
 apply(subgoal_tac "? ks rs. x1 = (ks,rs)") prefer 2 apply(force)
 apply(elim exE)
 apply(simp)
 apply(rule) apply(force intro:FIXME)
 apply(rule) apply(force intro:FIXME)
 (* want check_keys ... & check_keys & check_keys *)
 apply(subgoal_tac "
   ? i cn ts2 t2 l2 u2 indexes_to_leaves.
   (search_key_to_index ks k = i) &
    (Cnode(xs,l,ks,rs,i,u,zs) = cn) &
    ((cn # ts_n) = ts2) &
    (rs!i = t2) &
    (cnode_to_bound cn = (l2,u2)) &
    ((% is. is |> List.map (% j. tree_to_leaves (rs!j)) |> List.concat) = indexes_to_leaves)
") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE)
 apply(simp add: Let_def)
 apply(elim conjE)
 apply(clarsimp)
 apply(simp add: rev_apply_def)
 apply(intro conjI)
  (* 4 subgoals *)
  apply(simp add: check_keys_def)
  apply(case_tac l') apply(force)
  apply(rename_tac l')
  apply(simp)
  apply(rule)
  (* l' is a lower bound - xs is already bounded; may need l \<le> l' FIXME add to ind hyp *)
  apply(force intro: FIXME)
  
  apply(simp add: check_keys_def)
  (* examine l' and u' - they bound the subtree *)
  apply(force intro:FIXME)
  
  apply(simp add: check_keys_def)
  (* u' is an upper bound -as l' *)
  apply(force intro:FIXME)
  apply(subgoal_tac "k' = k0") prefer 2 apply(force intro:FIXME) (* FIXME add to ind *)
  apply(simp)
  (* need to use induction hyp *)
  apply(force intro: FIXME)
done
end