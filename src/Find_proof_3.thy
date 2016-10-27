theory Find_proof_3 imports Find_tree_stack begin

lemma invariant_wf_fts: "invariant_wf_fts_b"
sorry

definition guard :: "'a \<Rightarrow> 'a" where "guard a = a"

lemma map_comp: "map (f o g) xs = map f (map g xs)" apply(force) done


lemma i2: "
! ls P Q. 
 ((% fts. wellformed_fts k0 fts) = P) \<longrightarrow>
((% fts. focus_to_leaves (fst fts) = ls) = Q) \<longrightarrow>
fts_invariant P \<longrightarrow> fts_invariant (% fts. P fts & Q fts)" 
apply(intro allI)
apply(intro impI)
apply(simp add:fts_invariant_def)
apply(simp add: invariant_def)
apply(intro allI impI)
apply(rename_tac f ts f' ts')
apply(drule_tac x=f in spec)
apply(drule_tac x=ts in spec)
apply(drule_tac x=f' in spec)
apply(drule_tac x=ts' in spec)
apply(simp)
apply(elim conjE)
apply(drule_tac t=Q in sym)
apply(simp)
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

lemma invariant_leaves: "invariant_leaves_b"
using i2 sorry

end