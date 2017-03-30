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
    (? ts2. ((cn # ts) = ts2) &
    (* new focus ----- *)
    (? tsx t2 tsy. (split_list rs i =  (tsx,t2,tsy)) & 
    (? xs' zs'. (
      (tsx |> List.map tree_to_leaves |> List.concat, tsy |> List.map tree_to_leaves |> List.concat) = (xs',zs'))
    &  
    (? l2 u2. cnode_to_bound cn  = (l2,u2)))))))
  ") prefer 2 apply(force intro: FIXME)
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
  apply(simp add: check_keys_2_def)
  apply(intro conjI)
   (* 5 subgoals *)
   (* l2 = None? *)
   apply(case_tac l2) prefer 2 apply(force)
   (* l2 = None *)
   apply(simp)
   (* if l2 is none , then cnode_to_bound cn = (None,_), so i is 0, and l is None; so xs is [] from wf_focus, and xs'  is [] from defn of split_list; *)
   apply(subgoal_tac "(i=min_child_index) & (l=None)") prefer 2
    (* mini lemma *)
    apply(simp add: cnode_to_bound_def)
    apply(drule_tac t=cn in sym, simp)
    apply(simp add: index_to_bound_def rev_apply_def mk_core_def)
    apply(simp add: with_parent_bound_def)
    apply(case_tac "i=min_child_index") apply(force)
    apply(force)
   apply(elim conjE, simp)
   apply(rule append_leaves_to_map)
    (* xs ... = {} ? *)
    apply(simp add: wellformed_fts_def wellformed_fts_focus_def wellformed_core_def rev_apply_def)
    apply(force simp add: check_keys_2_def leaves_to_map_def rev_apply_def)

    (* xs'... = {} ? *)
    apply(drule_tac t=xs' in sym)
    apply(simp)
    apply(simp add: split_list_def Let_def)
    apply(elim conjE)
    apply(drule_tac t=tsx in sym)
    apply(simp)
    apply(simp  add: min_child_index_def rev_apply_def)
    apply(force simp add: leaves_to_map_def rev_apply_def)
   
   (* same for u2 *)
   apply(force intro: FIXME)
   
   (* ck2 .. l2; xs' are less than l2; from wellformed_fts *)
   apply(force intro: FIXME)
   
   (* ck2 l2 ... u2 ; from wellformed_fts *)
   apply(force intro: FIXME)
   
   (* ck2 u2 ... ; from wellformed_fts *)
   apply(force intro: FIXME)

  
 (* wellformed_fts_1 f' *)
 apply(simp add: wellformed_fts_1_def)
 apply(drule_tac t=cn in sym)
 apply(simp)
 apply(drule_tac t=f' in sym)
 apply(simp)
 apply(simp add: split_list_def)
 apply(simp add: Let_def)
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
    (? ts2. ((cn # ts) = ts2) &
    (* new focus ----- *)
    (? tsx t2 tsy. (split_list rs i = (tsx,t2,tsy)) & 
    (? xs' zs'. (
      (tsx |> List.map tree_to_leaves |> List.concat, tsy |> List.map tree_to_leaves |> List.concat) = (xs',zs'))
    &  
    (? l2 u2. cnode_to_bound cn  = (l2,u2)))))))
  ") prefer 2 apply(force intro: FIXME)
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