theory Find_proof imports Key_value_proof Find_tree_stack begin

(*begin find invariant*)
definition invariant_wf_fts :: "bool" where
"invariant_wf_fts = (! fts fts'.
  total_order_key_lte &
  (step_fts fts = Some (fts')) &
  wellformed_fts fts \<longrightarrow> wellformed_fts fts')
"
(*end find invariant*)

(* FIXME andrea: this is a very important lemma ! ! ! *)
lemma wellformed_tree_children: "wellformed_tree x (Node(ks,rs)) \<longrightarrow> (! r : set(rs). wellformed_tree None r)"
  apply(force intro: FIXME)
  done

lemma check_keys_eq_ck_ck: "
check_keys l ks u = (check_keys l ks None & check_keys None ks u)
"
apply(simp add: check_keys_def)
done


declare  wellformed_context.simps[simp del]

(*
declare wellformed_context_def_2[simp del] (* not a simp? - may expand too far? or use anyway? *)
*)

declare ts_to_ms_def_2[simp] (* likely a simp *)
declare dest_fts_focus_def_2[simp] (* surely a simp *)
declare dest_cnode_t_def_2[simp]



lemma check_keys_subseteq: "check_keys l ks u & set(ks') \<le> set(ks) \<longrightarrow> check_keys l ks' u"
by (smt check_keys_def option.case_eq_if subsetD)


(* this lemma details what happens to check_keys when we make a step: 
providing l,u was already a bound, l0,u0 is now a new bound *)
lemma check_keys_narrow: "
(check_keys l (k#(keys (Node(ks,rs)))) u) &
(search_key_to_index ks k = i) &
(rs!i=r) &
(Cnode ((ks, rs), i, l, u) = cn)  &
(cnode_to_bound cn=(l0,u0)) \<longrightarrow> 
(check_keys l0 (k#(keys r)) u0)"
  apply(force intro: FIXME)
  done




(* intuitively, we examine all the possible cases... *)
lemma invariant_wf_fts: "
  invariant_wf_fts
"
apply (unfold invariant_wf_fts_def)
apply(intro impI allI)
apply(elim exE conjE)
(* apply(subgoal_tac "main_property fts'")
 prefer 2 apply (simp add: main_lemma option.case_eq_if) *)
apply(simp add: step_fts_def)
apply(subgoal_tac "? f ts. fts = (f,ts)") prefer 2 apply(force intro: FIXME)
apply(elim exE, simp)
apply(subgoal_tac "? k l t u. f = \<lparr> fts_key=k,fts_l=l,fts_t=t,fts_u=u \<rparr>") prefer 2 apply(force intro: FIXME)
apply(elim exE, simp)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. t = Node(ks,rs))") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* Leaf *)
 apply(force)

 (* t = Node(ks,rs) *)
 apply(elim exE, simp)
 apply(thin_tac "fts=_")
 apply(thin_tac "f=_")
 apply(subgoal_tac "? i. search_key_to_index ks k = i") prefer 2 apply(force)
 apply(elim exE, simp)
 apply(subgoal_tac "? cn. Cnode((ks,rs),i,l,u) = cn") prefer 2 apply(force)
 apply(elim exE, simp)
 apply(subgoal_tac "? l0 u0. cnode_to_bound cn = (l0,u0)") prefer 2 apply(force)
 apply(elim exE, simp)
 apply(subgoal_tac "i : set(subtree_indexes (ks,rs))") prefer 2 apply(force intro:FIXME)
 apply(subgoal_tac "? r. r : set(rs) &  (rs ! i) = r") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE, simp)
 apply(simp add: wellformed_fts_def)
 apply(subgoal_tac "? f' ts'. fts'=(f',ts')") prefer 2 apply(force intro:FIXME)
 apply(elim exE conjE, simp)
 apply(elim conjE)
 apply(intro conjI)
  (* want wellformed_context ts' *)
  apply(drule_tac t="ts'" in sym)
  apply(simp add: wellformed_context_def_2)
  apply(simp add: wellformed_cnode_def)
  apply(drule_tac t="cn" in sym)
  apply(simp)
  apply(rule conjI)
   (* want wellformed_tree ; from wf_focus *)
   apply(force simp add: wellformed_fts_focus_def)

   (* check_keys l (keys (Node (ks, rs))) u, from fts_focus *) 
   apply(simp add: wellformed_fts_focus_def)
   apply(elim conjE)
   (* check_keys A; B\<le>A \<longrightarrow> check_keys B *)
   using check_keys_subseteq apply (metis set_subset_Cons)


  (* wellformed_fts_focus f' since wf_fts_1 Node(_,rs) *)
  apply(simp add: wellformed_fts_focus_def)
  apply(drule_tac t=f' in sym) apply(simp)
  apply(rule conjI)
   (* want  wellformed_tree (ts_to_ms ts') r; but r is a child *)
   apply(elim conjE)
   using wellformed_tree_children apply(force)

   (* want  check_keys l0 (k # keys r) u0 *)
   apply(elim conjE)
   using check_keys_narrow apply(force)

  (* want wellformed_fts_1 (f',ts') *)
  apply(simp (no_asm) add: wellformed_fts_1_def)
  apply(drule_tac t=ts' in sym) apply(simp)
  apply(drule_tac t=f' in sym) apply(simp)
  apply(drule_tac t=cn in sym) apply(simp)

done

end
