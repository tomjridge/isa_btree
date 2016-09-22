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

lemma check_keys_eq_ck_ck: "
check_keys l ks u = (check_keys l ks None & check_keys None ks u)
"
apply(simp add: check_keys_def)
done


declare  wellformed_context.simps[simp del]

declare wellformed_context_def_2[simp del] (* not a simp? - may expand too far? or use anyway? *)

declare ts_to_ms_def_2[simp] (* likely a simp *)
declare dest_fts_state_t_def_2[simp] (* surely a simp *)

lemma search_key_to_index: "
(search_key_to_index ks k = i) \<longrightarrow> i : set(subtree_indexes (ks,rs))
"
apply(force intro:FIXME)
done

lemma subtree_indexes_trichotomy: " 
i : set(subtree_indexes (ks,rs)) \<longrightarrow> 
(min_child_index < i & i < max_child_index(ks,rs)) | 
(i = min_child_index) | (i = max_child_index(ks,rs))"
apply(force intro:FIXME)
done

(* the easy case *)
lemma search_key_to_index_bound: "
(search_key_to_index ks k = i) & 
min_child_index < i &
i < max_child_index(ks,rs) \<longrightarrow> (
let (l,u) = get_lu_for_child ((ks,rs),i) in
check_keys l [k] u)"
apply(force intro: FIXME)
done

lemma lu_with_default_eq_lu: "
min_child_index < i &
i < max_child_index(ks,rs) \<longrightarrow>
get_lu_for_child_with_parent_default x2 ((ks,rs),i) = get_lu_for_child ((ks,rs),i)"
apply(force intro:FIXME)
done

(*
wellformed_fts_focus (ts_to_ms ts) (Node (ks, rs)) \<Longrightarrow>
       wellformed_context ts \<Longrightarrow>
*)

lemma get_parent_bounds_check_keys: "
wellformed_fts_1 (Fts_state (k, Node (ks, rs), ts)) \<Longrightarrow>
get_parent_bounds ts = (l1, u1) \<Longrightarrow>
check_keys l1 [k] u1
"
apply(simp add: get_parent_bounds_def)
apply(case_tac ts) apply(simp add: get_parent_bounds_def check_keys_def)
apply(simp)
apply(subgoal_tac "? n i x. a = Cnode(n,i,x)") prefer 2 apply(force intro:FIXME)
apply(elim exE, simp)
apply(simp add: wellformed_fts_1_def dest_cnode_t_def)
apply(force simp add: check_keys_def)
done

definition main_property :: "fts_state_t \<Rightarrow> bool" where
"main_property fts' = (
  let (k,t,ts) = dest_fts_state_t fts' in
  case ts of 
  Nil \<Rightarrow> True
  | cn#cns \<Rightarrow> (
    let (n,i,x) = dest_cnode_t cn in
    let (l,u) = x in
    check_keys l [k] u
  ))"

lemma main_lemma: "(
(* want to check_keys l [k] u *)
total_order_key_lte --> (
  wellformed_fts fts & (step_fts fts = Some fts') --> main_property fts'))
"
apply(simp add: main_property_def)
apply(simp, intro allI impI, elim conjE)
apply(subgoal_tac "? k t ts. fts = Fts_state(k,t,ts)") prefer 2 apply(force intro:FIXME)
apply(elim exE, simp)
apply(simp add: step_fts_def)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. t = Node(ks,rs))") prefer 2 apply(force intro: FIXME)
apply(erule disjE) apply(force)
apply(elim exE, simp)
apply(subgoal_tac "? i. search_key_to_index ks k = i") prefer 2 apply(force)
apply(elim exE, simp)
apply(drule_tac t=fts' in sym) apply(simp)
apply(thin_tac "fts'=_")
apply(simp add: dest_cnode_t_def)
apply(subgoal_tac "
   ? l0 u0. get_lu_for_child_with_parent_default (get_parent_bounds ts) ((ks, rs), i) = (l0,u0)") prefer 2 apply(force)
apply(elim exE, simp)
(* this is the goal we want *)
apply(subgoal_tac "check_keys l0 [k] None & check_keys None [k] u0") apply(force intro:FIXME)
apply(rule conjI)
 (* want check_keys l0 [k] None; distinguish i=min_child from other case *)
 apply(subgoal_tac "(i = min_child_index) | (min_child_index < i & i \<le> max_child_index(ks,rs))") prefer 2 apply(force intro:FIXME)
 apply(elim disjE)
  (* i = min_child_index; so l0 is the lower bound of the parent *)
  apply(subgoal_tac "? l1 u1. get_parent_bounds ts = (l1,u1)") prefer 2 apply(force intro:FIXME)
  apply(elim exE,simp)
  apply(subgoal_tac "l0 = l1") prefer 2 apply(force intro:FIXME)
  apply(simp)
  apply(simp add: wellformed_fts_def ) apply(elim conjE)
  using check_keys_eq_ck_ck get_parent_bounds_check_keys apply blast
    
  (* min_child_index < i *)
  apply(force intro:FIXME)

 (* want check_keys None [k] u0 *)
  apply(subgoal_tac "? l1 u1. get_parent_bounds ts = (l1,u1)") prefer 2 apply(force intro:FIXME)
  apply(elim exE,simp)
  apply(subgoal_tac "u0 = u1") prefer 2 apply(force intro:FIXME)
  apply(simp)
  apply(simp add: wellformed_fts_def ) apply(elim conjE)
  using check_keys_eq_ck_ck get_parent_bounds_check_keys apply blast
done 


(* intuitively, we examine all the possible cases... *)
lemma invariant_wf_fts: "invariant_wf_fts"
apply (simp add:invariant_wf_fts_def)
apply(intro impI allI)
apply(subgoal_tac "(step_fts fts = None) | (? fts'. step_fts fts = Some(Fts_state(fts')))")
  prefer 2 apply(force intro:FIXME)
apply(erule disjE) apply(force)
apply(elim exE)
apply(simp)
apply(subgoal_tac "main_property (Fts_state(fts'))")
 prefer 2 apply (simp add: main_lemma option.case_eq_if)
apply(simp add: step_fts_def)
apply(subgoal_tac "? k t ts. fts = Fts_state(k,t,ts)") prefer 2 apply(force intro: FIXME)
apply(elim exE, simp)
apply(subgoal_tac "(? kvs. t = Leaf kvs) | (? ks rs. t = Node(ks,rs))") prefer 2 apply(force intro:FIXME)
apply(erule disjE)
 (* Leaf *)
 apply(force)

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
 apply(drule_tac t=fts' in sym) apply(simp) apply(thin_tac "fts'=_")
 apply(elim conjE)
 apply(intro conjI)
  (* wellformed_fts_focus rs!x since wf_fts_1 Node(_,rs) *)
  apply(simp add: wellformed_fts_focus_def)
  (* since Node(ks,rs) is wellformed, so too is rs!i *)
  apply(subgoal_tac "? ms. wellformed_tree ms (Node(ks,rs))") prefer 2 apply(force)
  apply(elim exE)
  using wellformed_tree_children apply( blast)

  (* want wellformed_cnode Cnode(ks,rs,i,l0,u0) *)
  apply(simp add: wellformed_context_def_2)
  apply(simp add: wellformed_cnode_def dest_cnode_t_def)
  apply(rule conjI)
   (* want wellformed_tree *)
   apply(force simp add: wellformed_fts_focus_def)

   (* check_keys l0 (keys r) u0 ; suppose pb is a bound for rs, then lget_lu_with_def is a bound for rs!i *)
   apply(force intro: FIXME)

  (* want wellformed_fts_1 k,r,cn1#ts *)
  apply(simp (no_asm) add: wellformed_fts_1_def dest_fts_state_t_def dest_cnode_t_def)
  apply(simp)
  (* want check_keys l0 [k] u0 this comes from the fact that k is the search key, and this is bounded *)
  (* FIXME need lemma about get_lu_for_child *)
  apply(force simp add: main_property_def dest_cnode_t_def)

done

end
