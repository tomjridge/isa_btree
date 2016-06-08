theory Find_proof
imports Key_lt_order Find_tree_stack
begin

definition invariant_wf_fts :: "bool" where
"invariant_wf_fts == (
! fts.
 wellformed_fts fts -->
(
let fts' = step_fts fts in
case fts' of None => True
| Some fts' => wellformed_fts fts'
))"

lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma keys_Cons: 
"keys (Node (l, cs)) = l@((List.map keys cs) |> List.concat)"
apply (simp add:keys_def rev_apply_def keys_1_def)
apply (induct cs) apply (force simp add:keys_def rev_apply_def)+
done

lemma invariant_wf_fts: "invariant_wf_fts"
apply (simp add:invariant_wf_fts_def)
apply clarify
apply (case_tac "step_fts fts",force)
(*step_fts = Some fts'*)
apply simp
apply (rename_tac fts')
apply (simp add:step_fts_def dest_fts_state_def)
apply (case_tac fts,simp)
apply (case_tac x,simp)
apply (rename_tac k node_or_leaf ctx)
apply (thin_tac "x=_")
apply simp
apply (case_tac "case ctx of [] \<Rightarrow> (None, None) | (lb, xb, xc) # xa \<Rightarrow> (lb, xc)")
apply simp
apply (rename_tac lb rb)
apply (case_tac node_or_leaf)
prefer 2
 (*node_or_leaf = Leaf _*)
 apply force

 (*node_or_leaf = Node (ks,rs)*)
 apply (case_tac x1,simp)
 apply (thin_tac "x1=_")
 apply (rename_tac ks rs)
 apply (simp add:Let_def)
 apply (subgoal_tac "? index. search_key_to_index ks k = index") prefer 2 apply (force simp add:search_key_to_index_def Let_def)
 apply (erule exE)
 apply simp
 apply (case_tac "get_lower_upper_keys_for_node_t ks lb index rb")
 apply simp
 apply (rename_tac l u)
 apply (simp add:wellformed_fts_def dest_fts_state_def)
 apply (drule_tac t="fts'" in sym,simp)
 apply (subgoal_tac "length rs = length ks + 1") prefer 2 apply (force simp add:wellformed_fts_focus_def wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
 apply (subgoal_tac "index < length rs")
 prefer 2
  apply (simp add:search_key_to_index_def Let_def, case_tac " List.find (\<lambda>x. key_lt k (ks ! x)) [0..<length ks]",force,simp)
  apply (smt diff_zero find_Some_iff length_upt less_Suc_eq less_diff_conv nth_upt zero_less_diff)
 apply (subgoal_tac "? child. rs ! index =  child") prefer 2 apply force
 apply (erule exE)
 apply simp
 apply (subgoal_tac "child : set rs") prefer 2 apply force 
 apply (subgoal_tac "wellformed_fts_focus (Rmbs False) (rs ! index) ")
 prefer 2
  apply (simp add:wellformed_fts_focus_def wellformed_tree_def)
  apply (subgoal_tac "wf_size (Rmbs False) child") prefer 2 apply (case_tac "ctx = []",(force simp add:Let_def wf_size_def forall_subtrees_def rev_apply_def list_all_iff)+)
  apply (subgoal_tac "wf_ks_rs child") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "balanced child") prefer 2 apply (force simp add:balanced_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "keys_consistent child") prefer 2 apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def list_all_iff)
  apply (subgoal_tac "keys_ordered child") prefer 2 apply (force simp add:keys_ordered_def forall_subtrees_def rev_apply_def list_all_iff)
  apply force
 apply simp
 apply (subgoal_tac "ks ~= []") prefer 2 apply (simp add:wellformed_fts_focus_def wellformed_tree_def wf_size_def,case_tac ctx,force,force simp add:forall_subtrees_def rev_apply_def wf_size_1_def Let_def)
 apply (subgoal_tac "wellformed_fts_1 (Fts_state (k, child, (l, ((ks, rs), index), u) # ctx))")
 prefer 2
  apply (simp add:dest_fts_state_def wellformed_fts_1_def)
  apply (simp add:get_lower_upper_keys_for_node_t_def check_keys_def)
  apply (subgoal_tac "index < length ks --> key_lt k (ks ! index)")
  prefer 2
   apply rule
   apply (simp add:search_key_to_index_def Let_def)
   apply (case_tac "List.find (\<lambda>x. key_lt k (ks ! x)) [0..<length ks]",force)
   apply (simp add:find_Some_iff)
   apply (erule exE)+
   apply force
  apply (subgoal_tac "0 < index --> key_le (ks ! (index - Suc 0)) k")
  prefer 2
   apply rule
   apply (simp add:search_key_to_index_def Let_def)
   apply (subgoal_tac "total_order_key_lte") prefer 2 apply (force intro:FIXME) (*move in assumptions*)
   apply (case_tac "List.find (\<lambda>x. key_lt k (ks ! x)) [0..<length ks]")
    (*None*)
    apply (simp add:find_None_iff)
    apply (drule_tac x="index-1" in spec)
    apply (force simp add:neg_key_lt)
    
    (*Some*)
    apply (simp add:find_Some_iff)
    apply (erule exE)+
    apply (erule conjE)+
    apply (drule_tac x="index-1" in spec)
    apply (force simp add:neg_key_lt)
    
  apply (case_tac "index = 0")
   apply (case_tac ctx,force,simp)
   apply (case_tac list)
    apply clarsimp
    apply (case_tac x,simp add:get_lower_upper_keys_for_node_t_def Let_def,case_tac ba,force,force)
    apply (simp add:get_lower_upper_keys_for_node_t_def Let_def check_keys_def)
    apply (simp add:wellformed_context_1_def check_keys_def )
    apply clarsimp
    apply (case_tac l,force)
    apply (case_tac "ba = 0",force,force)
   
    (*list ~= []*)
    apply clarsimp
    apply (case_tac l,force)
    apply (rename_tac kl)
    apply (simp add:get_lower_upper_keys_for_node_t_def Let_def check_keys_def)
    apply (case_tac ba,force)
    apply force
   (*index = length ks*)
   apply simp
   apply (case_tac u,force)
   apply (rename_tac kr)
   apply (case_tac ctx,force,simp)
   apply (case_tac list)
    apply clarsimp
    apply (simp add:get_lower_upper_keys_for_node_t_def Let_def check_keys_def)
    apply (simp add:wellformed_context_1_def check_keys_def )
    apply clarsimp
    apply (case_tac "ba = length aa",force,force)
   
    (*list ~= []*)
    apply clarsimp
    apply (rename_tac kl)
    apply (simp add:get_lower_upper_keys_for_node_t_def Let_def check_keys_def)
    apply (case_tac "ba=length aa",force)
    apply force
 apply (case_tac ctx)
 (*ctx = [] *)
 apply simp
 apply (simp add:wellformed_context_1_def Let_def wellformed_fts_focus_def subtree_indexes_def check_keys_def get_lower_upper_keys_for_node_t_def)
 apply rule
  apply (case_tac l) apply force
  apply (rename_tac im1ks)
  apply simp
  apply (subgoal_tac "im1ks = (ks ! (index - 1))") prefer 2 apply (metis option.distinct(1) option.inject)
  apply simp
  apply (simp add:wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def check_keys_def)
  apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def check_keys_def key_indexes_def atLeast0LessThan lessThan_def)
  apply (erule conjE)+
  apply (drule_tac x="index - Suc 0" in spec) back
  apply force

  apply (case_tac u) apply (force)
  apply (rename_tac iks)
  apply simp
  apply (subgoal_tac "iks = ks ! index") prefer 2 apply (case_tac "index = length ks",force,force)
  apply simp
  apply (simp add:wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def check_keys_def)
  apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def check_keys_def key_indexes_def atLeast0LessThan lessThan_def)
  apply (erule conjE)+
  apply (drule_tac x="index" in spec)
  apply force

  (*ctx = a#list*)
  apply simp
  apply rule
   (*wellformed_context_1*)
   apply (simp add:wellformed_context_1_def wellformed_fts_focus_def)
   apply (simp add:subtree_indexes_def)
   apply (simp add:check_keys_def)
   apply (simp add:get_lower_upper_keys_for_node_t_def)
   apply (case_tac a,simp)
   apply (erule conjE)+
   apply (subgoal_tac "wellformed_context_1 (Rmbs (list = [])) (lb, b, rb)") prefer 2 apply (case_tac list, force,force) 
   apply (rule)
    (*case l of None \<Rightarrow> True | Some kl \<Rightarrow> Ball (set (keys child)) (key_le kl)*)
    apply (case_tac l,force)
    apply (rename_tac kl)
    apply (simp add:wellformed_context_1_def,case_tac b,case_tac ab,simp)
    apply (case_tac "index = 0")
     apply (simp add:check_keys_def wellformed_fts_1_def dest_fts_state_def)
     apply (erule conjE)+
     apply (drule_tac t="bb!ba" in sym) back
     apply (simp add:keys_def rev_apply_def keys_1_def)
     apply blast

     (*index ~= 0*)
     apply simp
     apply (drule_tac t="kl" in sym)
     apply simp
     apply (simp add:wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def check_keys_def)
     apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def check_keys_def key_indexes_def atLeast0LessThan lessThan_def)
    
    (*case u of None \<Rightarrow> True | Some kr \<Rightarrow> \<forall>k\<in>set (keys child). key_lt k kr*)
    apply (case_tac u,force)
    
    (*u = Some kr*)
    apply (rename_tac kr)
    apply (simp add:wellformed_context_1_def,case_tac b,case_tac ab,simp)
    apply (case_tac "index = length ks")
     (*index = length ks*)
     apply (simp add:check_keys_def wellformed_fts_1_def dest_fts_state_def)
     apply (erule conjE)+
     apply (drule_tac t="bb!ba" in sym) back
     apply (simp add:keys_def rev_apply_def keys_1_def)
     apply blast

     (*index ~= length ks*)
     apply simp
     apply (drule_tac t="kr" in sym)
     apply simp
     apply (simp add:wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def check_keys_def)
     apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def check_keys_def key_indexes_def atLeast0LessThan lessThan_def)    
  
  apply (subgoal_tac "ks ~= []") prefer 2 apply (force simp add:wellformed_fts_focus_def wellformed_tree_def wf_size_def forall_subtrees_def rev_apply_def wf_size_1_def)
  apply (case_tac a,simp)
  apply (subgoal_tac "is_subnode ((ks, rs), index) b \<and> linked_context (lb, b, rb) list")
  prefer 2
  apply (case_tac "list")
   (*list = []*)
   apply (simp add:is_subnode_def,case_tac b,case_tac ab,force simp add:wellformed_context_1_def wellformed_fts_1_def dest_fts_state_def)
  
   (*list ~= []*)
   apply simp
   apply (case_tac b,case_tac ac,case_tac ab,simp)
   apply (simp add:is_subnode_def,case_tac b,case_tac ab,force simp add:wellformed_context_1_def wellformed_fts_1_def dest_fts_state_def)  
  apply (case_tac "index = 0")
   (*index = 0*)
   apply (force simp add:get_lower_upper_keys_for_node_t_def)
   
   (*index ~= 0*)
   apply (case_tac "index = length ks")
   apply (erule conjE)+
   apply (force simp add:get_lower_upper_keys_for_node_t_def)

   (*0 < index*)
   apply (force simp add:get_lower_upper_keys_for_node_t_def)
done
end
