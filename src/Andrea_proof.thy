theory Andrea_proof
imports Insert_tree_stack Key_lt_order Find_tree_stack  Find_proof (*FIXME uncomment when finished step_across_proof: Insert_step_up_proof *)
begin

(*FIXME begin: delete all*)
lemma forall_subtrees_Cons: "forall_subtrees P t = 
(case t of 
 Node(l,cs) => 
  (P t & 
  List.list_all (forall_subtrees P) cs)
 | Leaf l => P t)"
apply (simp add: forall_subtrees_def rev_apply_def)
apply (case_tac t)
 (*t = Node x1*)
 apply (simp,case_tac x1,simp add:rev_apply_def)
 apply (force simp add:forall_subtrees_def rev_apply_def list_all_iff)

 (*t = Leaf x2*)
 apply force
done

definition wf_size' :: "rmbs_t => Tree => bool" where
"wf_size' rmbs t0 == (
case rmbs of
Rmbs False => (
case t0 of 
Leaf(l) => (length l <= Constants.max_leaf_size +1)
| Node(l,cs) => (
1 <= length l
& List.list_all (forall_subtrees wf_size_1) cs)
)
| Rmbs True => (
case t0 of 
Leaf(l) => (length l <= Constants.max_leaf_size +1)
| Node(l,cs) => (
1 <= length l
& List.list_all (forall_subtrees wf_size_1) cs)
))"

lemma wf_size_implies_wf_size': "wf_size r t ==> wf_size' r t"
apply (simp add:wf_size'_def wf_size_def)
apply (case_tac r)
 (*r = True*)
 apply (simp,case_tac x,simp,case_tac t, simp,case_tac x1,simp)
 apply (force simp add: Let_def list_all_length)+

 (*r = False*)
 apply (simp,case_tac x,simp,case_tac t, simp,case_tac x1,simp)
 apply (force simp add: Let_def wf_size_1_def forall_subtrees_Cons list_all_length)+
done

definition wellformed_tree' :: "rmbs_t => Tree => bool" where
"wellformed_tree' rmbs t0 == (
let b1 = wf_size' rmbs t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"

lemma wf_tree_implies_wf_tree': "wellformed_tree rmbs t ==> wellformed_tree' rmbs t"
apply (simp add:wellformed_tree_def wellformed_tree'_def wf_size_implies_wf_size')
done
  
lemma wellformed_context_hereditary: "wellformed_context (x#xs) ==> wellformed_context xs"
apply (case_tac xs,auto)
done

lemma wellformed_context_1_i_less_than_length_rs:
"wellformed_context_1 (Rbms b) ((lb,((ks, rs), i),rb)) ==> i <= length ks \<and> i < length rs \<and> rs ~= []"
 apply (force simp add:Let_def wellformed_tree_def wellformed_context_1_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def subtree_indexes_def)+
done

lemma wellformed_context_i_less_than_length_rs:
"wellformed_context ((lb,((ks, rs), i),rb) # stk) ==> i <= length ks \<and> i < length rs"
apply (case_tac stk,(force simp add:wellformed_context_1_i_less_than_length_rs)+)
done

lemma wf_size_ks_not_empty: "wf_size (Rmbs (stk = [])) (Node(ks,rs)) ==> 1<=length ks"
apply (simp add:wf_size_def)
apply (case_tac "stk")
  (*stk = []*)
  apply (force simp add:Let_def)

  (*stk = a#list*)
  apply (force simp add:forall_subtrees_def rev_apply_def wf_size_1_def Let_def)
done

lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma list_all_of_list_replace_at_n:
"i < length rs ==>
 list_replace_at_n rs i [tleft, tright] |> dest_Some = rs2 ==>
 P tleft ==>
 P tright ==>
 list_all P rs ==> list_all P rs2"
apply (simp_all add:list_replace_at_n_def rev_apply_def split_at_def)
apply (drule_tac t="rs2" in sym)
 apply (case_tac "i=0")
 (*i=0*)
 apply (case_tac rs,simp+)

 (*i\<noteq>0*)
 apply (metis append_take_drop_id drop_eq_Nil list.collapse list.pred_inject(2) list_all_append not_le)
done

lemma list_all_of_list_replace_at_n_concat_map_subtrees:
"
i < length rs ==>
dest_Some (list_replace_at_n rs i [tleft, tright]) = rs2 ==>
list_all P (concat (map tree_to_subtrees rs)) ==>
list_all P (tree_to_subtrees tleft) ==>
list_all P (tree_to_subtrees tright) ==>
list_all P (concat (map tree_to_subtrees rs2))
"
apply (simp_all add:list_replace_at_n_def rev_apply_def split_at_def)
apply (drule_tac t="rs2" in sym)
apply (case_tac "i=0")
 (*i=0*)
 apply (case_tac rs,force+)

 (*i\<noteq>0*)
 apply (simp add:butlast_take)
 apply (metis append_take_drop_id concat_append drop_Suc list_all_append map_append tl_drop)
done

lemma keys_Cons: 
"keys (Node (l, cs)) = l@((List.map keys cs) |> List.concat)"
apply (simp add:keys_def rev_apply_def keys_1_def)
apply (induct cs) apply (force simp add:keys_def rev_apply_def)+
done
(*FIXME edn: delete all*)
definition wf_its_state :: "its_state => bool" where
"wf_its_state its == (
case its of
Its_down (fts,_) => wellformed_fts fts
| Its_up its => wellformed_ts its
)"

definition invariant_wf_its_state :: "bool" where
"invariant_wf_its_state == (
! its.
  wf_its_state its --> 
(
let its' = its_step_tree_stack its in
case its' of 
None => True
| Some its' => (
wf_its_state its'
)
))
"

lemma invariant_wf_its_state : "invariant_wf_its_state"
apply (subgoal_tac "total_order_key_lte") prefer 2 apply (force intro:FIXME)
(*FIXME we already proofed step up and find, we need to solve step across*)
apply (simp add:invariant_wf_its_state_def)
apply clarify
apply (case_tac "its_step_tree_stack its",force)
apply simp
apply (rename_tac its')
apply (simp add:its_step_tree_stack_def Let_def)
apply (case_tac its)
 (*its = Its_down*)
 apply (simp add:Let_def)
 apply (case_tac x1,simp)
 apply (rename_tac fts v0)
 apply (case_tac "step_fts fts")
  (*step_fts fts = None*)
  apply (simp add:dest_fts_state_def)
  apply (case_tac fts,simp)
  apply (case_tac x,simp)
  apply (rename_tac k0 node stk)
  apply (case_tac node,force)
   (*node = Leaf kvs -- this is the only interesting case*)
   apply (rename_tac kvs)
   apply (simp add:step_fts_def dest_fts_state_def)
   apply (subgoal_tac "? entry_in_kvs. (\<exists>a b. List.find (\<lambda>x. key_eq k0 (fst x)) kvs = Some (a, b)) = entry_in_kvs") prefer 2 apply force
   apply (erule exE)
   apply (subgoal_tac "? kvs2. list_ordered_insert (%x. key_lt (fst x) k0) (k0, v0) kvs entry_in_kvs = kvs2") prefer 2 apply force
   apply (erule exE)
   apply (subgoal_tac "set kvs2 \<subseteq> (insert (k0,v0) (set kvs))")
   prefer 2
    apply (subgoal_tac "kvs2 = list_ordered_insert (\<lambda>x. key_lt (fst x) k0) (k0, v0) kvs entry_in_kvs") prefer 2 apply (case_tac "entry_in_kvs \<or> length kvs < max_leaf_size",force,force)
    apply (simp add:list_ordered_insert_def)
    apply (case_tac "entry_in_kvs")
     (*entry_in_kvs*)
     apply (simp add:Let_def)
     apply (case_tac "!x : set kvs. key_lt (fst x) k0")
      (*!x : set kvs. key_lt (fst x) k0*)
      apply (meson find_Some_iff key_eq_def nth_mem)
      
      (*~ !x : set kvs. key_lt (fst x) k0*)
      apply (metis (no_types, lifting) append_Nil2 contra_subsetD list.set_sel(2) set_dropWhileD set_takeWhileD subsetI subset_insertI takeWhile_dropWhile_id)     
     (*~ entry_in_kvs*)
     apply simp
     apply (metis (no_types, lifting) contra_subsetD set_dropWhileD set_takeWhileD subsetI subset_insertI)
   apply (subgoal_tac "if entry_in_kvs then (length kvs2 = length kvs) else (length kvs2 = Suc (length kvs))")
   prefer 2
    apply (case_tac "entry_in_kvs")
     (*entry_in_kvs*)
     apply (simp add:list_ordered_insert_def Let_def)
     apply (erule exE)+
     apply (rename_tac k v)
     apply (case_tac "!x:set kvs. key_lt (fst x) k0")
     (*!x:set kvs. key_lt (fst x) k0*)
     apply simp
     apply (drule_tac t="kvs2" in sym)
     apply simp
     apply (metis (no_types, lifting) One_nat_def add_eq_if dropWhile_eq_Nil_conv find_Some_iff length_0_conv length_append length_tl less_nat_zero_code list.sel(2) takeWhile_dropWhile_id)
        
     (*~ !x:set kvs. key_lt (fst x) k0*)
     apply simp
     apply (drule_tac t="kvs2" in sym)
     apply simp
     apply (metis length_append takeWhile_dropWhile_id)
       
    (*~entry_in_kvs*)
    apply (simp add:list_ordered_insert_def Let_def)
    apply (case_tac "length kvs < max_leaf_size")
     (*length kvs < max_leaf_size*)
     apply simp
     apply (drule_tac t=kvs2 in sym)
     apply simp
     apply (metis length_append takeWhile_dropWhile_id)
     
     (*~ length kvs < max_leaf_size*)
     apply simp
     apply (drule_tac t=kvs2 in sym)
     apply simp
     apply (metis length_append takeWhile_dropWhile_id)
   apply (subgoal_tac "!i<length kvs2 - Suc 0. key_lt (fst (kvs2 ! i)) (fst (kvs2 ! Suc i))")
   prefer 2
    apply (subgoal_tac "keys_ordered_1 (Leaf kvs)") prefer 2 apply (force simp add:wf_its_state_def wellformed_fts_def dest_fts_state_def wellformed_fts_focus_def wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def)
    apply (simp add:keys_ordered_1_def rev_apply_def Let_def key_indexes_def atLeast0LessThan lessThan_def check_keys_def set_butlast_lessThan)
    apply (case_tac "entry_in_kvs")
     (*entry_in_kvs*)
     apply (simp add:list_ordered_insert_def Let_def)
     apply (erule exE)+
     apply (rename_tac k v)
     apply (case_tac "!x:set kvs. key_lt (fst x) k0")
     (*!x:set kvs. key_lt (fst x) k0*)
     apply simp
     apply (drule_tac t="kvs2" in sym)
     apply simp
     apply rule+
     apply (subgoal_tac "takeWhile (\<lambda>x. key_lt (fst x) k0) kvs = kvs") prefer 2 apply force
     apply (drule_tac t=kvs in sym)
     apply simp
     apply (smt Suc_lessI Suc_pred append_butlast_last_id diff_add_inverse2 fst_conv length_Cons length_append less_SucI list.size(3) nth_append nth_append_length nth_mem old.nat.distinct(2) zero_less_Suc)
             
     (*~ !x:set kvs. key_lt (fst x) k0*)
     apply simp
     apply (simp add:find_Some_iff)
     apply (erule conjE exE)+
     apply (rename_tac index)
     apply rule
     apply (case_tac " i < length kvs - Suc 0")prefer 2 apply force
     apply simp
     apply (subgoal_tac "? l_kvs r_kvs. ((length l_kvs) = index) & (kvs = l_kvs@(k,v)#r_kvs)")
     prefer 2 apply (metis (no_types, lifting) Cons_nth_drop_Suc add_diff_cancel_right' diff_diff_cancel id_take_nth_drop length_append length_drop less_imp_le_nat)
     apply (erule exE)+
     apply (drule_tac s="(k,v)" in sym)
     apply simp
     apply (subgoal_tac "kvs2 = l_kvs@(k0,v0)#r_kvs")
     prefer 2
       apply (simp add:nth_append)
       apply (erule conjE)+
       apply (subgoal_tac "! x : set l_kvs. key_lt (fst x) k0")
       prefer 2
        apply rule
        apply (rename_tac "kv")
        apply (subgoal_tac "keys_ordered_1 (Leaf kvs)") prefer 2 apply (force simp add:wf_its_state_def wellformed_fts_def dest_fts_state_def wellformed_fts_focus_def wellformed_tree_def keys_ordered_def forall_subtrees_def rev_apply_def)
        apply (simp add:keys_ordered_1_def Let_def rev_apply_def key_indexes_def atLeast0LessThan lessThan_def)
        apply (simp add:nth_append)
        apply (subgoal_tac "? kv_index < index. kv = l_kvs ! kv_index") prefer 2 apply (metis in_set_conv_nth)
        apply (erule exE conjE)+
        apply simp
        apply (drule_tac x="kv_index" in spec)
        apply (subgoal_tac "? key. (fst (l_kvs ! kv_index)) = key") prefer 2 apply force
        apply (erule exE)
        apply (subgoal_tac "? l_ks. map fst l_kvs = l_ks") prefer 2 apply force
        apply (erule exE)
        apply simp
        apply (subgoal_tac "key_lt key k")
        prefer 2
         (*I am readjusting stuff to reuse Key_lt_order lemma*)
         apply (subgoal_tac "l_ks ~= []") prefer 2 apply force
         apply (subgoal_tac "key_lt ((last l_ks)) k")
         prefer 2
          apply (simp add:last_conv_nth)
          apply (drule_tac x="(length l_ks - Suc 0)" in spec) back
          apply simp
          apply (subgoal_tac "length l_ks - Suc 0 < index + length r_kvs") prefer 2 apply force
          apply (subgoal_tac "(~ (length l_ks < index)) & length l_ks - Suc 0 < index") prefer 2 apply force
          apply force
         apply (subgoal_tac "\<forall>i\<in>{0..<length l_ks - Suc 0}. key_lt (((l_ks) ! i)) k")
         prefer 2
          apply (subgoal_tac "\<forall>i\<in>{0..<length l_ks - Suc 0}. key_lt (((l_ks ! i))) ((l_ks ! Suc i))")
          prefer 2
           apply (simp add: atLeast0LessThan lessThan_def)
           apply rule
           apply (case_tac "ia < index - Suc 0") prefer 2 apply force
           apply (drule_tac x=ia in spec) back
           apply (subgoal_tac "Suc ia < index") prefer 2 apply force
           apply force
          using bigger_than_last_in_list_sorted_by_key_lt apply blast
         apply (simp add:keys_ordered_1_def Let_def rev_apply_def key_indexes_def atLeast0LessThan lessThan_def)
         apply (drule_tac x="kv_index" in spec) back back
         apply (case_tac "kv_index < index - Suc 0")
          apply force
          
          apply (subgoal_tac "kv_index = index -1") prefer 2 apply force
          apply (case_tac "index = 0",force)
          apply (subgoal_tac "key = fst(last l_kvs)")
          prefer 2
           apply (force simp add:last_conv_nth)
          apply (simp)
        using key_lt_eq apply blast
       apply (force simp add:key_eq_def)
     apply (simp add:nth_append)
     apply (drule_tac x="i" in spec)
     apply (case_tac "Suc i < length l_kvs")
      (*Suc i < length l_kvs*)
      apply force

      (*~ Suc i < length l_kvs*)
      apply simp
      apply (case_tac "Suc i = length l_kvs")
       apply simp
       apply (meson key_eq_def neg_key_lt order_key_le_lt) 
       
       (*Suc i ~= length l_kvs*)
       apply (case_tac "i = length l_kvs")
        (*i = length l_kvs*)
        apply simp
        apply (meson key_eq_def neg_key_lt order_key_le_lt)

        (*i ~= length l_kvs*)
        apply force

    (*~entry_in_kvs*)
    apply (simp add:list_ordered_insert_def Let_def)
    apply (drule_tac t=kvs2 in sym)
    apply simp
    apply rule
    apply (subgoal_tac "? index. length (takeWhile (\<lambda>x. key_lt (fst x) k0) kvs) = index") prefer 2 apply force
    apply (erule conjE exE)+
    apply rule
    apply (subgoal_tac "1 < length kvs") prefer 2 apply (fast intro:FIXME) (*wf_size*)
    apply (subgoal_tac "? l_kvs r_kvs. ((length l_kvs) = index) & (kvs = l_kvs@r_kvs)") prefer 2 apply (metis takeWhile_dropWhile_id) 
    apply (erule exE)+
    apply simp
    apply (subgoal_tac "kvs2 = l_kvs@(k0,v0)#r_kvs") prefer 2 apply (metis append_eq_append_conv takeWhile_dropWhile_id) 
    apply (simp add:nth_append)
    apply (subgoal_tac "l_kvs ~= [] --> key_lt (fst(last l_kvs)) k0")
    prefer 2
     apply (simp add:last_conv_nth)
     apply (metis diff_Suc_less length_greater_0_conv nth_mem set_takeWhileD)
    apply (subgoal_tac "r_kvs ~= [] --> key_lt  k0 (fst(hd r_kvs))")
    prefer 2 
     apply rule+
     apply (simp add:hd_def,case_tac r_kvs,force,clarsimp)
     apply (case_tac "List.find (\<lambda>x. key_eq k0 (fst x)) (l_kvs @ (ac, bb) # list)") prefer 2 apply force
     apply (simp add:find_None_iff)
     apply (metis dropWhile_eq_Cons_conv fst_conv key_lt_rev)
    apply (subgoal_tac "r_kvs ~= [] --> key_lt (fst (((k0, v0) # r_kvs) ! (i - index))) (fst (r_kvs ! (i-index)))")
    prefer 2
     apply (rule)+
     apply (subgoal_tac "? i' . (i - index) = i'") prefer 2 apply force
     apply (erule exE conjE)+
     apply simp
     apply (subgoal_tac "i' < (length r_kvs)") prefer 2 apply clarsimp apply (metis add.commute length_greater_0_conv less_diff_conv2 less_imp_le_nat neq0_conv zero_less_diff)
     apply (case_tac "i' = 0")
      (*i' = 0*)
      apply (simp add:hd_def,case_tac "r_kvs",force,force)
      
      (*i' ~= 0 *)
      apply simp
      apply (drule_tac x="i'+index-1" in spec)
      apply simp
      apply (subgoal_tac "i' + index - Suc 0 < index + length r_kvs - Suc 0") prefer 2 apply force
      apply (subgoal_tac "~ (i' + index - Suc 0 < index) ") prefer 2 apply force
      apply force
    apply (subgoal_tac "l_kvs ~= [] --> (Suc i < index --> key_lt (fst (l_kvs ! i)) (fst (l_kvs ! Suc i))) & (Suc i = index --> key_lt (fst (l_kvs ! i)) k0)")
    prefer 2
     apply (case_tac "Suc i < index")
      (*Suc i < index*)
      apply simp
      apply rule+
      apply (drule_tac x="i" in spec)
      apply force

      (*~ Suc i < index*)
      apply simp
      apply (case_tac "Suc i ~= index",force)
      apply (case_tac "l_kvs = []",force)
      apply (simp add:last_conv_nth)
      apply force
    apply (case_tac "l_kvs = []")
     (*l_kvs = []*)
     apply (case_tac "r_kvs = []",force,force)

     (*l_kvs ~= []*)
     apply (case_tac "r_kvs = []",force,force)
   (*we show that the fat leaf is partially wellformed*)
   apply (subgoal_tac "wellformed_tree' (Rmbs (stk=[])) (Leaf kvs2)")
   prefer 2
    apply (simp add:wellformed_tree'_def)
    apply rule
     (*wf_size'*)
     apply (simp add:wf_size'_def)
     apply (subgoal_tac "wf_size (Rmbs (stk=[])) (Leaf kvs)") prefer 2 apply (fast intro:FIXME)
     apply (case_tac "stk=[]")
      (*stk=[]*)
      apply (simp add:wf_size_def forall_subtrees_def wf_size_1_def)
      apply (simp add:list_ordered_insert_def Let_def)
      apply (case_tac "entry_in_kvs")
       apply force+
             
      (*stk~=[]*)
      apply (simp add:wf_size_def forall_subtrees_def wf_size_1_def)
      apply (simp add:list_ordered_insert_def Let_def)
      apply (case_tac "entry_in_kvs")
       apply (simp add:forall_subtrees_def rev_apply_def wf_size_1_def Let_def)+
    apply rule
     (*wf_ks_rs*)
     apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
    apply rule
     (*balanced*)
     apply (force simp add:balanced_def forall_subtrees_def rev_apply_def balanced_1_def)
    apply rule
     (* keys_consistent *)
     apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def) 
    (* keys_ordered *)
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def)
    apply (force simp add:Let_def key_indexes_def atLeast0LessThan lessThan_def check_keys_def set_butlast_lessThan)
   apply (subgoal_tac "wellformed_context stk") prefer 2 apply (force simp add:wf_its_state_def wellformed_fts_def dest_fts_state_def)
   apply (case_tac "(? a b. List.find (% x. key_eq k0 (fst x)) kvs = Some (a, b)) | length kvs < max_leaf_size")
    (*cond = true*)
    apply (drule_tac t="Some its'" in sym)
    apply (simp add:wf_its_state_def wellformed_ts_def dest_ts_def)
    apply (subgoal_tac "wellformed_focus (Inserting_one (Leaf kvs2)) (stk = [])")
    prefer 2
     apply (simp add:wellformed_focus_def wellformed_tree_def wellformed_tree'_def wf_size_def wellformed_fts_def dest_fts_state_def wellformed_fts_focus_def)
     apply (case_tac "length kvs2 <= max_leaf_size & min_leaf_size < length kvs2")
     prefer 2
      apply (erule conjE)+
      apply (erule disjE)
       (*entry_in_kvs*)       
       apply (case_tac "stk=[]",force,force simp add:forall_subtrees_def rev_apply_def wf_size_1_def)

       (*length kvs < max_leaf_size*)
       apply (case_tac "entry_in_kvs")
        apply (case_tac "stk = []",force,force simp add:forall_subtrees_def rev_apply_def wf_size_1_def)
        apply (case_tac "stk = []",force,force simp add:forall_subtrees_def rev_apply_def wf_size_1_def)
      apply (case_tac "stk = []",force,force simp add:forall_subtrees_def rev_apply_def wf_size_1_def)
    apply (subgoal_tac "wellformed_ts_1 (Tree_stack (Focus (Inserting_one (Leaf kvs2)), stk))")
    prefer 2
     apply (simp add:wellformed_ts_1_def dest_ts_def)
     apply (case_tac stk,force)
     apply (rename_tac hd_stk stk')
     apply (case_tac hd_stk,simp)
     apply (rename_tac lb ni rb)
     apply (case_tac ni)
     apply (rename_tac n i)
     apply (case_tac n)
     apply (rename_tac ks rs)
     apply simp
     apply (subgoal_tac "wellformed_context_1 (Rmbs (stk' = [])) ((lb, ((ks, rs), i), rb))") prefer 2 apply (case_tac stk',force,force)
     apply (simp add:wellformed_context_1_def)
     apply (simp add:wellformed_fts_def dest_fts_state_def wellformed_fts_1_def)
     apply (erule conjE)+
     apply (thin_tac "node=_")
     apply (drule_tac t="rs!i" in sym)
     apply simp
     apply (simp add:get_lower_upper_keys_for_node_t_def)
     apply (subgoal_tac "ks ~= []") prefer 2 apply (simp add:wellformed_focus_def wellformed_tree_def wf_size_def,case_tac stk',force simp add: Let_def wf_size_1_def,force simp add:Let_def forall_subtrees_def rev_apply_def wf_size_1_def)
     apply simp
     apply (case_tac "i=0")
      (*i=0*)
      apply (simp add:check_keys_def)
      apply (subgoal_tac "keys_consistent (Node(ks,rs))") prefer 2 apply (force simp add:wellformed_focus_def wellformed_tree_def)
      apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def key_indexes_def atLeast0LessThan lessThan_def check_keys_def)
      apply (erule conjE)+
      apply (drule_tac x=0 in spec)
      apply (simp add:keys_def rev_apply_def keys_1_def)
      apply rule
       apply (case_tac lb,force)
       apply (simp add:keys_def rev_apply_def keys_1_def)
       apply fastforce+
                          
      (*i~=0*)
      apply (case_tac "i = length ks")
       (*i = length ks*)
       apply simp
       apply (simp add:check_keys_def)
       apply rule
        (*\<forall>x\<in>set (keys (Leaf kvs2)). key_le (ks ! (length ks - Suc 0)) x*)
        apply rule
        apply (simp add:keys_def rev_apply_def keys_1_def)
        (*FIXME this is true for key_consistent, also I need a subgoal about the find: ks!i \<le> k0 < ks!i+1*)
        apply (force intro:FIXME)
       apply (force intro:FIXME)

       (*i ~= length ks*)
       apply (force intro:FIXME)
    apply force
    
    (*cond = false*)
    apply (simp add:split_leaf_kvs_def Let_def)
    apply (subgoal_tac "? left_kvs2 . take min_leaf_size kvs2 = left_kvs2") prefer 2 apply force
    apply (subgoal_tac "? median_k. fst (hd (drop min_leaf_size kvs2)) = median_k") prefer 2 apply force
    apply (subgoal_tac "? right_kvs2. drop min_leaf_size kvs2 = right_kvs2") prefer 2 apply force
    apply (erule exE)+
    apply (drule_tac t="its'" in sym)
    apply (simp add:wf_its_state_def wellformed_ts_def dest_ts_def)
    apply (subgoal_tac "wellformed_focus(Inserting_two(Leaf (left_kvs2), median_k, Leaf (right_kvs2)))(stk = []) ")
    prefer 2 apply (force intro:FIXME)
    apply (subgoal_tac "wellformed_ts_1 (Tree_stack(Focus (Inserting_two(Leaf (left_kvs2), median_k, Leaf (right_kvs2))),stk))")
    prefer 2 apply (force intro:FIXME)
    apply (force)
 
  (* step_fts fts = Some fts'*)
  apply (rename_tac fts')
  apply (insert invariant_wf_fts)
  apply (force simp add:wf_its_state_def invariant_wf_fts_def)
  
 (*its = Its_up*)
 apply (thin_tac "invariant_wf_fts")
 apply (simp add:wf_its_state_def)
 apply (case_tac "step_up x2",force)
 apply (drule_tac t="Some its'" in sym)
 apply simp
(* FIXME uncomment when finished step across proof
 apply (insert invariant_wf_ts)
 apply (simp add:invariant_wf_ts_def)
 apply force
*)
 apply (fast intro:FIXME)
done

end