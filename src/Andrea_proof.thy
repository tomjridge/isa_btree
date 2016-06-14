theory Andrea_proof
imports Insert_tree_stack Key_lt_order Find_tree_stack  Find_proof
begin

(*begin insert invariant definition*)
definition invariant_wf_ts :: "bool" where
"invariant_wf_ts == (
! ts.
  wellformed_ts ts --> 
(
let ts' = step_up ts in
case ts' of 
None => True
| Some ts' => (
wellformed_ts ts'
)
))
"
(*end insert invariant definition*)

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

lemma invariant_wf_ts: "invariant_wf_ts"
(*the following two subgoals add hypothesises necessary for this proof*)
(*we need that the minimum and maximum constants have a minimum boundary 
and they are related between themselves*)
apply (subgoal_tac "1 <= min_leaf_size & 1 <= min_node_keys & (max_node_keys = 2 * min_node_keys | max_node_keys = Suc (2 * min_node_keys))") prefer 2 apply (force intro:FIXME) (* further hypothesis*)
(*we need that keys can be ordered*)
apply (subgoal_tac "total_order_key_lte") prefer 2 apply (force intro:FIXME)

apply(simp add: invariant_wf_ts_def)
apply(intro allI impI)
apply(case_tac ts)
apply(case_tac x)
apply(rename_tac ff stk)
apply(simp add: step_up_def dest_ts_def)
apply (case_tac ff,simp)
apply (rename_tac f)
apply(case_tac stk) apply(force)
apply (rename_tac hd_stk stk)
apply (subgoal_tac "? lb n i rb. hd_stk = (lb,(n,i),rb)") prefer 2 apply force
apply (erule exE)+
apply (simp)
apply (thin_tac "x=_")
apply (thin_tac "hd_stk=_")
apply(simp add: wellformed_ts_def)
apply(simp add: dest_ts_def)
apply(elim conjE)
apply (case_tac n,rename_tac ks rs)
apply simp
apply (thin_tac "n=_")
apply(subgoal_tac " wellformed_focus (update_focus_at_position (ks, rs) i f) (stk = []) &
       wellformed_context stk")
prefer 2
(* begin subproof *)
apply(intro conjI)
 (* wf_focus *)
 apply(simp add: wellformed_focus_def )
 apply (subgoal_tac "i<length rs") prefer 2 apply (force simp add:wellformed_context_i_less_than_length_rs)
 apply(subgoal_tac "wellformed_tree (Rmbs (stk=[])) (Node (ks,rs))") (* A: given that the tree without update is wf, we just need to check that rs was wf (replacing an element will leave it as before)*)
  prefer 2
   apply (case_tac stk, (force simp add:wellformed_context_1_def Let_def)+)
 apply(case_tac f)
  (* inserting_one *) (*A: this case is easier, because the stepped focus can be only insert_one *)
  apply(rename_tac t)
  apply(simp)
  apply(simp add: update_focus_at_position_def)
  apply(simp add: wellformed_tree_def)
  apply(elim conjE)
  apply (simp add:list_replace_1_at_n_def dest_Some_def)
  apply(intro conjI)
   (*wf_size (Rmbs (stk = [])) (Node (ks, rs[i := t]))*)
   apply (simp add:wf_size_def) 
   apply (subgoal_tac "wf_size_1 t") prefer 2  apply (case_tac t) apply (force simp add:forall_subtrees_def rev_apply_def)+
   apply (case_tac "stk=[]")
    (*stk=[]*)
    apply (simp add:Let_def)
    apply (metis length_list_update list_all_length nth_list_update_eq nth_list_update_neq)

    (*stk\<noteq>[]*)
    apply (simp add:Let_def forall_subtrees_def rev_apply_def wf_size_1_def list_all_iff)
    apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
    apply fast
    
   (* wf_ks_rs (Node (ks, rs[i := t])) *)
   apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def list_all_iff)
   apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
   apply fast

   (* balanced (Node (ks, rs[i := t])) *)
   apply (case_tac "rs \<noteq> []")
    (* rs \<noteq> [] *)
    apply (subgoal_tac "(height (rs!i) = height t) ") 
    prefer 2
     (* (height (rs!i) = height t) *)
     apply (simp add:wellformed_ts_1_def dest_ts_def)
    apply (simp add:balanced_def forall_subtrees_def rev_apply_def balanced_1_def del:height.simps)
    apply (elim conjE)+
    (* now I know that height rs!i = height t, so a substitution should not do any harm*)
    apply (intro conjI)
     apply (smt length_list_update list_all_length nth_list_update_eq nth_list_update_neq)
     
     apply (subgoal_tac "list_all balanced_1 (tree_to_subtrees t)") prefer 2 apply force
     apply (smt concat.simps(2) concat_append id_take_nth_drop list.map(2) list_all_append list_update_beyond map_append not_le upd_conv_take_nth_drop)

    (* rs = [] *)
    apply (simp add:wellformed_ts_1_def)

   (* keys_consistent; but this follows from wf_ts *)
   apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def)
   apply (intro conjI)
    (* keys_consistent_1 (Node (ks, rs[i := t])) *)
    apply (elim conjE)
    apply (thin_tac "list_all keys_consistent_1 (concat (map tree_to_subtrees rs))")
    apply (thin_tac "list_all keys_consistent_1 (case t of Node (l, cs) => t # map tree_to_subtrees cs |> concat | Leaf x => [t])")
    apply (simp add:keys_consistent_1_def)
    apply (elim conjE)
    apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
    apply (subgoal_tac "1 < length rs")
    prefer 2
     apply (subgoal_tac "1 <= length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty)
     apply force
    apply (subgoal_tac "? ys x zs . (rs = ys@x#zs) & (rs!i = x) & (i = length ys)") prefer 2 using id_take_nth_drop apply fastforce
    apply (erule exE)+
    apply (erule conjE)+
    apply (intro conjI)
     (* R!i \<sqsubseteq> ks!i  - ! ia : set (key_indexes (Node (ks, rs[i := t]))). check_keys None (keys (rs[i := t] ! ia)) (Some (ks ! ia))*)
     apply (simp add:nth_append)
     apply (rule)
     apply (rename_tac i')
     apply (case_tac "i' < length ys")
      (*i' < length ys*)
      apply simp
      apply (subgoal_tac "i'  :  set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force  simp add:key_indexes_def)
      apply (force)

      (*i' \<ge> length ys*)
      apply simp
      apply (case_tac "i' = length ys")
       (* i' = i *)
       apply (simp add:wellformed_ts_1_def dest_ts_def check_keys_def)
       apply (force simp add:get_lower_upper_keys_for_node_t_def key_indexes_def atLeast0LessThan lessThan_def)
       
       (*i' > length ys*)
       apply (subgoal_tac "i'  :  set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
       apply (force)
       
     (* k!i \<sqsubset> R!i+1 - ! ia : set (key_indexes (Node (ks, rs[i := t]))). check_keys (Some (ks ! ia)) (keys (rs[i := t] ! Suc ia)) None*)
     apply (simp add:nth_append)
     apply (rule)
     apply (rename_tac i')
     apply (case_tac "Suc i' < length ys")
      (*Suc i' < length ys*)
      apply (subgoal_tac "i'  :  set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
      apply force

      (*Suc i' \<ge> length ys*)
      apply simp
      apply (case_tac "Suc i' = length ys")
       (* Suc i' = i *)
       apply (simp add:get_lower_upper_keys_for_node_t_def wellformed_ts_1_def dest_ts_def check_keys_def)
       apply (case_tac ys, force, force)
       
       (*i' > length ys*)
       apply (subgoal_tac "i'  :  set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
       apply fastforce
    
    (* list_all keys_consistent_1 (concat (map tree_to_subtrees (rs[i := t]))) *)
    apply (subgoal_tac "list_all keys_consistent_1 (tree_to_subtrees t)") prefer 2 apply force
    apply ((smt concat.simps(2) concat_append id_take_nth_drop list.map(2) list_all_append list_update_beyond map_append not_le upd_conv_take_nth_drop))

   (* keys ordered *)
   apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def list_all_iff key_indexes_def)
   apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
   apply fast

  (* inserting_two *)
  apply(simp)
  apply(case_tac x2)
  apply(rename_tac tleft k0 tright)
  apply(simp add: update_focus_at_position_def)
  apply(elim conjE)
  apply(thin_tac "x2 = _")
  apply(subgoal_tac "? ks2. list_insert_at_n ks i [k0] = ks2") prefer 2 apply(force)
  apply(subgoal_tac "? rs2. list_replace_at_n rs i [tleft, tright] |> dest_Some = rs2") prefer 2 apply(force)
  apply(elim exE)+
  apply(simp add: Let_def)
  (* we do not want to case_tac on the length of ks2 for most of the proof*)
  (* so we create a node that may be fat*)
  apply (subgoal_tac "? fat_node. Node(ks2,rs2) = fat_node") prefer 2 apply force
  apply (erule exE)
  (*now we show that the fat_node is mostly wellformed (wellformed_tree')*)
  apply (subgoal_tac "wellformed_tree' (Rmbs False) fat_node") 
  prefer 2
   apply (simp add:wellformed_tree'_def wellformed_tree_def)
   apply(subgoal_tac "length ks2 = Suc (length ks)") prefer 2 apply (force simp add:list_insert_at_n_def rev_apply_def split_at_def)
   apply (intro conjI)
    (*wf_size' (Rmbs (stk = [])) (Node (ks2, rs2)) *)
    apply (drule_tac t="fat_node" in sym)
    apply simp
    apply (thin_tac "fat_node = Node(ks2,rs2)")
    apply (simp add:wf_size'_def wf_size_def)
    apply (case_tac "stk=[]")
     (*stk = []*)
     apply (subgoal_tac "wf_size_1 tleft & wf_size_1 tright") 
     prefer 2
      apply (simp add:forall_subtrees_def rev_apply_def)
      apply (case_tac tleft,simp, case_tac x1,simp,case_tac tright,simp,case_tac x1,force+)
      apply (case_tac tright,simp,case_tac x1,force+)
     apply (force simp add:Let_def list_all_of_list_replace_at_n)
    
     (*stk \<noteq> []*)
     apply (simp add: wf_size_1_def Let_def)
     apply (subgoal_tac "list_all (forall_subtrees wf_size_1) rs") prefer 2 apply (force simp add:forall_subtrees_Cons)
     apply (force simp add:list_all_of_list_replace_at_n)
    
    (* wf_ks_rs (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def )
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:wf_ks_rs_1_def)
    apply (simp add:list_replace_at_n_def)
    apply (simp add:split_at_def)
    apply (case_tac "i=0",force,force simp add:butlast_take)

    (* balanced (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (simp add:balanced_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:balanced_1_def del:height.simps)
    apply (subgoal_tac "list_replace_at_n rs i [tleft, tright] |> dest_Some = rs2") prefer 2 apply (force simp add:rev_apply_def)
    apply (subgoal_tac "height tright = height (rs!i) & height tleft = height (rs!i)") prefer 2 apply (force simp add:wellformed_ts_1_def dest_ts_def Let_def )
    apply (subgoal_tac "height (rs2!0) = height (rs!0)")
    prefer 2 
     apply (simp add:list_replace_at_n_def rev_apply_def split_at_def del:height.simps)
     apply (case_tac "i=0",force)
      (* i \<noteq> 0 *)
      apply (simp add: del:height.simps)
      apply (metis append_take_drop_id gr_implies_not0 length_0_conv length_greater_0_conv nth_append take_eq_Nil)
    apply (case_tac "rs2 = []", fast)
     (*rs2 \<noteq> []*)
     apply (metis list.size(3) list_all_length list_all_of_list_replace_at_n not_less0)

    (* keys_consistent (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:keys_consistent_1_def check_keys_def)
    (*so I know already that between tleft k0 tright there is consistency,
      while I know that there is consistency ks!i and tleft and ks!i+1 and tright by wellformed_ts_1

      I need to divide in bits this goal
    *)
    apply (simp add:list_replace_at_n_def split_at_def)
    apply (case_tac "rs = []") apply force
    (*rs ~= [] *)
    apply (subgoal_tac "? xs ys. (ks2 = xs@k0#ys) & (ks = xs @ ys) & (i = length xs)")
    prefer 2
     apply (simp add:list_insert_at_n_def split_at_def)
     using wellformed_context_i_less_than_length_rs apply fastforce
    apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
    apply (subgoal_tac "1 < length rs")
    prefer 2
     apply (subgoal_tac "1 <= length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty)
     apply force
    apply (erule exE)+
    apply (erule conjE)+
    apply simp
    apply rule
     (* key_lt --! i : set (key_indexes (Node (xs @ k0 # ys, rs2))). ! k : set (keys (rs2 ! i)). key_lt k ((xs @ k0 # ys) ! i)*)
     apply rule+
     apply (rename_tac i' k)
     apply (case_tac "i' < i")
      (*i' < i*)
      apply (subgoal_tac "xs ~= []") prefer 2 apply force
      apply simp
      apply (drule_tac t=rs2 in sym)
      apply (simp add:nth_append key_indexes_def atLeast0LessThan lessThan_def)
      apply (smt Suc_less_eq Suc_pred length_greater_0_conv less_trans_Suc)

      (* i' \<ge> i *)
      apply (case_tac "i' = i")
       (*i' = i*) (* here  i may be equal to 0*)
       apply (subgoal_tac "i' = length xs") prefer 2 apply force
       apply (drule_tac t=rs2 in sym)
       apply (force simp add:nth_append key_indexes_def wellformed_ts_1_def dest_ts_def Let_def check_keys_def)
       
       (*i' > i*) (* here  i may be equal to 0*)
       apply simp
       apply (drule_tac t=rs2 in sym)
       apply simp
       (*if i' = Suc i, we are in tright*)
       apply (case_tac "i' = Suc i")
        (*i' = Suc i, we are in tright*)
        apply (subgoal_tac "length ys ~= 0") prefer 2 apply (force simp add:key_indexes_def)
        apply (simp add: Let_def get_lower_upper_keys_for_node_t_def wellformed_ts_1_def dest_ts_def check_keys_def del:height.simps)
        apply (force simp add:nth_append)
        
        (*i' ~= Suc i*)
        apply (subgoal_tac "Suc (length xs)<i'") prefer 2 apply force
        apply (simp add:key_indexes_def atLeast0LessThan lessThan_def)
        apply (case_tac "length ys =0", force)
         (*length ys ~= 0*)
         apply (subgoal_tac "(tl (drop (length xs) rs)) = (drop (length xs +1) rs)") prefer 2 apply (force simp add:drop_Suc drop_tl)
         apply (simp add:nth_append min_def)
         apply (smt One_nat_def Suc_lessE add_2_eq_Suc atLeastLessThan_iff diff_Suc_1 diff_Suc_eq_diff_pred le_add_diff_inverse less_2_cases less_Suc0 less_imp_le_nat not_le old.nat.distinct(2))
     
     (*key_le --! i : set (key_indexes (Node (xs @ k0 # ys, rs2))). ! x : set (keys (rs2 ! Suc i)). key_le ((xs @ k0 # ys) ! i) x*)
     apply rule+
     apply (rename_tac i' k)
     apply (case_tac "Suc i' < i")
      (*Suc i' < i*)
      apply (subgoal_tac "xs ~= []") prefer 2 apply force
      apply simp
      apply (drule_tac t=rs2 in sym)
      apply (simp add:nth_append key_indexes_def atLeast0LessThan lessThan_def)
      apply (drule_tac x="i'" in spec) back
      apply force

      (* Suc i' \<ge> i *)
      apply (case_tac "Suc i' = i")
       (*i' = i*) (* here  i may be equal to 0*)
       apply (subgoal_tac "Suc i' = length xs") prefer 2 apply force
       apply (drule_tac t=rs2 in sym)
       apply (simp add:get_lower_upper_keys_for_node_t_def wellformed_ts_1_def dest_ts_def Let_def check_keys_def del:height.simps)
       apply (subgoal_tac "xs ~= []") prefer 2 apply force
       apply (simp add:nth_append key_indexes_def)
       apply (metis One_nat_def diff_Suc_1)
       
       (*Suc i' > i*) (* here  i may be equal to 0*)
       apply simp
       apply (drule_tac t=rs2 in sym)
       apply simp
       (*if Suc i' = Suc i, we are in tright*)
       apply (case_tac "Suc i' = Suc i")
        (*Suc i' = Suc i, we are in tright*)
        apply (force simp add:nth_append)
        
        (*Suc i' ~= Suc i*)
        apply (subgoal_tac "Suc (length xs) < Suc i'") prefer 2 apply force
        apply (subgoal_tac "Suc i' <= length rs") prefer 2 apply (force simp add:key_indexes_def)
        apply (simp add:key_indexes_def)
        apply (case_tac "length ys =0") apply force
        apply (subgoal_tac "(tl (drop (length xs) rs)) = (drop (length xs +1) rs)") prefer 2 apply (force simp add:drop_Suc drop_tl)
        apply (simp add:nth_append min_def)
        apply (subgoal_tac "length rs = 1+length xs + length ys") prefer 2 apply force
        apply (thin_tac " length xs + length ys = length rs - Suc 0")
        apply simp
        apply (case_tac "length ys") apply force
        apply (subgoal_tac "? x. i' = x+(Suc(length xs))") prefer 2 apply (metis Suc_leI le_add_diff_inverse2)
        apply (erule exE)
        apply force

    (* keys_ordered (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (thin_tac "length ks2 = Suc (length ks)")
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees keys_ordered_1_def)
    apply (subgoal_tac "1 <= length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty)
    apply (subgoal_tac "? xs ys. (ks2 = xs@k0#ys) & (ks = xs @ ys) & (i = length xs)")
    prefer 2
     apply (simp add:list_insert_at_n_def split_at_def)
     using wellformed_context_i_less_than_length_rs apply fastforce
    apply (erule exE)+
    apply (erule conjE)+
    apply simp
    apply rule
    apply (rename_tac i')
    apply (case_tac "Suc i'<length xs")
     (*Suc i' < length xs*)
     apply (subgoal_tac "i' < length xs") prefer 2 apply force
     apply (simp add:nth_append)
     apply (subgoal_tac "1 < length xs") prefer 2 apply force
     apply (subgoal_tac "i'  :  set (butlast (key_indexes (Node (xs @ ys, rs))))") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)
     apply (case_tac "Suc i' < length xs - Suc 0")
      (*Suc i' < length xs - Suc 0*)
      apply (subgoal_tac "Suc i'  :  set (butlast (key_indexes (Node (xs @ ys, rs))))")
      prefer 2
       apply (force simp add:key_indexes_def set_butlast_lessThan)
      apply force

      (*Suc i' \<ge> length xs - Suc 0*)
      apply (case_tac "Suc i' = length xs - Suc 0")
       (*Suc i' = length xs - Suc 0*)
       apply (subgoal_tac "i' = length xs - 2") prefer 2 apply force
       apply force

       (*Suc i' > length xs - Suc 0*)
       apply force
      
     (*Suc i' \<ge> length xs*)
     apply (case_tac "Suc i' = length xs")
      (*Suc i' = length xs*)
      apply (subgoal_tac "i' = length xs - 1") prefer 2 apply force
      apply (subgoal_tac "xs ~= []") prefer 2 apply force
      apply (simp add:wellformed_ts_1_def dest_ts_def Let_def check_keys_def nth_append)
      apply (simp add:key_indexes_def set_butlast_lessThan atLeast0LessThan lessThan_def)
      apply (drule_tac x="i'" in spec)
      apply simp
      apply (subgoal_tac "keys tleft ~= []")
      prefer 2 
       apply (simp add:wf_size_def forall_subtrees_Cons)
       apply (case_tac "tleft")
        (*tleft = Node x1*)
        apply (case_tac x1)
        apply (force simp add:keys_Cons wf_size_1_def)

        (*tleft = Leaf x2*)
        apply (force simp add:keys_def keys_1_def rev_apply_def wf_size_1_def)
      apply (subgoal_tac "? k  :  set(keys(tleft)). key_le (xs ! (length xs - Suc 0)) k & key_lt k k0")
      prefer 2
       apply (simp add:get_lower_upper_keys_for_node_t_def nth_append)
       apply (case_tac "keys tleft",force,force)
      apply (erule conjE)+
      apply simp
      using order_key_le_lt apply blast

      (*Suc i' ~= length xs*)
      apply (subgoal_tac "length xs < Suc i'") prefer 2 apply force
      apply (subgoal_tac "Suc i'  :  set (key_indexes (Node (xs @ k0 # ys, rs2)))") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)  
      apply (case_tac "i' = length xs")
       (* i' = length xs *)
       apply (simp add:get_lower_upper_keys_for_node_t_def wellformed_ts_1_def dest_ts_def Let_def check_keys_def nth_append)
       apply (force simp add:key_indexes_def atLeast0LessThan lessThan_def nth_append)
       
       (* length xs < i' *)
       apply (subgoal_tac "length xs < i'") prefer 2 apply force
       apply (case_tac i') apply force
       apply (rename_tac i'')
       apply (subgoal_tac "2 <= length ys") prefer 2 apply (case_tac "length ys < 2", force simp add:key_indexes_def) apply force
       apply simp
       (*we take only the subset we are interested in*)
       apply (subgoal_tac "!  i  :  {length xs ..<length xs + length ys - 1}.  key_lt ((xs @ ys) ! i) ((xs @ ys) ! Suc i)") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)
       apply (case_tac "i' <= length xs + length ys - 1")
        (*i' <= length xs + length ys - 1*)
        apply (force simp add:nth_append)
         
        (*i' > length xs + length ys - 1 -- this case should be false because Suc i' would not belong to {..<Suc(length xs+length ys)}*)
        apply (force simp add:key_indexes_def set_butlast_lessThan)
  (* okay we know that the fat node is mostly well formed*)
  apply (subgoal_tac "length ks2 = Suc (length ks)") prefer 2 apply (force simp add:list_insert_at_n_def split_at_def)
  apply(case_tac "length ks2 <= max_node_keys")
   (*length ks2 <= max_node_keys -- inserting_two \<rightarrow> inserting_one*)
   apply (simp add:wellformed_tree_def wellformed_tree'_def)
   (*wf_size (Rmbs (stk = [])) (Node (ks2, rs2)) *) 
   apply (drule_tac t="fat_node" in sym)
   apply simp
   apply (thin_tac "fat_node = Node(ks2,rs2)")
    apply (simp add: wf_size'_def wf_size_def)
    apply (case_tac "stk=[]",(force simp add:forall_subtrees_Cons wf_size_1_def Let_def)+)

   (*length ks2 > max_node_keys -- inserting_two \<rightarrow> inserting_two*)
   apply simp
   apply(simp add: split_node_def)
   apply (case_tac "case drop min_node_keys ks2 of x # xa => (x, xa)")
   apply (rename_tac "k" "right_ks")
   apply (subgoal_tac "? left_ks. take min_node_keys ks2 = left_ks") prefer 2 apply force
   apply (subgoal_tac "? right_rs. drop (Suc min_node_keys) rs2 = right_rs") prefer 2 apply force
   apply (subgoal_tac "? left_rs. take (Suc min_node_keys) rs2 = left_rs") prefer 2 apply force
   apply (erule exE)+
   apply (subgoal_tac "((set right_rs) \<subseteq> set rs2) & ((set left_rs) \<subseteq> set rs2)") prefer 2 apply (simp add:list_replace_at_n_def split_at_def rev_apply_def) apply (meson  set_drop_subset set_take_subset)
   apply simp 
   (*wellformed_tree (Rmbs False) (Node (left_ks, left_rs))*)
   apply (simp add:wellformed_tree_def wellformed_tree'_def)
   apply (drule_tac t="fat_node" in sym)
   (*wf_size*)
   apply (subgoal_tac "wf_size (Rmbs False) (Node (left_ks, left_rs)) & wf_size (Rmbs False) (Node (right_ks, right_rs))")
   prefer 2
    apply (thin_tac "f = Inserting_two (tleft, k0, tright)")
    apply (thin_tac "wf_size (Rmbs False) tleft & wf_ks_rs tleft & balanced tleft & keys_consistent tleft & keys_ordered tleft ")
    apply (thin_tac "wf_size (Rmbs False) tright & wf_ks_rs tright & balanced tright & keys_consistent tright & keys_ordered tright")
    apply (simp add:wf_size_def wf_size'_def list_all_iff forall_subtrees_def rev_apply_def)
    apply (subgoal_tac "wf_size_1 (Node (left_ks, left_rs)) & wf_size_1 (Node (right_ks, right_rs))")
    prefer 2
     (*here we need the hypothesis 1<= min_node_size and max_node_size= 2*min_node_size etc*)
     apply (simp add:wf_size_1_def Let_def)
     apply (subgoal_tac "0 < length ks") prefer 2 apply force
     apply (subgoal_tac "(length ks) <= max_node_keys") prefer 2 apply (case_tac stk) apply force apply (force simp add:forall_subtrees_def rev_apply_def Let_def wf_size_1_def)
     apply (subgoal_tac "drop min_node_keys ks2 = k#right_ks")
     prefer 2
      apply (case_tac "drop min_node_keys ks2")
       (*drop min_node_keys ks2 = []*)
       apply (subgoal_tac "\<not> (length ks2 <= min_node_keys)") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
       apply (metis drop_eq_Nil)
       
       apply force
     apply (subgoal_tac "tl (drop min_node_keys ks2) = right_ks & hd (drop min_node_keys ks2) = k ") prefer 2 apply force
     apply (thin_tac "drop min_node_keys ks2 = k # right_ks")
     apply (erule conjE)+
     apply simp
     apply (subgoal_tac "length ks = max_node_keys") prefer 2
      apply fastforce
     apply force
    apply blast
   (*wf_ks_rs*)
   apply (subgoal_tac "wf_ks_rs (Node (left_ks, left_rs)) & wf_ks_rs (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "wf_ks_rs_1 (Node (left_ks, left_rs)) & wf_ks_rs_1 (Node (right_ks, right_rs))")
    prefer 2
     apply (drule_tac t="left_rs" in sym,drule_tac t="right_rs" in sym,drule_tac t="left_ks" in sym)
     apply (subgoal_tac "drop min_node_keys ks2 = k # right_ks")
     prefer 2
      apply (case_tac "drop min_node_keys ks2")
       (*drop min_node_keys ks2 = []*)
       apply (subgoal_tac "\<not> (length ks2 <= min_node_keys)") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
       apply (metis drop_eq_Nil)
       
       apply force
     apply (simp add:wf_ks_rs_1_def)
     apply (subgoal_tac "length rs2 = (Suc (length rs))") prefer 2 apply force
     apply (subgoal_tac "length right_ks = length rs - Suc min_node_keys") prefer 2 apply (metis drop_Suc length_drop list.sel(3) tl_drop)
     apply simp
     apply (metis Suc_diff_Suc drop_eq_Nil list.distinct(1) not_le)
    apply blast
   (*balanced*)
   apply (subgoal_tac "balanced (Node (left_ks, left_rs)) & balanced (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:balanced_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "balanced_1 (Node (left_ks, left_rs)) & balanced_1 (Node (right_ks, right_rs))")
    prefer 2
     apply (simp add:balanced_1_def del:height.simps)
     apply (case_tac "rs2 = []",force)
      
      apply (case_tac "left_rs = []") apply force
      apply (case_tac "right_rs = []") apply force
       apply (subgoal_tac "left_rs ! 0 = rs2 ! 0") prefer 2 apply force
       apply (smt Cons_nth_drop_Suc append_take_drop_id drop_all list_all_append list_all_length not_le nth_Cons_0)
    apply blast

   (*keys_consistent*)
   apply (subgoal_tac "keys_consistent (Node (left_ks, left_rs)) & check_keys None (keys (last left_rs)) (Some k)  & check_keys (Some k) (keys (hd right_rs)) None & keys_consistent (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "keys_consistent_1 (Node (left_ks, left_rs)) & check_keys None (keys (last left_rs)) (Some k)  & check_keys (Some k) (keys (hd right_rs)) None & keys_consistent_1 (Node (right_ks, right_rs))")
    prefer 2
     apply (simp add:keys_consistent_1_def)
     apply (subgoal_tac "drop min_node_keys ks2 = k # right_ks")
     prefer 2
      apply (case_tac "drop min_node_keys ks2")
       (*drop min_node_keys ks2 = []*)
       apply (subgoal_tac "\<not> (length ks2 <= min_node_keys)") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
       apply (metis drop_eq_Nil)
       
       apply force
     apply (drule_tac s="length ks2" in sym)
     apply (subgoal_tac "left_ks ~= [] & right_ks ~= [] & min_node_keys < length ks2") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
     apply (subgoal_tac "left_rs ~= [] & right_rs ~= []") prefer 2 apply (force simp add:wf_ks_rs_def wf_ks_rs_1_def wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
     apply (drule_tac t="left_ks" in sym)
     apply (subgoal_tac "tl (drop min_node_keys ks2) = right_ks & hd (drop min_node_keys ks2) = k ") prefer 2 apply force
     apply (thin_tac "drop min_node_keys ks2 = k # right_ks")
     apply (erule conjE)+
     apply simp
     apply (drule_tac t="right_ks" in sym)
     apply (drule_tac t="left_rs" in sym)
     apply (drule_tac t="right_rs" in sym)
     apply (drule_tac t="k" in sym)
     apply (simp add:key_indexes_def set_butlast_lessThan check_keys_def)
     apply (simp add: hd_drop_conv_nth nth_tl tl_drop)
     apply (subgoal_tac "Suc (length ks2) = length rs2") prefer 2 apply (force simp add:wf_ks_rs_def wf_ks_rs_1_def forall_subtrees_def rev_apply_def Let_def)
     apply (simp add:min_def)
     apply (simp add:hd_conv_nth last_conv_nth)
     apply (metis (no_types, lifting) One_nat_def Suc_leD Suc_mono append_take_drop_id atLeastLessThan_iff diff_Suc_1 diff_add_inverse2 diff_diff_cancel length_append length_drop length_take less_imp_le_nat)
    apply blast
   (*keys_ordered*)
   apply (subgoal_tac "keys_ordered  (Node (left_ks, left_rs)) & key_lt (last left_ks) k & key_lt k (hd right_ks)  & keys_ordered  (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "keys_ordered_1 (Node (left_ks, left_rs)) & key_lt (last left_ks) k & key_lt k (hd right_ks)  & keys_ordered_1 (Node (right_ks, right_rs))")
    prefer 2
     apply (erule conjE)+
     apply (thin_tac "! x : set (case tleft of Node (l, cs) => tleft # map tree_to_subtrees cs |> concat | Leaf x => [tleft]). keys_ordered_1 x")
     apply (thin_tac "! x : set (case tright of Node (l, cs) => tright # map tree_to_subtrees cs |> concat | Leaf x => [tright]). keys_ordered_1 x")
     apply (thin_tac "! a : set rs. ! x : set (case a of Node (l, cs) => a # map tree_to_subtrees cs |> concat | Leaf x => [a]). keys_ordered_1 x")
     apply (thin_tac "! a : set rs2. ! x : set (case a of Node (l, cs) => a # map tree_to_subtrees cs |> concat | Leaf x => [a]). keys_ordered_1 x")
     apply (thin_tac "keys_ordered_1 (Node (ks, rs))")
     apply (simp add:keys_ordered_1_def)
     apply (subgoal_tac "drop min_node_keys ks2 = k # right_ks")
     prefer 2
      apply (case_tac "drop min_node_keys ks2")
       (*drop min_node_keys ks2 = []*)
       apply (subgoal_tac "\<not> (length ks2 <= min_node_keys)") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
       apply (metis drop_eq_Nil)
       
       apply force
     apply (drule_tac s="length ks2" in sym)
     apply (subgoal_tac "left_ks ~= [] & right_ks ~= [] & min_node_keys < length ks2") prefer 2 apply (force simp add:wf_size_def wf_size_1_def forall_subtrees_def rev_apply_def Let_def)
     apply (simp add:last_conv_nth hd_conv_nth)
     apply (drule_tac t="left_ks" in sym)
     apply (subgoal_tac "tl (drop min_node_keys ks2) = right_ks & hd (drop min_node_keys ks2) = k ") prefer 2 apply force
     apply (thin_tac "drop min_node_keys ks2 = k # right_ks")
     apply (erule conjE)+
     apply simp
     apply (drule_tac t="right_ks" in sym)
     apply (drule_tac t="k" in sym)
     apply (simp add:key_indexes_def set_butlast_lessThan)
     apply (simp add:min_def)
     apply (simp add: hd_drop_conv_nth nth_tl tl_drop)
     apply (metis Suc_pred atLeastLessThan_iff diff_Suc_1 less_Suc_eq_0_disj less_Suc_eq_le neq0_conv)
    apply blast

   (*check_keys*)
   apply (subgoal_tac "check_keys None (keys (Node (left_ks, left_rs))) (Some k) & check_keys (Some k) (keys (Node (right_ks, right_rs))) None")
   prefer 2
    (*cleanup hypothesises*)
    apply (thin_tac "wf_size' (Rmbs False) fat_node & wf_ks_rs fat_node & balanced fat_node & keys_consistent fat_node & keys_ordered fat_node ")
    apply (thin_tac "wf_size (Rmbs (stk = [])) (Node (ks, rs)) &
       wf_ks_rs (Node (ks, rs)) & balanced (Node (ks, rs)) & keys_consistent (Node (ks, rs)) & keys_ordered (Node (ks, rs))")
    apply (thin_tac "wf_size (Rmbs False) tleft & wf_ks_rs tleft & balanced tleft & keys_consistent tleft & keys_ordered tleft")
    apply (thin_tac "wf_size (Rmbs False) tright & wf_ks_rs tright & balanced tright & keys_consistent tright & keys_ordered tright")
    apply (thin_tac "check_keys None (keys tleft) (Some k0)")
    apply (thin_tac "check_keys (Some k0) (keys tright) None")
    apply (simp add:check_keys_def)
    apply (simp add:keys_Cons)
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def list_all_iff keys_ordered_1_def Let_def)
    apply (simp add:key_indexes_def set_butlast_lessThan)
    apply (subgoal_tac "left_ks ~= []") prefer 2 apply force
    apply rule+
     apply (subgoal_tac "!  x  :  set left_ks. key_lt x k")
     prefer 2
      using bigger_than_last_in_list_sorted_by_key_lt' apply presburger
     apply (subgoal_tac "!  x  :  (UN a : (set left_rs). set (keys a)). key_lt x k")
     prefer 2
      apply (subgoal_tac "((! i : {0..<length left_ks}. ! k : set (keys (left_rs ! i)). key_lt k (left_ks ! i)))") prefer 2 apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def key_indexes_def check_keys_def)      
      apply (subgoal_tac "length left_rs = Suc (length left_ks)") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def key_indexes_def check_keys_def) 
      using bigger_than_subkeys_in_list_sorted_by_key_lt' apply presburger
     apply force
     
     apply (subgoal_tac "right_ks ~= []") prefer 2 apply (force simp add:wf_size_def forall_subtrees_def rev_apply_def wf_size_1_def)
     apply (subgoal_tac "!  x  :  set right_ks. key_lt k x")
     prefer 2
      using k_klt_hd_klt_all apply presburger
     apply (subgoal_tac "!  x  :  UN a : set right_rs. set (keys a). key_le k x")
     prefer 2
      apply (subgoal_tac "length right_rs = Suc (length right_ks)") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def key_indexes_def check_keys_def) 
      apply (subgoal_tac "(! i : {0..<length right_ks}. ! x : set (keys (right_rs ! Suc i)). key_le (right_ks ! i) x)") prefer 2 apply (force simp add:keys_consistent_def forall_subtrees_def rev_apply_def keys_consistent_1_def key_indexes_def check_keys_def)
      using k_klt_hdsubkeys_kle_allsubkeys apply presburger
    apply (force simp add:key_le_def)
   apply force

 (* wf_context *)
 apply(force intro: wellformed_context_hereditary)
(* end subproof *)
apply(elim conjE)

apply(simp)
(* wf_ts_1 *)
apply(simp add: update_focus_at_position_def)
apply(case_tac f)
 (* i1 *)
 apply (rename_tac "new_focus")
 apply(simp add: wellformed_ts_def wellformed_ts_1_def dest_ts_def Let_def del:height.simps)
 apply (case_tac "stk") apply force
 
 (* stk = (lb,((l,c) i'),rb) *)
 apply (rename_tac hd_stk tl_stk)
 apply simp
 apply (subgoal_tac "? lb' l cs i' rb'. hd_stk = (lb',((l, cs), i'),rb')") prefer 2 apply force
 apply (erule exE)+
 apply (subgoal_tac "cs ! i' = Node(ks,rs)") prefer 2 apply (force simp add:is_subnode_def)
 apply (simp add:list_replace_1_at_n_def)
 apply rule
  (*height of old focus equal to height of new focus*)
  apply (simp add:wellformed_focus_def wellformed_tree_def balanced_def)
  apply (metis height.simps list.set_map list_update_id map_update)
  
  (*keys of new focus maintain the order of the old focus*)
  apply rule+
  apply (subgoal_tac "0 < length l & i <= length ks & i' <= length l & keys_consistent(Node(l,cs)) ") prefer 2 apply (case_tac tl_stk,(force simp add:Let_def wellformed_context_1_def subtree_indexes_def is_subnode_def wellformed_tree_def wf_ks_rs_def wf_size_def forall_subtrees_Cons wf_ks_rs_1_def wf_size_1_def)+)
  apply (subgoal_tac "keys_consistent(Node(ks,rs[i := new_focus]))") prefer 2 apply (force simp add:wellformed_focus_def wellformed_tree_def)
  apply (simp add:keys_consistent_def forall_subtrees_Cons keys_consistent_1_def key_indexes_def atLeast0LessThan lessThan_def check_keys_def) 
  apply (simp add:get_lower_upper_keys_for_node_t_def)
  apply (rename_tac l u)
  apply (subgoal_tac "? l_rs r_rs rsi. rs=l_rs@rsi#r_rs & (length l_rs = i) ")
  prefer 2 
   apply (subgoal_tac "i <= length ks & i < length rs & rs ~= []") prefer 2  apply (force simp add:Let_def wellformed_tree_def wellformed_context_1_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def subtree_indexes_def)
   apply (metis (no_types, lifting) Cons_nth_drop_Suc diff_add_inverse2 diff_diff_cancel id_take_nth_drop length_append length_drop less_imp_le_nat)
  apply (erule exE)+
  apply (simp)
  apply (subgoal_tac " ((l_rs @ rsi # r_rs)[i := new_focus] = l_rs@new_focus#r_rs)") prefer 2 apply force
  apply (simp add:rev_apply_def)
  apply (subgoal_tac "case l of Some kl => Ball (set (keys (Node (ks, rs[i := new_focus])))) (key_le kl) | _ => True ")
  prefer 2
   apply (case_tac l,force)
   apply simp
   apply (rename_tac kl)
   apply (simp add:keys_Cons check_keys_def rev_apply_def)
   apply (subgoal_tac "wellformed_context_1 (Rmbs (tl_stk=[])) (lb', ((la, cs), i'), rb')") prefer 2 apply (case_tac tl_stk) apply (force simp add:Let_def get_lower_upper_keys_for_node_t_def) apply (force simp add:Let_def get_lower_upper_keys_for_node_t_def)
   apply (simp add:wellformed_context_1_def)    
   (*we need to instantiate the bounds of the grandparent*)   
   apply (case_tac "i'=0")
    apply simp
    (*we need to instantiate the bounds of the parent now*)
    apply (case_tac "i=0")
     (*i = 0*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     apply (erule conjE)+
     apply (drule_tac s=lb in sym)
     apply blast

     (*i ~= 0 *)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     apply (erule conjE)+
     apply simp
     (*we know that ! x:sks . key_le kl x and that !x:snew_focus. key_le (ks!i-1) x and !x:new_focus. key_le (ks!i-1) x (this is obtainable)*)
     apply (subgoal_tac "i - Suc 0 < length ks") prefer 2 apply linarith
     apply (subgoal_tac "!x : set (keys new_focus). key_le (ks!(i-1)) x") prefer 2     
      apply (drule_tac x="i-1" in spec) back
      apply (force)
     apply (thin_tac "\<forall>i<length ks. \<forall>x\<in>set (keys ((l_rs @ new_focus # r_rs) ! Suc i)). key_le (ks ! i) x")
     apply simp
     apply (subgoal_tac " key_le kl (ks!(i-1))") prefer 2 apply force
    apply (subgoal_tac "!x : set (keys new_focus). key_le kl x")
     prefer 2
      using order_key_le apply (metis One_nat_def)
     apply blast
     
    (*i' ~= 0*)
    apply simp
    apply (erule conjE)+
    apply (drule_tac t=kl in sym)
    apply (simp add:Let_def is_subnode_def keys_Cons)
    apply (subgoal_tac "\<forall>x\<in>set (keys (cs ! i')). key_le (la ! (i' - Suc 0)) x") prefer 2 apply force
    apply (thin_tac "\<forall>i<length la. \<forall>x\<in>set (keys (cs ! Suc i)). key_le (la ! i) x")
    apply (simp add:keys_Cons check_keys_def rev_apply_def)
    apply (subgoal_tac "lb' = Some (la ! (i' - Suc 0))") prefer 2 apply (case_tac "tl_stk") apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) 
    apply (case_tac "i=0")
     (*i = 0*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     apply (drule_tac s=lb in sym)
     apply blast

     (*i ~= 0 *)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     apply (erule conjE)+
     (*we know that ! x:sks . key_le kl x and that !x:snew_focus. key_le (ks!i-1) x and !x:new_focus. key_le (ks!i-1) x (this is obtainable)*)
     apply (subgoal_tac "i - Suc 0 < length ks") prefer 2 apply (linarith)
     apply (subgoal_tac "!x : set (keys new_focus). key_le (ks!(i-1)) x") prefer 2     
      apply (drule_tac x="i-1" in spec) back
      apply (force)
     apply (thin_tac "\<forall>i<length ks. \<forall>x\<in>set (keys ((l_rs @ new_focus # r_rs) ! Suc i)). key_le (ks ! i) x")
     apply simp
     apply (subgoal_tac " key_le kl (ks!(i-1))") prefer 2 apply force
     apply (subgoal_tac "!x : set (keys new_focus). key_le kl x")
     prefer 2
      using order_key_le apply (metis One_nat_def)
     apply blast
  apply (subgoal_tac "case u of Some kr => (!k : set (keys (Node (ks, rs[i := new_focus]))). key_lt k kr) | _ => True")
  prefer 2
   apply (case_tac u,force)
   apply simp
   apply (rename_tac kr)
   apply (simp add:keys_Cons check_keys_def rev_apply_def)
   apply (subgoal_tac "wellformed_context_1 (Rmbs (tl_stk=[])) (lb', ((la, cs), i'), rb')") prefer 2 apply (case_tac "tl_stk") apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def)
   apply (simp add:wellformed_context_1_def)
   (*we need to instantiate the bounds of the grandparent*)   
   apply (case_tac "i' = length la")
    (*i' = length la*)
    apply simp
    apply (case_tac "i = length ks")
     (*i = length ks*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def is_subnode_def Let_def)
     apply (erule conjE)+
     apply simp
     apply blast

     (*i < length ks*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     apply (erule conjE)+
     apply simp
     (*we know that ! x:sks . key_le kl x and that !x:snew_focus. key_le (ks!i-1) x and !x:new_focus. key_le (ks!i-1) x (this is obtainable)*)
     apply (subgoal_tac "!x : set (keys new_focus). key_lt x (ks!i)") prefer 2     
      apply (force)
     apply (subgoal_tac " key_lt (ks!(i)) kr") prefer 2 apply force
    apply (subgoal_tac "!x : set (keys new_focus). key_lt x kr")
     prefer 2
      using order_key_lt apply meson
     apply blast
    
    (*i' < length la*)
    apply simp
    apply (erule conjE)+
    apply (drule_tac t=kr in sym)
    apply (simp add:Let_def is_subnode_def keys_Cons)
    apply (subgoal_tac "\<forall>x\<in>set (keys (cs ! i')). key_lt x (la ! i')") prefer 2 apply force
    apply (thin_tac "\<forall>i<length la. \<forall>x\<in>set (keys (cs ! i)). key_lt  x (la ! i)")
    apply (simp add:keys_Cons check_keys_def rev_apply_def)
    apply (subgoal_tac "rb' = Some (la ! (i'))") prefer 2 apply (case_tac "tl_stk") apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) 
    apply (case_tac "i = length ks")
     (*i = length ks*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def is_subnode_def Let_def)
     apply (erule conjE)+
     apply blast

     (*i < length ks*)
     apply (simp add:keys_Cons check_keys_def rev_apply_def)
     (*we know that ! x:sks . key_le kl x and that !x:snew_focus. key_le (ks!i-1) x and !x:new_focus. key_le (ks!i-1) x (this is obtainable)*)
     apply (subgoal_tac "!x : set (keys new_focus). key_lt x (ks!i)") prefer 2     
      apply (force)
     apply (subgoal_tac " key_lt (ks!(i)) kr") prefer 2 apply force
    apply (subgoal_tac "!x : set (keys new_focus). key_lt x kr")
     prefer 2
      using order_key_lt apply meson
     apply blast
  apply (case_tac l)
   (*l = None*)
   apply (case_tac u)
    apply force
    apply force
   
   (*l = Some kl*)
   apply (case_tac u)
    (* u = None *)
    apply force

    (* u = Some kr *)
    apply force

 (* i2 *)
 apply(simp)
 apply(subgoal_tac "? tleft k0 tr. x2 = (tleft,k0,tr)") prefer 2 apply(force)
 apply(elim exE)
 apply(simp)
 apply(subgoal_tac "? ks2. list_insert_at_n ks i [k0]  = ks2") prefer 2 apply(force)
 apply(subgoal_tac "? rs2. list_replace_at_n rs i [tleft, tr] |> dest_Some = rs2") prefer 2 apply(force)
 apply(elim exE)
 apply(simp add: Let_def)
 apply (subgoal_tac "? fat_node. Node(ks2,rs2) = fat_node") prefer 2 apply force
 apply (erule exE)
 apply (subgoal_tac "wellformed_ts_1 (Tree_stack (Focus(Inserting_one fat_node), stk))")
 prefer 2
  apply (simp add:wellformed_ts_1_def dest_ts_def)
  apply (case_tac stk,force)
  (*stk~=[]*)
  apply (rename_tac hd_stk tl_stk)
  apply simp
  apply (subgoal_tac "? lb' l cs i' rb' . hd_stk = (lb', ((l, cs), i'), rb')") prefer 2 apply force
  apply (erule exE)+
  apply simp
  apply (drule_tac t=fat_node in sym)
  apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:wellformed_tree_def wellformed_context_1_def subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
  apply (subgoal_tac "rs2 ~= []") prefer 2 apply (force simp add:list_replace_at_n_def split_at_def rev_apply_def)
  apply (subgoal_tac "set rs2 \<subseteq> set rs \<union> {tleft} \<union> {tr}")
   prefer 2
    apply (drule_tac t=rs2 in sym)
    apply (simp add:list_replace_at_n_def split_at_def rev_apply_def)
    apply rule
     (*set (take i rs) \<subseteq> insert tr (insert tleft (set rs))*)
     apply (meson insert_iff set_take_subset subsetCE subsetI)
     
     (*set (tl (drop i rs)) \<subseteq> insert tr (insert tleft (set rs))*)
     apply (metis Cons_nth_drop_Suc in_set_dropD insert_iff list.sel(3) subsetI)
  apply rule+
   (*height*)
   apply (subgoal_tac "cs ! i' = Node(ks,rs)") prefer 2 apply (force simp add: is_subnode_def Let_def)
   apply (subgoal_tac "? hrsi. (case rs ! i of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1) = hrsi") prefer 2 apply force
   apply (erule exE)
   apply simp
   apply (subgoal_tac "height ` set rs2 \<subseteq> height ` (set rs \<union> {tleft} \<union> {tr})") prefer 2 apply blast
   apply simp
   apply (subgoal_tac "height ` (set rs) = {hrsi}")
   prefer 2
    apply (simp add:wellformed_context_1_def wellformed_tree_def balanced_def Let_def forall_subtrees_Cons balanced_1_def list_all_iff)
    apply (subgoal_tac "set rs ~= {} ") prefer 2 apply (force simp add:subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
    apply (erule conjE)+
    apply (simp (no_asm) add:image_def)
    apply clarify
    apply simp
    apply (subgoal_tac "(case rs ! 0 of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1) = (case tleft of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1)")
    prefer 2 
     apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
     apply force
    apply (smt Collect_cong length_greater_0_conv nth_mem singleton_conv)
   apply simp
   apply (subgoal_tac "height ` set rs2 = {} | height ` set rs2 = {hrsi}") prefer 2 apply (metis subset_singletonD)
   apply force
   (*check_keys*)
   apply rule+
   apply (rename_tac lbk ubk)
   apply (simp add:get_lower_upper_keys_for_node_t_def Let_def)
   apply (simp add:wellformed_focus_def Let_def)
   apply (simp add:wellformed_context_1_def Let_def)
   apply (erule conjE)+
   apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:wellformed_tree_def subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
   apply (simp add:keys_Cons rev_apply_def check_keys_def)
   apply (subgoal_tac "set ks2 = (set ks \<union> {k0})") prefer 2 apply (drule_tac t=ks2 in sym) apply (simp add:list_insert_at_n_def split_at_def ) apply (metis append_take_drop_id set_append)
   apply (subgoal_tac "wellformed_context_1 (Rmbs (tl_stk = [])) (lb',((l,cs),i'),rb')") prefer 2 apply (case_tac tl_stk) apply force apply force
   apply (subgoal_tac "(case lbk of None \<Rightarrow> True | Some kl \<Rightarrow> Ball (set (ks2 @ concat (map keys rs2))) (key_le kl))")
   prefer 2
    apply (subgoal_tac "lbk = lb'") prefer 2 apply (case_tac tl_stk) apply simp  apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) apply simp apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def)
    apply (case_tac lbk,force)
    apply (rename_tac kl)
    apply simp
    apply (subgoal_tac "(key_le kl k0) & (!x : set (keys tleft). key_le kl x)") (*this hypothesis is useful for the following subgoals*)
    prefer 2
     apply (case_tac "i'=0")
      (*i' = 0 *)
      apply (case_tac "i=0",force)
       (*i ~= 0*)
       apply (simp add:wellformed_context_1_def check_keys_def)
       apply (erule conjE)+
       apply (case_tac lb',force)
       apply simp
       apply (drule_tac t=a in sym)
       apply simp
       apply (thin_tac "a=_")
       apply (subgoal_tac "key_le kl (ks ! (i - Suc 0))") prefer 2 apply (simp add:is_subnode_def subtree_indexes_def) apply (drule_tac t="cs!0" in sym) apply (force simp add: keys_Cons)
       apply simp
       using order_key_le apply blast
      (*i' ~= 0*)
      apply simp
      apply (case_tac "i=0",force)
       (*i ~= 0*)
       apply simp
       apply (simp add:wellformed_context_1_def check_keys_def)
       apply (erule conjE)+
       apply (case_tac lb',force)
       apply simp
       apply (drule_tac t=a in sym)
       apply simp
       apply (thin_tac "a=_")
       (*key ks!(i-1) belongs to subnode of N(l,cs) at position i' *)
       apply (simp add:is_subnode_def Let_def subtree_indexes_def)
       apply (drule_tac t="cs!i'" in sym)
       apply (simp add:keys_Cons)
       apply (subgoal_tac " key_le (l ! (i' - Suc 0)) (ks ! (i - Suc 0))") prefer 2 apply force
       apply (thin_tac "\<forall>x\<in>set ks \<union> set (map keys rs |> concat). key_le (l ! (i' - Suc 0)) x")
       using order_key_le apply blast     
    apply (subgoal_tac "!x : set ks2. key_le kl x")
    prefer 2
     (*given set ks2 = (set ks \<union> {k0}) we just have to show the order for ks and k0*)
     apply (subgoal_tac "!x : set ks. key_le kl x")
     prefer 2
      apply (simp add:wellformed_context_1_def check_keys_def is_subnode_def) 
      apply (erule conjE)+
      apply (drule_tac t="cs!i'" in sym)
      apply (drule_tac s="Some kl" in sym) 
      apply (force simp add:keys_Cons)
     apply force
    apply (subgoal_tac "!x : UN a : set rs2. set (keys a). key_le kl x")
    prefer 2
     (*we know that set set rs2 \<subseteq> insert tr (insert tleft (set rs)) so we can decompose the thing *)
     apply (subgoal_tac "!x : UN a : set rs. set (keys a). key_le kl x")
     prefer 2
      apply simp
      apply (erule conjE)+
      apply (simp add:wellformed_context_1_def check_keys_def)
      apply (drule_tac s="Some kl" in sym)
      apply (simp add:is_subnode_def Let_def)
      apply (drule_tac t="cs!i'" in sym)
      apply (simp add:keys_Cons rev_apply_def)
      apply blast
     apply (subgoal_tac "!x : set (keys tr). key_le kl x") prefer 2 using order_key_le apply blast
     apply blast
    apply force
   apply (subgoal_tac "(case ubk of None \<Rightarrow> True | Some kr \<Rightarrow> \<forall>k\<in>set (ks2 @ concat (map keys rs2)). key_lt k kr)")
   prefer 2
    apply (subgoal_tac "ubk = rb'") prefer 2 apply (case_tac tl_stk) apply simp  apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def) apply simp apply (force simp add:get_lower_upper_keys_for_node_t_def Let_def)   
    apply (case_tac ubk,force)
    apply (rename_tac kr)
    apply simp
    apply (subgoal_tac "(key_lt k0 kr) & (!x : set (keys tr). key_lt x kr)") (*this hypothesis is useful for the following subgoals*)
    (*start*)
    prefer 2
     apply (case_tac "i'=length l")
      (*i' = 0 *)
      apply (case_tac "i=length ks",force)
       (*i ~= 0*)
       apply (simp add:wellformed_context_1_def check_keys_def)
       apply (erule conjE)+
       apply (case_tac rb',force)
       apply simp
        apply (drule_tac t=a in sym)
       apply simp
       apply (thin_tac "a=_")
       apply (subgoal_tac "key_lt (ks ! i) kr") prefer 2 apply (simp add:is_subnode_def subtree_indexes_def) apply (drule_tac t="cs!(length l)" in sym) apply (force simp add: keys_Cons)
       apply simp
       using order_key_lt apply blast
      (*i' ~= 0*)
      apply simp
      apply (case_tac "i=(length ks)",force)
       (*i ~= 0*)
       apply simp
       apply (simp add:wellformed_context_1_def check_keys_def)
       apply (erule conjE)+
       apply (case_tac rb',force)
       apply simp
       apply (drule_tac t=a in sym)
       apply simp
       apply (thin_tac "a=_")
       (*key ks!(i-1) belongs to subnode of N(l,cs) at position i' *)
       apply (simp add:is_subnode_def Let_def subtree_indexes_def)
       apply (drule_tac t="cs!i'" in sym)
       apply (simp add:keys_Cons)
       apply (subgoal_tac " key_lt (ks ! (i)) (l ! (i'))") prefer 2 apply force       
       apply (thin_tac "\<forall>k\<in>set ks \<union> set (map keys rs |> concat). key_lt k (l ! i')")
       using order_key_lt apply blast  
    (*end*)
    apply (subgoal_tac "!x : set ks2. key_lt x kr")
    prefer 2
     (*given set ks2 = (set ks \<union> {k0}) we just have to show the order for ks and k0*)
     apply (subgoal_tac "!x : set ks. key_lt x kr")
     prefer 2
      apply (simp add:wellformed_context_1_def check_keys_def is_subnode_def) 
      apply (erule conjE)+
      apply (drule_tac t="cs!i'" in sym)
      apply (drule_tac s="Some kr" in sym) 
      apply (force simp add:keys_Cons)
     apply force
    apply (subgoal_tac "!x : UN a : set rs2. set (keys a). key_lt x kr")
    prefer 2
     (*we know that set set rs2 \<subseteq> insert tr (insert tleft (set rs)) so we can decompose the thing *)
     apply (subgoal_tac "!x : UN a : set rs. set (keys a). key_lt x kr")
     prefer 2
      apply simp
      apply (erule conjE)+
      apply (simp add:wellformed_context_1_def check_keys_def)
      apply (drule_tac s="Some kr" in sym)
      apply (simp add:is_subnode_def Let_def)
      apply (drule_tac t="cs!i'" in sym)
      apply (simp add:keys_Cons rev_apply_def)
      apply blast
     apply (subgoal_tac "!x : set (keys tleft). key_lt x kr") prefer 2 using order_key_lt apply blast
     apply blast
    apply force
   apply force
 (* we can now proceed to solve the two cases of Inserting_two *)
 apply (case_tac "length ks2 <= max_node_keys")
  (*length ks2 <= max_node_keys*)
  apply force  

  (*length ks2 > max_node_keys*)
  apply simp
  apply (simp add:wellformed_ts_1_def dest_ts_def Let_def)
  apply (case_tac stk, force)  
  apply (rename_tac hd_stk tl_stk)
  (*stk = hd_stk#tl_stk*)
  apply simp
  apply (subgoal_tac "? lb' l cs i' rb' . hd_stk = (lb', ((l, cs), i'), rb')") prefer 2 apply force 
  apply (erule exE)+
  apply simp
  apply (case_tac "get_lower_upper_keys_for_node_t l lb' i' rb'")
  apply simp
  apply (rename_tac lb rb)
  apply(simp add: split_node_def)
  apply (case_tac "case drop min_node_keys ks2 of x # xa => (x, xa)")
  apply (rename_tac "k" "right_ks")  
  apply (subgoal_tac "? left_ks. take min_node_keys ks2 = left_ks") prefer 2 apply force
  apply (subgoal_tac "? right_rs. drop (Suc min_node_keys) rs2 = right_rs") prefer 2 apply force
  apply (subgoal_tac "? left_rs. take (Suc min_node_keys) rs2 = left_rs") prefer 2 apply force
  apply (erule exE)+
  apply (drule_tac t=fat_node in sym)
  apply (subgoal_tac "k  :  set ks2")
  prefer 2
   apply (subgoal_tac "min_node_keys < length ks2") prefer 2 apply linarith
   apply (metis (no_types, lifting) Cons_nth_drop_Suc in_set_conv_nth list.simps(5) prod.inject)
  apply (subgoal_tac "((set right_rs) \<subseteq> set rs2) & ((set left_rs) \<subseteq> set rs2)") prefer 2 apply (simp add:list_replace_at_n_def split_at_def rev_apply_def) apply (meson  set_drop_subset set_take_subset)
  apply (subgoal_tac "set (keys (Node (left_ks, left_rs))) \<subseteq> set (keys fat_node) & set (keys (Node (right_ks, right_rs))) \<subseteq> set (keys fat_node)")
  prefer 2 
   apply (subgoal_tac "min_node_keys < length ks2") prefer 2 apply linarith
   apply (subgoal_tac "set left_ks \<subseteq> set ks2") prefer 2 apply (meson set_take_subset)
   apply (subgoal_tac "set right_ks \<subseteq> set ks2") prefer 2 apply (smt Cons_nth_drop_Suc list.simps(5) prod.inject set_drop_subset)
   apply (simp add:keys_Cons rev_apply_def)
   apply fast
  apply simp
  apply (thin_tac "fat_node=_")
  apply (erule conjE)+
  (*we work to solve the height part of the subgoal*)
  apply (subgoal_tac "? hrsi.(case rs ! i of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1) = hrsi ") prefer 2 apply force
  apply (erule exE)
  apply simp
  apply (subgoal_tac "set rs2 \<subseteq> set rs \<union> {tleft} \<union> {tr} & rs2~=[]")
  prefer 2
   (*set rs2 \<subseteq> set rs \<union> {tleft} \<union> {tr} & rs2 ~= []*)
   apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:wellformed_tree_def wellformed_context_1_def subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
   apply (subgoal_tac "rs2 ~= []") prefer 2 apply (force simp add:list_replace_at_n_def split_at_def rev_apply_def)
   apply (subgoal_tac "set rs2 \<subseteq> set rs \<union> {tleft} \<union> {tr}") 
   prefer 2
    apply (drule_tac t=rs2 in sym)
    apply (simp add:list_replace_at_n_def split_at_def rev_apply_def)
    apply rule
    (*set (take i rs) \<subseteq> insert tr (insert tleft (set rs))*)
    apply (meson insertCI set_take_subset subsetCE subsetI)
  
    (*set (tl (drop i rs)) \<subseteq> insert tr (insert tleft (set rs))*)
    apply (metis Cons_nth_drop_Suc in_set_dropD insert_iff list.sel(3) subsetI)
   apply force
  apply (subgoal_tac "height ` set rs2 = {hrsi}")
  prefer 2  
   apply (subgoal_tac "height ` set rs2 \<subseteq> height ` (set rs \<union> {tleft} \<union> {tr})") prefer 2 apply blast
   apply (subgoal_tac "height ` (set rs) = {hrsi}")
   prefer 2
    apply (simp add:wellformed_context_1_def wellformed_tree_def balanced_def Let_def forall_subtrees_Cons balanced_1_def list_all_iff)
    apply (subgoal_tac "set rs ~= {} ") prefer 2 apply (force simp add:subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
    apply (erule conjE)+
    apply (simp (no_asm) add:image_def)
    apply clarify
    apply (subgoal_tac "(case rs ! 0 of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1) = (case tleft of Node (xa, cs) => 1 + Max (set (map height cs)) | Leaf x => 1)")
    prefer 2 
     apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
    apply force
   apply (smt Collect_cong length_greater_0_conv nth_mem singleton_conv)
    
   apply simp
   apply (subgoal_tac "height ` set rs2 = {} | height ` set rs2 = {hrsi}") prefer 2 apply (metis subset_singletonD)
   apply force
  apply (subgoal_tac "height ` set left_rs \<subseteq> height ` set rs2 ") prefer 2 apply blast
  apply (subgoal_tac "height ` set right_rs \<subseteq> height ` set rs2") prefer 2 apply blast
  apply simp
  (*heights*)
  apply (subgoal_tac "height ` set left_rs = {hrsi} & height ` set right_rs = {hrsi} ") prefer 2
   apply (subgoal_tac "set right_rs ~= {}")
   prefer 2 (*this is for drop Suc min_node*)
    apply (drule_tac t="right_rs" in sym)
    apply (subgoal_tac "length rs2 = Suc (length ks2)")
    prefer 2
     apply (clarsimp)
     apply (simp add:rev_apply_def list_replace_at_n_def list_insert_at_n_def split_at_def)
     apply (subgoal_tac "i < length rs") prefer 2 apply (force simp add:wellformed_tree_def wellformed_context_1_def subtree_indexes_def wf_ks_rs_def Let_def forall_subtrees_Cons wf_ks_rs_1_def)
     apply (force simp add:Let_def min_def wellformed_context_1_def wellformed_tree_def wf_ks_rs_def forall_subtrees_Cons wf_ks_rs_1_def)
    apply force
   apply (subgoal_tac "? hlrs. height ` set left_rs = hlrs") prefer 2 apply force
   apply (subgoal_tac "? hrrs. height ` set right_rs = hrrs") prefer 2 apply force
   apply (erule exE)+
   apply simp
   apply rule
    (*hlrs = {hrsi}*)
    apply (subgoal_tac "hlrs = {} | hlrs = {hrsi}") prefer 2 apply (metis subset_singletonD)
    apply (subgoal_tac "hlrs ~= {}") prefer 2 apply (force)
    apply force
     
    (*hrrs = {hrsi}*)
    apply (subgoal_tac "hrrs = {} | hrrs = {hrsi}") prefer 2 apply (metis subset_singletonD)
    apply (subgoal_tac "hrrs ~= {}") prefer 2 apply (force)
    apply force    
  apply simp
  (*check_keys*)
  (* I need to show that k is in ks2 and that the check_keys on ks2 considers all the check_keys predicates in the goal*)
  apply (simp add:wellformed_focus_def check_keys_def)
  apply rule+
   (*(case lb of None => True | Some kl => Ball (set (keys (Node (left_ks, left_rs)))) (key_le kl))*)
   apply (case_tac lb) apply force apply force
   
  (*(case rb of None => True | Some kr => !k : set (keys (Node (right_ks, right_rs))). key_lt k kr)*)
  apply rule+
   apply (case_tac rb) apply force apply force
   
  (*(case lb of None => True | Some kl => Ball (set [k]) (key_le kl))*)
  apply rule+
   apply (case_tac lb) apply force apply (force simp add:keys_Cons)

  (*case rb of None => True | Some kr => !k : set [k]. key_lt k kr*)
  apply (case_tac rb) apply force apply (force simp add:keys_Cons)
done

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

(*FIXME move in Key_lt_order*)
lemma key_lt_eq: "! a b c. total_order_key_lte --> key_lt b a --> key_eq a c | key_eq c a --> key_lt b c"
apply (unfold total_order_key_lte_def key_eq_def key_le_def)
apply rule+
apply simp
apply meson
done
(*FIXME move in Key_lt_order*)
lemma key_lt_rev: "! a b . total_order_key_lte --> ~ (key_lt a b) --> ~( key_eq a b) | ~ (key_eq b a) --> key_lt b a"
apply (unfold total_order_key_lte_def key_eq_def key_le_def)
apply rule+
apply force
done

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
   apply (subgoal_tac "case stk of (lb,((ks,rs),i),rb)#_ =>  let (l,u) = get_lower_upper_keys_for_node_t ks lb i rb in check_keys l [k0] u | _ => True")
   prefer 2
    apply (case_tac stk,force)
    apply (rename_tac hd_stk stk')
    apply simp
    apply (case_tac hd_stk,simp,case_tac b,simp,case_tac aa,simp)
    apply (case_tac stk')
    (*FIXME each of the following generates many cases: we want to summarize them as much as we can*)
     (*stk' = []*)
     apply (simp add:get_lower_upper_keys_for_node_t_def)
     apply clarsimp
     apply (simp add: check_keys_def)
     apply (force intro:FIXME)
     (*stk' ~= []*)
     apply (force intro:FIXME)
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
 apply (insert invariant_wf_ts)
 apply (simp add:invariant_wf_ts_def)
 apply force
done

end