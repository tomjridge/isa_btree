theory Andrea_proof
imports Insert_tree_stack
begin

definition invariant_wf_ts :: "bool" where
"invariant_wf_ts == (
! ts.
wellformed_ts ts \<longrightarrow> 
(
let ts' = step_tree_stack ts in
case ts' of 
None \<Rightarrow> True
| Some ts' \<Rightarrow> (
wellformed_ts ts'
)
))
"

lemma forall_subtrees_Cons: "forall_subtrees P t = 
(case t of 
 Node(l,cs) \<Rightarrow> 
  (P t & 
  List.list_all (forall_subtrees P) cs)
 | Leaf l \<Rightarrow> P t)"
apply (simp add: forall_subtrees_def rev_apply_def)
apply (case_tac t)
 apply (simp,case_tac x1,simp add:rev_apply_def)
 apply (simp add:forall_subtrees_def rev_apply_def list_all_iff)

 apply force
done

definition wf_size' :: "rmbs_t \<Rightarrow> Tree \<Rightarrow> bool" where
"wf_size' rmbs t0 == (
case rmbs of
Rmbs False \<Rightarrow> (
case t0 of 
Leaf(l) \<Rightarrow> (length l \<le> Constants.max_leaf_size)
| Node(l,cs) \<Rightarrow> (
1 \<le> length l
& List.list_all (forall_subtrees wf_size_1) cs)
)
| Rmbs True \<Rightarrow> (
case t0 of 
Leaf(l) \<Rightarrow> (length l \<le> Constants.max_leaf_size)
| Node(l,cs) \<Rightarrow> (
1 \<le> length l
& List.list_all (forall_subtrees wf_size_1) cs)
))"

lemma wf_size_implies_wf_size': "wf_size r t \<Longrightarrow> wf_size' r t"
apply (simp add:wf_size'_def wf_size_def)
apply (case_tac r)
 apply (simp,case_tac x,simp,case_tac t, simp,case_tac x1,simp)
 apply (force simp add: Let_def list_all_length)+

 apply (simp,case_tac x,simp,case_tac t, simp,case_tac x1,simp)
 apply (force simp add: Let_def wf_size_1_def forall_subtrees_Cons list_all_length)+
done

definition wellformed_tree' :: "rmbs_t \<Rightarrow> Tree \<Rightarrow> bool" where
"wellformed_tree' rmbs t0 == (
let b1 = wf_size' rmbs t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"

lemma wf_tree_implies_wf_tree': "wellformed_tree rmbs t \<Longrightarrow> wellformed_tree' rmbs t"
apply (simp add:wellformed_tree_def wellformed_tree'_def wf_size_implies_wf_size')
done

lemma fst_snd_simps: "((a,b)|>fst = a) & ((a,b)|>snd = b)"
apply(simp add:rev_apply_def)
done
  
lemma wellformed_context_hereditary: "wellformed_context (x#xs) \<Longrightarrow> wellformed_context xs"
apply (case_tac xs)
 apply (force simp add:wellformed_context_def)+
done

lemma wellformed_context_i_less_than_length_rs:
"wellformed_context (((ks, rs), i) # stk) \<Longrightarrow> i \<le> length ks \<and> i < length rs"
apply (induct stk)
 apply (simp add:wellformed_context_def)
 apply (simp add:wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def subtree_indexes_def)

 apply (simp add:wellformed_context_def)
 apply (case_tac "stk =[]")
  (*stk = []*)
  apply (case_tac a, case_tac aa)
  apply (simp add:wellformed_context_1_def)
  apply (simp add:wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def subtree_indexes_def)

  (*stk = aa#list*)
  apply (case_tac "last stk")
  apply simp
done

lemma wf_size_ks_not_empty: "wf_size rmbs (Node(ks,rs)) \<longrightarrow> 1\<le>length ks"
apply (simp add:wf_size_def)
apply (case_tac "rmbs")
 apply (case_tac x)
  apply (force simp add:Let_def)

  apply (force simp add:forall_subtrees_def rev_apply_def wf_size_1_def Let_def)
done

lemma wf_size_ks_not_empty': "wf_size (Rmbs (stk = [])) (Node(ks,rs)) \<Longrightarrow> 1\<le>length ks"
apply (insert wf_size_ks_not_empty,force)
done

lemma set_butlast_lessThan:"set (butlast [0..<n]) = {0..<n -1}"
apply (case_tac n,force+)
done

lemma list_all_update: "list_all P l \<Longrightarrow> P a \<Longrightarrow> list_all P (l[i := a]) "
by (metis length_list_update list_all_length nth_list_update_eq nth_list_update_neq) 

lemma list_all_update_concat_map_subtrees: 
"list_all P (concat (map tree_to_subtrees rs)) \<Longrightarrow> list_all P (tree_to_subtrees t) \<Longrightarrow>
list_all P (concat (map tree_to_subtrees (rs[i := t])))"
by (smt concat.simps(2) concat_append id_take_nth_drop list.map(2) list_all_append list_update_beyond map_append not_le upd_conv_take_nth_drop)

lemma list_all_take_drop_less_one_element: 
"list_all P xs \<Longrightarrow> (list_all P (take (i- Suc 0) xs)) \<and> (list_all P (drop i xs))"
by (metis append_take_drop_id list_all_append)

lemma list_all_of_list_replace_at_n:
"i < length rs \<Longrightarrow>
 list_replace_at_n rs i [tleft, tright] |> dest_Some = rs2 \<Longrightarrow>
 P tleft \<Longrightarrow>
 P tright \<Longrightarrow>
 list_all P rs \<Longrightarrow> list_all P rs2"
apply (simp_all add:list_replace_at_n_def rev_apply_def split_at_def)
apply (drule_tac t="rs2" in sym)
 apply (case_tac "i=0")
 (*i=0*)
 apply (case_tac rs,simp+)

 (*i\<noteq>0*)
 apply (metis append_take_drop_id drop_eq_Nil list.collapse list.pred_inject(2) list_all_append not_le)
done

lemma list_all_take_drop_less_one_element_concat_map_subtrees:
"list_all P (concat (map tree_to_subtrees xs)) \<Longrightarrow> 
(list_all P (concat (map tree_to_subtrees (take i xs)))) 
\<and> (list_all P (concat (map tree_to_subtrees (tl (drop i  xs)))))"
by (metis append_take_drop_id concat_append drop_Suc list_all_append map_append tl_drop)


lemma list_all_of_list_replace_at_n_concat_map_subtrees:
"
i < length rs \<Longrightarrow>
dest_Some (list_replace_at_n rs i [tleft, tright]) = rs2 \<Longrightarrow>
list_all P (concat (map tree_to_subtrees rs)) \<Longrightarrow>
list_all P (tree_to_subtrees tleft) \<Longrightarrow>
list_all P (tree_to_subtrees tright) \<Longrightarrow>
list_all P (concat (map tree_to_subtrees rs2))
"
apply (simp_all add:list_replace_at_n_def rev_apply_def split_at_def)
apply (drule_tac t="rs2" in sym)
apply (case_tac "i=0")
 (*i=0*)
 apply (case_tac rs,force+)

 (*i\<noteq>0*)
 apply (force simp add:butlast_take list_all_take_drop_less_one_element_concat_map_subtrees)
done

lemma invariant_wf_ts: "invariant_wf_ts"
apply(simp add: invariant_wf_ts_def)
apply(intro allI impI)
apply(case_tac ts)
apply(case_tac x)
apply(rename_tac f stk)
apply(simp add: step_tree_stack_def dest_ts_def)
apply(case_tac stk) apply(force)
apply(rename_tac ni stk)
apply(case_tac ni)
apply(rename_tac n i)
apply(simp)
apply(thin_tac "ts = _")
apply(thin_tac "x = _")
apply(thin_tac "stka = _")
apply(thin_tac "ni = _")
apply(simp add: wellformed_ts_def)
apply(simp add: dest_ts_def)
apply(elim conjE)
apply(case_tac n)
apply(rename_tac ks rs)
apply(simp)
apply(subgoal_tac " wellformed_focus (update_focus_at_position (ks, rs) i f) (stk = []) \<and>
       wellformed_context stk")
prefer 2
(* begin subproof *)
apply(intro conjI)
 (* wf_focus *)
 apply(simp add: wellformed_focus_def )
 apply (subgoal_tac "i<length rs") prefer 2 apply (force simp add:wellformed_context_i_less_than_length_rs)
 apply(subgoal_tac "wellformed_tree (Rmbs (stk=[])) (Node (ks,rs))") (* A: given that the tree without update is wf, we just need to check that rs was wf (replacing an element will leave it as before)*)
  prefer 2
   apply(simp add: wellformed_context_def)
   apply (subgoal_tac "\<exists> ks' rs' i'. (if stk = [] then ((ks, rs), i) else last stk) = ((ks', rs'), i')")
   prefer 2
    apply force
   apply (elim exE)+
   apply simp
   apply (elim conjE)
   apply (case_tac stk)
    (*stk = [] *)
    apply simp
   
    (* stk \<noteq> [] *)
    apply simp
    apply (elim conjE)
    apply (simp add:wellformed_context_1_def)
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
    apply (force simp add:Let_def list_all_update)

    apply (simp add:Let_def forall_subtrees_def rev_apply_def wf_size_1_def list_all_iff)
    apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
    apply force
    
   (* wf_ks_rs (Node (ks, rs[i := t])) *)
   apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def list_all_iff)
   apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
   apply force

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
     apply (force simp:list_all_update_concat_map_subtrees)

    (* rs = [] *)
    apply (simp add:wellformed_ts_1_def)

   (* keys_consistent; but this follows from wf_ts *)
   apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def)
   apply (intro conjI)
    (* keys_consistent_1 (Node (ks, rs[i := t])) *)
    apply (elim conjE)
    apply (thin_tac "list_all keys_consistent_1 (concat (map tree_to_subtrees rs))")
    apply (thin_tac "list_all keys_consistent_1 (case t of Node (l, cs) \<Rightarrow> t # map tree_to_subtrees cs |> concat | Leaf x \<Rightarrow> [t])")
    apply (simp add:keys_consistent_1_def)
    apply (elim conjE)
    apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
    apply (subgoal_tac "1 < length rs")
    prefer 2
     apply (subgoal_tac "1 \<le> length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty')
     apply force
    apply (subgoal_tac "\<exists> ys x zs . (rs = ys@x#zs) \<and> (rs!i = x) \<and> (i = length ys)") prefer 2 using id_take_nth_drop apply fastforce 
    apply (erule exE)+
    apply (erule conjE)+
    apply (intro conjI)
     (* R!i \<sqsubseteq> ks!i  - \<forall>ia\<in>set (key_indexes (Node (ks, rs[i := t]))). check_keys None (keys (rs[i := t] ! ia)) (Some (ks ! ia))*)
     apply (simp add:nth_append)
     apply (rule)
     apply (rename_tac i')
     apply (case_tac "i' < length ys")
      (*ia < length ys*)
      apply (subgoal_tac "i' \<in> set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
      apply force

      (*i' \<ge> length ys*)
      apply simp
      apply (case_tac "i' = length ys")
       (* i' = i *)
       apply (simp add:wellformed_ts_1_def dest_ts_def check_keys_def)

       (*i' > length ys*)
       apply (subgoal_tac "i' \<in> set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
       apply force
       
     (* k!i \<sqsubset> R!i+1 - \<forall>ia\<in>set (key_indexes (Node (ks, rs[i := t]))). check_keys (Some (ks ! ia)) (keys (rs[i := t] ! Suc ia)) None*)
     apply (simp add:nth_append)
     apply (rule)
     apply (rename_tac i')
     apply (case_tac "Suc i' < length ys")
      (*Suc i' < length ys*)
      apply (subgoal_tac "i' \<in> set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
      apply force

      (*Suc i' \<ge> length ys*)
      apply simp
      apply (case_tac "Suc i' = length ys")
       (* Suc i' = i *)
       apply (simp add:wellformed_ts_1_def dest_ts_def check_keys_def)
       apply (case_tac ys, force, force)
       
       (*i' > length ys*)
       apply (subgoal_tac "i' \<in> set (key_indexes (Node (ks, ys @ x # zs)))") prefer 2 apply (force simp add:key_indexes_def)
       apply force
    
    (* list_all keys_consistent_1 (concat (map tree_to_subtrees (rs[i := t]))) *)
    apply (subgoal_tac "list_all keys_consistent_1 (tree_to_subtrees t)") prefer 2 apply force
    apply (force simp:list_all_update_concat_map_subtrees)

   (* keys ordered *)
   apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def list_all_iff key_indexes_def)
   apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
   apply force

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
     apply (subgoal_tac "wf_size_1 tleft \<and> wf_size_1 tright") 
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
    apply (subgoal_tac "height tright = height (rs!0) \<and> height tleft = height (rs!0)") prefer 2 apply (simp add:wellformed_ts_1_def dest_ts_def Let_def del:height.simps) apply (force intro:FIXME)
    apply (subgoal_tac "height (rs2!0) = height (rs!0)")
    prefer 2 
     apply (simp add:list_replace_at_n_def rev_apply_def split_at_def del:height.simps)
     apply (case_tac "i=0")
      (* i = 0 *)
      apply force

      (* i \<noteq> 0 *)
      apply (simp add: del:height.simps)
      apply (metis append_take_drop_id length_greater_0_conv list.size(3) nth_append nth_append_length)
      
    apply (case_tac "rs2 = []", simp)
    apply (force simp add: list_all_of_list_replace_at_n)

    (* keys_consistent (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:keys_consistent_1_def check_keys_def)
    (*so I know already that between tleft k0 tright there is consistency,
      while I know that there is consistency ks!i and tleft and ks!i+1 and tright by wellformed_ts_1

      I need to divide in bits this goal! !
    *)
    apply (simp add:list_replace_at_n_def split_at_def)
    apply (case_tac "rs = []") apply force
    (*rs \<noteq> [] *)
    apply (subgoal_tac "\<exists> xs ys. (ks2 = xs@k0#ys) \<and> (ks = xs @ ys) \<and> (i = length xs)")
    prefer 2
     apply (simp add:list_insert_at_n_def split_at_def)
     using wellformed_context_i_less_than_length_rs apply fastforce
    apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
    apply (subgoal_tac "1 < length rs")
    prefer 2
     apply (subgoal_tac "1 \<le> length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty')
     apply force
    apply (erule exE)+
    apply (erule conjE)+
    apply simp
    apply rule
     (* key_lt --\<forall>i\<in>set (key_indexes (Node (xs @ k0 # ys, rs2))). \<forall>k\<in>set (keys (rs2 ! i)). key_lt k ((xs @ k0 # ys) ! i)*)
     apply rule+
     apply (rename_tac i' k)
     apply (case_tac "i' < i") (* this assumption tells me that i < 0, because 0 < 0 is False*)
      (*i' < i*)
      (*i' can be only elements that were already in rs before,
      since this key_lt uses only i', the following hypothesis is enough
      \<forall>i\<in>set (key_indexes (Node (xs @ ys, rs))). \<forall>k\<in>set (keys (rs ! i)). key_lt k ((xs @ ys) ! i)
      *)
      apply (subgoal_tac "xs \<noteq> []") prefer 2 apply force
      apply simp
      apply (drule_tac t=rs2 in sym)
      apply (simp add:nth_append key_indexes_def)    
      apply (subgoal_tac "{0..<length xs} \<subset> {0..<length rs}") prefer 2 apply (force)
      apply force

      (* i' \<ge> i *)
      apply (case_tac "i' = i")
       (*i' = i*) (* here  i may be equal to 0*)
       apply (subgoal_tac "i' = length xs") prefer 2 apply force
       apply (drule_tac t=rs2 in sym)
       apply (force simp add:nth_append key_indexes_def)
       
       (*i' > i*) (* here  i may be equal to 0*)
       apply simp
       apply (drule_tac t=rs2 in sym)
       apply simp
       (*if i' = Suc i, we are in tright*)
       apply (case_tac "i' = Suc i")
        (*i' = Suc i, we are in tright*)
        apply (subgoal_tac "length ys \<noteq> 0") prefer 2 apply (force simp add:key_indexes_def)
        apply (simp add: Let_def wellformed_ts_1_def dest_ts_def check_keys_def del:height.simps)
        apply (force simp add:nth_append)
        
        (*i' \<noteq> Suc i*)
        apply (subgoal_tac "Suc (length xs)<i'") prefer 2 apply force
        apply (simp add:key_indexes_def)
        apply (case_tac "length ys =0") apply force
        apply (subgoal_tac "{Suc (length xs)..< length rs -1} \<subset> {0..<length rs -1}") prefer 2 apply force
        apply (subgoal_tac "(tl (drop (length xs) rs)) = (drop (length xs +1) rs)") prefer 2 apply (force simp add:drop_Suc drop_tl)
        apply (simp add:nth_append min_def)
        apply (smt One_nat_def Suc_lessE add_2_eq_Suc atLeastLessThan_iff diff_Suc_1 diff_Suc_eq_diff_pred le_add_diff_inverse less_2_cases less_Suc0 less_imp_le_nat not_le old.nat.distinct(2))
     
     (*key_le --\<forall>i\<in>set (key_indexes (Node (xs @ k0 # ys, rs2))). \<forall>x\<in>set (keys (rs2 ! Suc i)). key_le ((xs @ k0 # ys) ! i) x*)
     apply rule+
     apply (rename_tac i' k)
     apply (case_tac "Suc i' < i") (* this assumption tells me that i < 0, because 0 < 0 is False*)
      (*Suc i' < i*)
      (*i' can be only elements that were already in rs before,
      since this key_lt uses only i', the following hypothesis is enough
      \<forall>i\<in>set (key_indexes (Node (xs @ ys, rs))). \<forall>k\<in>set (keys (rs ! i)). key_lt k ((xs @ ys) ! i)
      *)
      apply (subgoal_tac "xs \<noteq> []") prefer 2 apply force
      apply simp
      apply (drule_tac t=rs2 in sym)
      apply (simp add:nth_append key_indexes_def)    
      apply (subgoal_tac "{0..<length xs} \<subset> {0..<length rs}") prefer 2 apply force
      apply force

      (* Suc i' \<ge> i *)
      apply (case_tac "Suc i' = i")
       (*i' = i*) (* here  i may be equal to 0*)
       apply (subgoal_tac "Suc i' = length xs") prefer 2 apply force
       apply (drule_tac t=rs2 in sym)
       apply (simp add:wellformed_ts_1_def dest_ts_def Let_def check_keys_def del:height.simps)
       apply (subgoal_tac "xs \<noteq> []") prefer 2 apply force
       apply (simp add:nth_append key_indexes_def)
       apply (metis One_nat_def diff_Suc_1)
       
       (*Suc i' > i*) (* here  i may be equal to 0*)
       apply simp
       apply (drule_tac t=rs2 in sym)
       apply simp
       (*if Suc i' = Suc i, we are in tright*)
       apply (case_tac "Suc i' = Suc i")
        (*Suc i' = Suc i, we are in tright*)
        apply (simp add: Let_def wellformed_ts_1_def dest_ts_def check_keys_def del:height.simps)
        apply (force simp add:nth_append)
        
        (*Suc i' \<noteq> Suc i*)
        apply (subgoal_tac "Suc (length xs) < Suc i'") prefer 2 apply force
        apply (subgoal_tac "Suc i' \<le> length rs") prefer 2 apply (force simp add:key_indexes_def)
        apply (simp add:key_indexes_def)
        apply (case_tac "length ys =0") apply force
        apply (subgoal_tac "(tl (drop (length xs) rs)) = (drop (length xs +1) rs)") prefer 2 apply (force simp add:drop_Suc drop_tl)
        apply (simp add:nth_append min_def)
        apply (subgoal_tac "length rs = 1+length xs + length ys") prefer 2 apply force
        apply (thin_tac " length xs + length ys = length rs - Suc 0")
        apply simp
        apply (case_tac "length ys") apply force
        apply (subgoal_tac "\<exists> x. i' = x+(Suc(length xs))") prefer 2 apply (metis Suc_leI le_add_diff_inverse2)
        apply (erule exE)
        apply force

    (* keys_ordered (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (drule_tac t="fat_node" in sym)
    apply (thin_tac "length ks2 = Suc (length ks)")
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees keys_ordered_1_def)
    apply (subgoal_tac "1 \<le> length ks") prefer 2 apply (blast intro:wf_size_ks_not_empty')
    apply (subgoal_tac "\<exists> xs ys. (ks2 = xs@k0#ys) \<and> (ks = xs @ ys) \<and> (i = length xs)")
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
     apply (subgoal_tac "i' \<in> set (butlast (key_indexes (Node (xs @ ys, rs))))") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)
     apply (case_tac "Suc i' < length xs - Suc 0")
      (*Suc i' < length xs - Suc 0*)
      apply (subgoal_tac "Suc i' \<in> set (butlast (key_indexes (Node (xs @ ys, rs))))")
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
      apply (subgoal_tac "i' < length xs") prefer 2 apply force
      apply (simp add:wellformed_ts_1_def dest_ts_def Let_def check_keys_def)
      apply (subgoal_tac "xs \<noteq> []") prefer 2 apply force
      apply (simp add:nth_append)
      (*FIXME the assumption key_lt (xs ! i') k0 should be in wellformed_ts_1: is it?*)
      apply (force intro:FIXME)

      (*Suc i' \<noteq> length xs*)
      apply (subgoal_tac "length xs < Suc i'") prefer 2 apply force
      apply (subgoal_tac "Suc i' \<in> set (key_indexes (Node (xs @ k0 # ys, rs2)))") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)  
      apply (case_tac "i' = length xs")
       (* i' = length xs *)
       apply (simp add:wellformed_ts_1_def dest_ts_def Let_def check_keys_def)
       apply (force simp add:nth_append)

       (* length xs < i' *)
       apply (subgoal_tac "length xs < i'") prefer 2 apply force
       apply (case_tac i') apply force
       apply (rename_tac i'')
       apply (subgoal_tac "2 \<le> length ys") prefer 2 apply (case_tac "length ys < 2", force simp add:key_indexes_def) apply force
       apply simp
       (*we take only the subset we are interested in*)
       apply (subgoal_tac "\<forall> i \<in> {length xs ..<length xs + length ys - 1}.  key_lt ((xs @ ys) ! i) ((xs @ ys) ! Suc i)") prefer 2 apply (force simp add:key_indexes_def set_butlast_lessThan)
       apply (case_tac "i' \<le> length xs + length ys - 1")
        (*i' \<le> length xs + length ys - 1*)
        apply (force simp add:nth_append)
         
        (*i' > length xs + length ys - 1 -- this case should be false because Suc i' would not belong to {..<Suc(length xs+length ys)}*)
        apply (force simp add:key_indexes_def set_butlast_lessThan)
  (* okay we know stuff about the fat node*)
  apply (subgoal_tac "length ks2 = Suc (length ks)") prefer 2 apply (force simp add:list_insert_at_n_def split_at_def)
  apply(case_tac "length ks2 \<le> max_node_keys")
   (*length ks2 \<le> max_node_keys -- inserting_two \<rightarrow> inserting_one*)
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
   apply (case_tac "case drop min_node_keys ks2 of x # xa \<Rightarrow> (x, xa)")
   apply (rename_tac "k" "right_ks")
   apply (subgoal_tac "\<exists> left_ks. take min_node_keys ks2 = left_ks") prefer 2 apply force
   apply (subgoal_tac "\<exists> right_rs. drop (Suc min_node_keys) rs2 = right_rs") prefer 2 apply force
   apply (subgoal_tac "\<exists> left_rs. take (Suc min_node_keys) rs2 = left_rs") prefer 2 apply force
   apply (erule exE)+
   apply (subgoal_tac "((set right_rs) \<subseteq> set rs2) \<and> ((set left_rs) \<subseteq> set rs2)") prefer 2 apply (simp add:list_replace_at_n_def split_at_def rev_apply_def) apply (meson  set_drop_subset set_take_subset)
   apply simp 
   (*wellformed_tree (Rmbs False) (Node (left_ks, left_rs))*)
   apply (simp add:wellformed_tree_def wellformed_tree'_def)
   apply (drule_tac t="fat_node" in sym)
   (*wf_size*)
   apply (subgoal_tac "wf_size (Rmbs False) (Node (left_ks, left_rs)) \<and> wf_size (Rmbs False) (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:wf_size'_def wf_size_def)
    apply (simp add:list_all_iff forall_subtrees_def rev_apply_def)
    (*FIXME I remember there could be a def problem in solving the followings *)
    apply (subgoal_tac "wf_size_1 (Node (left_ks, left_rs))") prefer 2 apply (force intro:FIXME)
    apply (subgoal_tac "wf_size_1 (Node (right_ks, right_rs))") prefer 2 apply (force intro:FIXME)
    apply blast
   (*wf_ks_rs*)
   apply (subgoal_tac "wf_ks_rs (Node (left_ks, left_rs)) \<and> wf_ks_rs (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "wf_ks_rs_1 (Node (left_ks, left_rs)) \<and> wf_ks_rs_1 (Node (right_ks, right_rs))") prefer 2 apply (force intro:FIXME)
    apply blast
   (*balanced*)
   apply (subgoal_tac "balanced (Node (left_ks, left_rs)) \<and> balanced (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:balanced_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "balanced_1 (Node (left_ks, left_rs)) \<and> balanced_1 (Node (right_ks, right_rs))") prefer 2 apply (force intro:FIXME)
    apply blast
   (*keys_consistent*)
   apply (subgoal_tac "keys_consistent (Node (left_ks, left_rs)) \<and> keys_consistent (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:keys_consistent_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "keys_consistent_1 (Node (left_ks, left_rs)) \<and> keys_consistent_1 (Node (right_ks, right_rs))") prefer 2 apply (force intro:FIXME)
    apply blast
   (*keys_ordered*)
   apply (subgoal_tac "keys_ordered  (Node (left_ks, left_rs)) \<and> keys_ordered  (Node (right_ks, right_rs))")
   prefer 2
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def list_all_iff)
    apply (subgoal_tac "keys_ordered_1 (Node (left_ks, left_rs)) \<and> keys_ordered_1 (Node (right_ks, right_rs))") prefer 2 apply (force intro:FIXME)
    apply blast
   apply simp
   (*check_keys None (keys (Node (left_ks, left_rs))) (Some k)*)
   (*FIXME: cannot we solve this by proofing that check_keys is valid on fat_node?*)
   apply (simp add:check_keys_def)
   (* I want to show that if ks=l_ks@r_ks and rs=l_rs@r_rs 
   then keys(left_ks,left_rs) = insert k0 (keys (l_ks,l_rs))
   and if k=k0, I need to know that 
   \<forall> ka \<in> (keys(left_ks,left_rs)). key_lt ka k0
   but do I know that key_lt any_left_ks k0?
   The only hypothesis we get is from wellformed_ts_1 and that tells about single keys.
   Probably we need to change the definitions...
   *)
   
   (*check_keys (Some k) (keys (Node (right_ks, right_rs))) None*)
   apply (force intro:FIXME)
 (* wf_context *)
 apply(force intro: wellformed_context_hereditary)
(* end subproof *)
apply(elim conjE)

apply(simp)
(* wf_ts_1 *)
apply(simp add: update_focus_at_position_def)
apply(case_tac f)
 (* i1 *)
 apply(simp)
 apply(force intro: FIXME)

  (* i2 FIXME may be worth combining with other i2 cases? *)
 apply(simp)
 apply(subgoal_tac "? tleft k0 tr. x2 = (tleft,k0,tr)") prefer 2 apply(force)
 apply(elim exE)
 apply(simp)
 apply(subgoal_tac "? ks2. list_insert_at_n (n |> fst) i [k0]  = ks2") prefer 2 apply(force)
 apply(subgoal_tac "? rs2. list_replace_at_n (n |> snd) i [tleft, tr] |> dest_Some = rs2") prefer 2 apply(force)
 apply(elim exE)
 apply(simp add: Let_def fst_snd_simps)

 apply(force intro: FIXME)
done


end