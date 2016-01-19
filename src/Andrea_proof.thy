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
 apply (simp add:wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)

 apply (simp add:wellformed_context_def)
 apply (case_tac "stk =[]")
  (*stk = []*)
  apply (case_tac a, case_tac aa)
  apply (simp add:wellformed_context_1_def)
  apply (simp add:wellformed_tree_def wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)

  (*stk = aa#list*)
  apply simp
  apply (case_tac "last stk")
  apply simp
  apply (case_tac aa)
  apply (simp add:wellformed_context_1_def)
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
 list_replace_at_n ((ks, rs) |> snd) i [tleft, tright] |> dest_Some = rs2 \<Longrightarrow>
 P tleft \<Longrightarrow>
 P tright \<Longrightarrow>
 list_all P rs \<Longrightarrow> list_all P rs2"
apply (simp_all add:list_replace_at_n_def rev_apply_def split_at_def)
apply (drule_tac t="rs2" in sym)
 apply (case_tac "i=0")
 (*i=0*)
 apply (case_tac rs,simp+)

 (*i\<noteq>0*)
 apply (simp add:butlast_take list_all_take_drop_less_one_element)
done


lemma list_all_take_drop_less_one_element_concat_map_subtrees:
"list_all P (concat (map tree_to_subtrees xs)) \<Longrightarrow> 
(list_all P (concat (map tree_to_subtrees (take (i- Suc 0) xs)))) 
\<and> (list_all P (concat (map tree_to_subtrees (drop i  xs))))"
by (metis append_take_drop_id concat_append list_all_append map_append)

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
  (*i=0*)
 apply (case_tac rs,simp+)

 (*i\<noteq>0*)
 apply (simp add:butlast_take list_all_take_drop_less_one_element_concat_map_subtrees)
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
    apply (simp add:list_all_update)

    apply (simp add:forall_subtrees_def rev_apply_def wf_size_1_def list_all_iff)
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
     (*\<forall>ia\<in>{0..length ks - Suc 0}. \<forall>k\<in>set (keys (rs[i := t] ! ia)). key_le k (ks ! ia)*)
     (* I need to know that 
      \<forall>k\<in>set(keys t). key_le k (ks!i)
      then I can divide the \<forall>ia on the ith index
      *)
     apply (subgoal_tac "i \<le> length ks") prefer 2 apply (simp add:wellformed_context_i_less_than_length_rs)
     apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
     apply simp
     apply (case_tac "i \<le> length rs - Suc (Suc 0)")
      apply (subgoal_tac 
       "(\<forall>ia\<in>{0..length rs - Suc (Suc 0)}. \<forall>x\<in>set (keys (rs[i := t] ! ia)). key_le (ks ! ia) x) =
       ((\<forall>i\<in>{0.. i - 1}. \<forall>k\<in>set (keys (rs ! i)). key_le (ks ! i) k) 
       \<and> ((i \<le> length rs - Suc (Suc 0)) \<longrightarrow> (\<forall>k\<in>set (keys (rs[i := t] ! i)). key_le (ks ! i) k)) 
       \<and> (\<forall>i\<in>{i+1.. length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs ! i)). key_le (ks ! i) k))
       ") prefer 2 apply (thin_tac "i < length rs") apply simp apply (metis atLeastAtMost_iff le0 nth_list_update_neq) 
      apply (subgoal_tac "
        (\<forall>ia\<in>{0..length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs[i := t]!ia)). key_lt k (ks ! (Suc ia))) =
        ((\<forall>i\<in>{0.. i - 1}. \<forall>k\<in>set (keys (rs ! i)). key_lt k (ks ! Suc i)) 
       \<and> ((i \<le> length rs - Suc (Suc 0)) \<longrightarrow> (\<forall>k\<in>set (keys (rs[i := t] ! i)). key_lt k (ks ! Suc i))) 
       \<and> (\<forall>i\<in>{i+1.. length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs ! i)). key_lt k (ks ! Suc i)))
        ") prefer 2 apply (thin_tac "i < length rs") apply simp apply (metis atLeastAtMost_iff le0 nth_list_update_neq) 
      apply (simp add:wellformed_ts_1_def dest_ts_def check_keys_def)
      apply (case_tac i)
       apply (case_tac rs, force, force)

       apply force

    (* list_all keys_consistent_1 (concat (map tree_to_subtrees (rs[i := t]))) *)
    apply (subgoal_tac "list_all keys_consistent_1 (tree_to_subtrees t)") prefer 2 apply force
    apply (force simp:list_all_update_concat_map_subtrees)

   (* keys ordered *)
   apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def keys_ordered_1_def list_all_iff)
   apply (subgoal_tac "set (rs[i := t]) \<subseteq> insert t (set rs)") prefer 2 apply (simp add: set_update_subset_insert)
   apply force

  (* inserting_two *)
  apply(simp)
  apply(case_tac x2)
  apply(rename_tac tleft k0 tright)
  apply(simp add: update_focus_at_position_def)
  apply(elim conjE)
  apply(thin_tac "x2 = _")
  apply(subgoal_tac "? ks2. list_insert_at_n (n |> fst) i [k0] = ks2") prefer 2 apply(force)
  apply(subgoal_tac "? rs2. list_replace_at_n (n |> snd) i [tleft, tright] |> dest_Some = rs2") prefer 2 apply(force)
  apply(elim exE)
  apply(simp add: Let_def)
  apply(case_tac "length ks2 \<le> max_node_keys")
   apply(simp)
   apply (simp add:wellformed_tree_def)
   apply(subgoal_tac "length ks2 = Suc (length ks)")
   prefer 2 apply (force simp add:list_insert_at_n_def rev_apply_def split_at_def)
   apply (intro conjI)
    (*wf_size (Rmbs (stk = [])) (Node (ks2, rs2)) *)
    apply (simp add:wf_size_def)
    apply (subgoal_tac "wf_size_1 tleft \<and> wf_size_1 tright") prefer 2 apply (force intro:FIXME)
    apply (elim conjE)+
    apply (case_tac "stk=[]")
     (* stk = []*)
     apply (simp add:list_all_of_list_replace_at_n)

     (* stk \<noteq> [] *)
     apply (simp add:forall_subtrees_def Let_def rev_apply_def wf_size_1_def)
     apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)
    
    (* wf_ks_rs (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def )
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:wf_ks_rs_1_def)
    apply (simp add:list_replace_at_n_def)
    apply (simp add:split_at_def)
    apply (case_tac "i=0",force,force simp add:butlast_take)

    (* balanced (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (simp add:balanced_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)  
    apply (simp add:balanced_1_def del:height.simps)
    apply (subgoal_tac "list_replace_at_n ((ks, rs) |> snd) i [tleft, tright] |> dest_Some = rs2") prefer 2 apply (force simp add:rev_apply_def)
    apply (subgoal_tac "height tright = height (rs!0) \<and> height tleft = height (rs!0)") prefer 2 apply (simp add:wellformed_ts_1_def dest_ts_def Let_def del:height.simps) apply (force intro:FIXME)
    apply (subgoal_tac "height (rs2!0) = height (rs!0)")
    prefer 2 
     apply (simp add:list_replace_at_n_def rev_apply_def split_at_def del:height.simps)
     apply (case_tac "i=0")
      (* i = 0 *)
      apply force

      (* i \<noteq> 0 *)
      apply (simp add:butlast_take del:height.simps)
      apply (case_tac "take (i - Suc 0) rs")
       apply force

       apply (metis append_Cons append_take_drop_id nth_Cons_0)
    apply (case_tac "rs2 = []", simp)
    apply (force simp add: list_all_of_list_replace_at_n)

    (* keys_consistent (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply(force intro: FIXME)

    (* keys_ordered (Node (ks2, take (i - Suc 0) rs @ tleft # tright # drop i rs)) *)
    apply (simp add:keys_ordered_def forall_subtrees_def rev_apply_def)
    apply (simp add:list_all_of_list_replace_at_n_concat_map_subtrees)
    apply (simp add:keys_ordered_1_def ordered_key_list_def)
    apply(force intro: FIXME)
   apply(simp)
   apply(simp add: split_node_def)
   apply(force intro: FIXME)
  

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