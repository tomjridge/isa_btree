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

lemma list_all_update: "list_all P l \<Longrightarrow> P a \<Longrightarrow> list_all P (l[i := a]) "
by (metis length_list_update list_all_length nth_list_update_eq nth_list_update_neq) 

lemma list_all_update_concat_map_subtrees: 
"list_all P (concat (map tree_to_subtrees rs)) \<Longrightarrow> list_all P (tree_to_subtrees t) \<Longrightarrow>
list_all P (concat (map tree_to_subtrees (rs[i := t])))"
by (smt concat.simps(2) concat_append id_take_nth_drop list.map(2) list_all_append list_update_beyond map_append not_le upd_conv_take_nth_drop)


lemma list_all_concat_map_tree_subtrees:
"(list_all P (concat (map tree_to_subtrees rs))) =               
 (list_all P rs \<and> list_all P (concat (map (\<lambda> t. case t of Node(l,cs) \<Rightarrow> (List.map tree_to_subtrees cs) |> List.concat | Leaf _ \<Rightarrow> []) rs)))"
apply (induct rs)
 apply simp

 apply (case_tac a)
  apply simp
  apply (case_tac x1)
   apply force

  apply force
done

lemma wf_size_hereditary: "wf_size (Rmbs b) (Node(ks,x#xs)) \<Longrightarrow> wf_size (Rmbs b) (Node (ks,xs))"
apply (simp add:wf_size_def)
apply (case_tac b)
  apply simp

  apply (simp add:forall_subtrees_def rev_apply_def wf_size_1_def)
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
 apply(case_tac f)
  (* inserting_one *) (*A: this case is easier, because the stepped focus can be only insert_one *)
  apply(rename_tac t)
  apply(simp)
  apply(simp add: update_focus_at_position_def)
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

  apply(simp add: wellformed_tree_def)
  apply(elim conjE)
  apply (simp add:list_replace_1_at_n_def dest_Some_def)
(*  apply (subgoal_tac "\<exists> x. rs!i = x") prefer 2 apply force
  apply (erule exE)
  apply (subgoal_tac "\<exists> rs1 rs2. (rs  = rs1@x#rs2)")
  prefer 2
   apply (case_tac "rs = []")
    apply (force intro:FIXME)

    apply (case_tac "i < length rs")
     
     apply (blast intro:id_take_nth_drop)

     apply (force intro:FIXME)
  apply (elim exE)+
  apply (subgoal_tac "(rs [i:=t ] = rs1@t#rs2)")
  prefer 2
   apply (subgoal_tac "length rs = length (rs1 @ x # rs2)") prefer 2 apply force
   apply (subgoal_tac "i = length rs1 ")
   prefer 2
    apply meson
    apply (subgoal_tac "(length rs) = (length (rs1@(rs!i)#rs2))") prefer 2 apply force
    apply (force intro:FIXME)
      
   apply simp
*)   
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
    apply (subgoal_tac "i < length rs \<and> (height (rs!i) = height t) ") 
    prefer 2
     apply (intro conjI)
      (* i < length rs *)
      apply (simp add:wellformed_context_def)
      apply (case_tac stk)
       apply (simp add:wf_ks_rs_def forall_subtrees_def rev_apply_def wf_ks_rs_1_def)
     
       apply (force intro:FIXME) (* I need to induct to solve this *)

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
     apply (subgoal_tac "i \<le> length ks") prefer 2 apply (force intro:FIXME)
     apply (subgoal_tac "length ks  = length rs - 1") prefer 2 apply (force intro:FIXME)
     apply simp
     apply (case_tac "i \<le> length rs - Suc (Suc 0)")
      apply (subgoal_tac 
       "(\<forall>ia\<in>{0..length rs - Suc (Suc 0)}. \<forall>x\<in>set (keys (rs[i := t] ! ia)). key_le (ks ! ia) x) =
       ((\<forall>i\<in>{0.. i - 1}. \<forall>k\<in>set (keys (rs ! i)). key_le (ks ! i) k) 
       \<and> ((i \<le> length rs - Suc (Suc 0)) \<longrightarrow> (\<forall>k\<in>set (keys (rs[i := t] ! i)). key_le (ks ! i) k)) 
       \<and> (\<forall>i\<in>{i+1.. length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs ! i)). key_le (ks ! i) k))
       ") prefer 2 apply simp apply (metis atLeastAtMost_iff le0 nth_list_update_neq)
      apply (subgoal_tac "
        (\<forall>ia\<in>{0..length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs[i := t]!ia)). key_lt k (ks ! (Suc ia))) =
        ((\<forall>i\<in>{0.. i - 1}. \<forall>k\<in>set (keys (rs ! i)). key_lt k (ks ! Suc i)) 
       \<and> ((i \<le> length rs - Suc (Suc 0)) \<longrightarrow> (\<forall>k\<in>set (keys (rs[i := t] ! i)). key_lt k (ks ! Suc i))) 
       \<and> (\<forall>i\<in>{i+1.. length rs - Suc (Suc 0)}. \<forall>k\<in>set (keys (rs ! i)). key_lt k (ks ! Suc i)))
        ") prefer 2 apply simp apply (metis atLeastAtMost_iff le0 nth_list_update_neq) 
      apply (simp add:wellformed_ts_1_def dest_ts_def check_keys_def)
      apply (case_tac i)
       apply (case_tac rs, force, force)

       apply force
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
  apply(rename_tac tleft k0 tr)
  apply(simp add: update_focus_at_position_def)
  apply(elim conjE)
  apply(thin_tac "x2 = _")
  apply(subgoal_tac "? ks2.  list_insert_at_n (n |> fst) i [k0] = ks2") prefer 2 apply(force)
  apply(subgoal_tac "? rs2. list_replace_at_n (n |> snd) i [tleft, tr] |> dest_Some = rs2") prefer 2 apply(force)
  apply(elim exE)
  apply(simp add: Let_def)
  apply(case_tac "length ks2 \<le> max_node_keys")
   apply(simp)
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