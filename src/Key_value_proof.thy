theory Key_value_proof
imports  "Key_value" 
begin

(* FIXME most of these lemmas should be unnecessary - they are all solvable with 1st order proof *)


(* FIXME might like to use strict total order with key_lt and aim to always eliminate key_le - better automation *)
definition total_order_key_lte :: " bool" where
"total_order_key_lte == (\<forall> a b c. 
   (key_le a b \<and> key_le b a \<longrightarrow> key_eq a b) \<and>
   (key_le a b \<and> key_le b c \<longrightarrow> key_le a c) \<and>
   (key_le a b \<or> key_le b a)
\<and> (a = b \<longrightarrow> (key_le a b)))" (* FIXME just use defn of key_le, with = *)

lemma neg_key_lt: "! a b. total_order_key_lte \<longrightarrow> (~ key_lt a b) = (key_le b a)"
apply rule+
apply (unfold total_order_key_lte_def)
apply (force simp add: key_eq_def key_le_def)+
done


lemma key_lt_not_key_le: "! a b. total_order_key_lte \<longrightarrow> (key_lt a b) = (~ key_le b a)"
apply (simp add: neg_key_lt)
using neg_key_lt apply blast
done

lemma eq_implies_key_le: "! a b. total_order_key_lte \<longrightarrow> ((a = b) \<longrightarrow> (key_le a b))"
apply rule+
apply (unfold total_order_key_lte_def)
apply meson
done

lemma key_le_implies_neq: "! a b. total_order_key_lte \<longrightarrow> (~(key_eq a b) \<longrightarrow> (a ~= b))"
apply rule+
apply (unfold total_order_key_lte_def)
apply meson
done

lemma key_lt_implies_neq: "! a b. total_order_key_lte \<longrightarrow> ((key_lt a b) \<longrightarrow> (a ~= b))"
apply (simp add:key_lt_not_key_le)
using eq_implies_key_le apply blast
done

lemma order_key_le_lt: "\<forall> a b c. total_order_key_lte \<longrightarrow> key_le a b \<and> key_lt b c \<longrightarrow> key_lt a c"
apply rule+
apply (unfold total_order_key_lte_def)
apply (meson key_eq_def key_le_def)
done

lemma order_key_lt_le: "\<forall> a b c. total_order_key_lte \<longrightarrow> key_le a b \<and> key_lt b c \<longrightarrow> key_le a c"
apply rule+
apply (unfold total_order_key_lte_def)
apply (meson key_eq_def key_le_def)
done

lemma order_key_le: "\<forall> a b c. total_order_key_lte \<longrightarrow> key_le a b \<and> key_le b c \<longrightarrow> key_le a c"
apply rule+
apply (unfold total_order_key_lte_def)
apply (drule_tac x=a in spec)
apply (drule_tac x=b in spec)
apply (drule_tac x=c in spec)
apply (simp add:key_le_def)
done

lemma order_key_lt: "\<forall> a b c. total_order_key_lte \<longrightarrow> key_lt a b \<and> key_lt b c \<longrightarrow> key_lt a c"
apply (simp add:total_order_key_lte_def key_le_def)
apply (meson key_eq_def key_le_def)
done

lemma key_lt_eq: "! a b c. total_order_key_lte --> key_lt b a --> key_eq a c | key_eq c a --> key_lt b c"
apply (unfold total_order_key_lte_def key_eq_def key_le_def)
apply rule+
apply simp
apply meson
done

lemma key_lt_rev: "! a b . total_order_key_lte --> ~ (key_lt a b) --> ~( key_eq a b) | ~ (key_eq b a) --> key_lt b a"
apply (unfold total_order_key_lte_def key_eq_def key_le_def)
apply rule+
apply force
done


lemma hd_smallest_in_list_sorted_by_key_lt: 
"total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow>
i < ((length l) - Suc 0) \<Longrightarrow> key_lt (l ! 0) (l ! Suc i)"
apply (induct i)
  apply force

  apply simp
  apply (subgoal_tac "key_lt (l ! (Suc i)) (l ! (Suc (Suc i)))") prefer 2 apply force
  apply (insert order_key_lt)
  apply fast
done
  
lemma last_bigger_in_list_sorted_by_key_lt: 
"total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow>
(i <length l - Suc 0) \<Longrightarrow> key_lt (l ! i) (last l)"
apply (simp add:last_conv_nth)
apply (induct i)
 apply (subgoal_tac "length l - 2 < length l - Suc 0") prefer 2 apply force
 apply (insert hd_smallest_in_list_sorted_by_key_lt [of l "length l - 2"])
 apply (simp add: Suc_diff_Suc numeral_2_eq_2)
 
 apply (thin_tac "(total_order_key_lte \<Longrightarrow>
          l \<noteq> [] \<Longrightarrow> \<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i) \<Longrightarrow> length l - 2 < length l - Suc 0 \<Longrightarrow> key_lt (l ! 0) (l ! Suc (length l - 2)))")
 apply simp
 apply (subgoal_tac "\<exists> ll lr. (l = ll@lr \<and> length ll = Suc i)") prefer 2 apply (metis Cons_nth_drop_Suc Suc_leI Suc_lessD Suc_pred diff_add_inverse2 diff_diff_cancel id_take_nth_drop length_append length_drop length_greater_0_conv less_SucI) 
 apply (erule exE)+
 apply (erule conjE)
 apply clarify
 apply (drule_tac s="length ll" in sym)
 apply (simp add:nth_append)
 apply (case_tac "lr = []")
  
  apply force
 
  apply clarsimp
  apply (subgoal_tac "\<forall>ia\<in>{0..<length lr - Suc 0}. key_lt (lr ! ia) (lr ! Suc ia)")
  prefer 2 
   apply (simp add:atLeast0LessThan lessThan_def)
   apply (subgoal_tac "\<forall>ia. length ll \<le> ia \<and> ia < length ll + length lr - Suc 0 \<longrightarrow>
       key_lt (lr ! (ia - length ll)) (lr ! (Suc ia - length ll))") prefer 2 apply force
   apply (smt Suc_eq_plus1 add.commute add.left_commute diff_add_inverse le_add1 less_diff_conv)
  apply (insert hd_smallest_in_list_sorted_by_key_lt)
 apply (smt Suc_diff_Suc add_diff_cancel_left' diff_right_commute lessI)
done

lemma bigger_than_last_in_list_sorted_by_key_lt:
"total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow>
key_lt (last l) k \<Longrightarrow> (\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) k)"
by (meson atLeastLessThan_iff last_bigger_in_list_sorted_by_key_lt order_key_lt)

lemma bigger_than_last_in_list_sorted_by_key_lt':
"total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow>
key_lt (last l) k \<Longrightarrow> (\<forall>k'\<in> set l. key_lt k' k)"
by (smt One_nat_def Suc_pred in_set_conv_nth last_bigger_in_list_sorted_by_key_lt last_conv_nth length_pos_if_in_set less_antisym order_key_lt)

lemma bigger_than_subkeys_in_list_sorted_by_key_lt': "
total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
length lr = Suc (length l) \<Longrightarrow>
(\<forall>k'\<in> set l. key_lt k' k) \<Longrightarrow>
(\<forall>k' \<in> set (keys (last lr)). key_lt k' k) \<Longrightarrow>
(\<forall>i\<in>{0..<length l}. \<forall>k\<in>set (keys (lr ! i)). key_lt k (l ! i)) \<Longrightarrow>       
\<forall>x\<in>\<Union>a\<in>set lr. set (keys a). key_lt x k"
apply rule+
apply simp
apply clarsimp
apply (simp add: atLeast0LessThan lessThan_def)
apply (subgoal_tac "\<exists> ia \<le> length l. a = lr ! ia") prefer 2 apply (metis in_set_conv_nth less_Suc_eq_le) 
apply (erule exE)
apply (drule_tac x=ia in spec)
apply simp
apply (case_tac " ia < length l")
 apply clarsimp
 apply (subgoal_tac "key_lt (l!ia) k") prefer 2 apply force
 apply (subgoal_tac "key_lt x (l!ia)") prefer 2 apply force
 apply (insert order_key_lt)
 apply fast

 apply (thin_tac "\<forall>a b c. total_order_key_lte \<longrightarrow> key_lt a b \<and> key_lt b c \<longrightarrow> key_lt a c")
 apply (subgoal_tac "\<forall>k'\<in>set (keys (lr!length l)). key_lt k' k") prefer 2 apply (metis diff_Suc_1 last_conv_nth length_0_conv old.nat.distinct(2)) 
 apply (force)
done

lemma k_klt_hd_klt_all: "
total_order_key_lte \<Longrightarrow>
l \<noteq> [] \<Longrightarrow>
key_lt k (hd l) \<Longrightarrow> 
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow> 
\<forall>x\<in>set l. key_lt k x"
apply (simp add:hd_conv_nth atLeast0LessThan lessThan_def)
apply rule+
apply (subgoal_tac "\<exists> i < length l. x = l!i") prefer 2 apply (metis in_set_conv_nth) 
apply (erule exE)
apply (erule conjE)+
apply simp
apply clarsimp
apply (smt Suc_le_lessD Suc_pred atLeastLessThan_iff hd_smallest_in_list_sorted_by_key_lt less_Suc0 less_antisym less_or_eq_imp_le not_le order_key_lt)
done

lemma k_kle_hd_kle_all: "
total_order_key_lte \<Longrightarrow>
l \<noteq> [] \<Longrightarrow>
key_le k (hd l) \<Longrightarrow> 
(\<forall>i\<in>{0..<length l - Suc 0}. key_lt (l ! i) (l ! Suc i)) \<Longrightarrow> 
\<forall>x\<in>set l. key_le k x"
apply (simp add:hd_conv_nth atLeast0LessThan lessThan_def)
apply rule+
apply (subgoal_tac "\<exists> i < length l. x = l!i") prefer 2 apply (metis in_set_conv_nth) 
apply (erule exE)
apply (erule conjE)+
apply simp
apply clarsimp

sorry


lemma k_klt_hdsubkeys_kle_allsubkeys: "
total_order_key_lte \<Longrightarrow> 
l \<noteq> [] \<Longrightarrow>
length lr = Suc (length l) \<Longrightarrow>
(\<forall> x \<in> set l. key_lt k x) \<Longrightarrow>
(\<forall>x\<in>set (keys (hd lr)). key_le k x) \<Longrightarrow>
(\<forall>i\<in>{0..<length l}. \<forall>k\<in>set (keys (lr ! Suc i)). key_le (l ! i) k) \<Longrightarrow>       
\<forall>x\<in>\<Union>a\<in>set lr. set (keys a). key_le k x"
apply rule+
apply clarsimp
apply (subgoal_tac "keys (hd lr) = keys(lr!0)") prefer 2 apply (metis hd_conv_nth list.size(3) old.nat.distinct(2)) 
apply (simp add:atLeast0LessThan lessThan_def)
apply (subgoal_tac "\<exists> ia < length lr. a = lr!ia") prefer 2 apply (metis in_set_conv_nth) 
apply (erule exE)
apply simp
apply (case_tac ia)
 apply (force simp add:key_le_def)
 
 apply clarsimp
 apply (meson key_le_def nth_mem total_order_key_lte_def)
done
end
