theory Key_value
imports Prelude
begin

typedecl key
typedecl value_t

(*begin key order operators definition*)
consts key_lt :: "key => key => bool"

(* FIXME tr: bit strange - just use equality *)
definition key_eq :: "key => key => bool" where
  "key_eq k1 k2 == (~ (key_lt k1 k2)) & (~ (key_lt k2 k1))"

(* FIXME tr: bit strange - just use equality *)
definition key_le :: "key => key => bool" where
  "key_le k1 k2 == (key_eq k1 k2) | (key_lt k1 k2)"
(*end key order operators definition*)

(* tr alternative defn *)
definition wf_key_lt :: bool where
"wf_key_lt ==  
  (! k1 k2 k3. key_lt k1 k2 & key_lt k2 k3 \<longrightarrow> key_lt k1 k3) &
  (! k1 k2. (~ (key_lt k2 k1 \<or> (k2 = k1)) = key_lt k1 k2))"


definition kv_lt :: "(key * value_t) => (key * value_t) => bool" where
  "kv_lt kv1 kv2 == (key_lt (fst kv1) (fst kv2))"



definition ordered_key_list :: "key list \<Rightarrow> bool" where
"ordered_key_list ks = (
  ! i : set(from_to 0 (length ks -2)). key_lt (ks!i) (ks!(i+1)))"


(*begin check keys definition*)
definition check_keys 
 :: "key option => key set => key option => bool"
where
"check_keys kl ks kr == (
let b1 = (
case kl of None => True 
| Some kl => (! k : ks. key_le kl k)
)
in
let b2 = (
case kr of None => True 
| Some kr => (! k : ks. key_lt k kr)
)
in
b1 & b2
)"
(*end check keys definition*)

definition check_keys_2 :: "key set \<Rightarrow> key option \<Rightarrow> key set \<Rightarrow> key option \<Rightarrow> key set \<Rightarrow> bool" where
"check_keys_2 xs l ks u zs = (
  (case l=None of True \<Rightarrow> xs={} | _ \<Rightarrow> True) &
  (case u=None of True \<Rightarrow> zs={} | _ \<Rightarrow> True) &
  (check_keys None xs l) &
  (check_keys l ks u) &
  (check_keys u zs None)
)"


(* lemmas --------------------------------------------------------------- *)


(* FIXME might like to use strict total order with key_lt and aim to always eliminate key_le - better automation *)
(* this is an assumption for the rest of the development *)
definition total_order_key_lte :: " bool" where
"total_order_key_lte == (\<forall> a b c. 
   (key_le a b \<and> key_le b a \<longrightarrow> key_eq a b) \<and>
   (key_le a b \<and> key_le b c \<longrightarrow> key_le a c) \<and>
   (key_le a b \<or> key_le b a)
\<and> (a = b \<longrightarrow> (key_le a b)))" (* FIXME just use defn of key_le, with = *)

end
