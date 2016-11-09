theory Key_value
imports Prelude
begin

(* this makes code export easier; of course, key is abstract *)
datatype key = Private_key nat

(* FIXME really an abstract parameter; this for code export *)
definition key_ord :: "key => key => int"  where (* as ocaml compare *)
"key_ord k1 k2 = failwith ''key_ord''"

datatype value_t = Private_value nat

(*
(* nonsense to get code export to work *)
instantiation key :: equal begin
definition equal_key :: "key \<Rightarrow> key \<Rightarrow> bool" where "equal_key = (op = )" 
instance by intro_classes (simp add: equal_key_def)
end
*)




type_synonym kv_t = "key * value_t"
type_synonym kvs_t = "kv_t list"



  
definition key_lt :: "key \<Rightarrow> key \<Rightarrow> bool" where
"key_lt k1 k2 = (key_ord k1 k2 < 0)"

definition key_eq :: "key \<Rightarrow> key \<Rightarrow> bool" where
"key_eq k1 k2 = (key_ord k1 k2 = 0)"

definition key_le :: "key \<Rightarrow> key \<Rightarrow> bool" where
"key_le k1 k2 = (key_lt k1 k2 \<or> key_eq k1 k2)"

(* FIXME assume EQ is equality *)
definition wf_key_ord :: "bool" where
"wf_key_ord = (
 strict_linear_order { (x,y). key_lt x y }
 & (! k1 k2. (key_eq k1 k2) = (k2 = k1)) 
)"

(* very minor defn *)
definition kv_lt :: "(key * value_t) => (key * value_t) => bool" where
  "kv_lt kv1 kv2 == (key_lt (fst kv1) (fst kv2))"

definition ordered_key_list :: "key list \<Rightarrow> bool" where
"ordered_key_list ks = (
  ! i : set(from_to 0 (length ks -2)). key_lt (ks!i) (ks!(i+1)))"

(*begin check keys definition*)
definition check_keys :: "key option => key set => key option => bool" where
"check_keys kl ks kr = (
  let b1 = (case kl of None => True | Some kl => (! k : ks. key_le kl k)) in
  let b2 = (case kr of None => True | Some kr => (! k : ks. key_lt k kr)) in
  b1 & b2)"
(*end check keys definition*)

(* xs < l \<le> ks < u \<le> zs *)
definition check_keys_2 :: "key set \<Rightarrow> key option \<Rightarrow> key set \<Rightarrow> key option \<Rightarrow> key set \<Rightarrow> bool" where
"check_keys_2 xs l ks u zs = (
  (case l=None of True \<Rightarrow> xs={} | _ \<Rightarrow> True) &
  (case u=None of True \<Rightarrow> zs={} | _ \<Rightarrow> True) &
  (check_keys None xs l) &
  (check_keys l ks u) &
  (check_keys u zs None)
)"

(* insert/ update assuming list ordered *)
definition lf_ordered_insert :: "kv_t list \<Rightarrow> key \<Rightarrow> value_t \<Rightarrow> kv_t list" where
"lf_ordered_insert kvs k v = (
kvs (* FIXME *)
)"


end
