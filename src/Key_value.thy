theory Key_value
imports Main
begin

typedecl key
typedecl value_t

consts key_lt :: "key \<Rightarrow> key \<Rightarrow> bool"

definition key_le :: "key => key => bool" where
  "key_le k1 k2 == (k1 = k2) | (key_lt k1 k2)"

definition kv_lt :: "(key * value_t) => (key * value_t) => bool" where
  "kv_lt kv1 kv2 == (key_lt (fst kv1) (fst kv2))"


definition check_keys :: "key option \<Rightarrow> key list \<Rightarrow> key option \<Rightarrow> bool" where
"check_keys kl ks kr == (
let b1 = (
case kl of None \<Rightarrow> True 
| Some kl \<Rightarrow> (! k : set ks. key_le kl k)
)
in
let b2 = (
case kr of None \<Rightarrow> True 
| Some kr \<Rightarrow> (! k : set ks. key_lt k kr)
)
in
b1 & b2
)"

end