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

end