theory Key_value
imports Main
begin

typedecl key
typedecl value_t

consts key_lt :: "key => key => bool"

definition key_le :: "key => key => bool" where
  "key_le k1 k2 == (k1 = k2) | (key_lt k1 k2)"

definition kv_lt :: "(key * value_t) => (key * value_t) => bool" where
  "kv_lt kv1 kv2 == (key_lt (fst kv1) (fst kv2))"

(*begin check keys definition*)
definition check_keys :: "key option => key list => key option => bool" where
"check_keys kl ks kr == (
let b1 = (
case kl of None => True 
| Some kl => (! k : set ks. key_le kl k)
)
in
let b2 = (
case kr of None => True 
| Some kr => (! k : set ks. key_lt k kr)
)
in
b1 & b2
)"
(*end check keys definition*)

end