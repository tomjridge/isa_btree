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
 :: "key option => key list => key option => bool"
where
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
