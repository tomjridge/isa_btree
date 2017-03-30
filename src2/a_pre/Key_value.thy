theory Key_value
imports Prelude
begin

(* want to have uniform definitions for the rest of the code; but everything is parametric on the 
key order and kv types; so we assume a universal key and value type *)

typedecl univ_key
type_synonym key = univ_key
type_synonym k = key
type_synonym ks = "k list"

typedecl univ_value
type_synonym value_t = univ_value
type_synonym v = value_t

type_synonym kv = "k*v"
type_synonym kvs = "kv list" 

consts k2u :: "'k \<Rightarrow> univ_key"
consts v2u :: "'v \<Rightarrow> univ_value"

(* o is "equal", -ve is lt, +ve is gt *)
type_synonym 'k ord = "'k \<Rightarrow> 'k \<Rightarrow> int"

(* FIXME assume EQ is equality *)
definition wf_key_ord :: "'k ord \<Rightarrow> bool" where
"wf_key_ord cmp = (
 strict_linear_order { (x,y). cmp x y < 0 }
 & (! k1 k2. (cmp k1 k2 = 0) = (k2 = k1)) 
)"

definition key_lt :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_lt cmp k1 k2 = (cmp k1 k2 < 0)"

definition key_le :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_le cmp k1 k2 = (cmp k1 k2 \<le> 0)"

(* very minor defn *)
definition kv_lt :: "'k ord \<Rightarrow> ('k*'v) \<Rightarrow> ('k*'v) \<Rightarrow> bool" where
  "kv_lt ord kv1 kv2 = (key_lt ord (fst kv1) (fst kv2))"

definition ordered_key_list :: "'k ord \<Rightarrow> 'k list \<Rightarrow> bool" where
"ordered_key_list cmp ks = (
  (List.length ks < 2) |  
  (! i : set(from_to 0 (length ks -2)). key_lt cmp (ks!i) (ks!(i+1)))
)"

(*begin check keys definition*)
definition check_keys :: "'k ord \<Rightarrow> 'k option => 'k set => 'k option => bool" where
"check_keys cmp kl ks kr = (
  let b1 = (case kl of None => True | Some kl => (! k : ks. key_le cmp kl k)) in
  let b2 = (case kr of None => True | Some kr => (! k : ks. key_lt cmp k kr)) in
  b1 & b2)"
(*end check keys definition*)

(* xs < l \<le> ks < u \<le> zs *)
definition check_keys_2 :: "'k ord \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> bool" where
"check_keys_2 cmp xs l ks u zs = (
  (case l=None of True \<Rightarrow> xs={} | _ \<Rightarrow> True) &
  (case u=None of True \<Rightarrow> zs={} | _ \<Rightarrow> True) &
  (check_keys cmp None xs l) &
  (check_keys cmp l ks u) &
  (check_keys cmp u zs None)
)"

(* for leaf *)
primrec kvs_insert :: "'k ord \<Rightarrow> 'k*'v \<Rightarrow> ('k*'v)list \<Rightarrow> ('k*'v)list" where
"kvs_insert cmp kv [] = [kv]"
| "kvs_insert cmp kv (kv'#kvs') = (
  let (k,v) = kv in
  let (k',v') = kv' in
  let i = cmp k' k in
  if i < 0 then (k',v')#(kvs_insert cmp kv kvs')
  else if i=0 then (k,v)#kvs' else
  (k,v)#(k',v')#kvs'
)"

definition kvs_delete :: "'k \<Rightarrow> ('k*'v)list \<Rightarrow> ('k*'v)list" where
"kvs_delete k kvs = List.filter (% kv. fst kv \<noteq> k) kvs"
  
(* search_key_to_index ------------- *)

(* FIXME move *)

(* return the index to the first key k1 st k < k1, or length of list if not found *)
(*tr: assumes xs are sorted *)
definition search_key_to_index :: "'k ord \<Rightarrow> 'k list => 'k => nat" where
"search_key_to_index cmp ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt cmp k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  i')"

definition split_ks_rs :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" where
"split_ks_rs cmp k ks_rs = (
  let (ks,rs) = ks_rs in
  let i = search_key_to_index cmp ks k in
  let (ks1,ks2) = split_at i ks in
  let (rs1,r',rs2) = split_at_3 i rs in
  ((ks1,rs1),r',(ks2,rs2))
)"
  
end
