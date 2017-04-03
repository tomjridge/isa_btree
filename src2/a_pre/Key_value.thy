theory Key_value
imports Prelude
begin

(* polymorphic just so that easier to deal with when supplying from ocaml side *)
type_synonym 'k key_order = "'k \<Rightarrow> 'k \<Rightarrow> int"
type_synonym 'k ord = "'k key_order"

(* generic defns --------------------------------------------------- *)

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
  

(* insert aux funs --------------------------------------------------------------- *)

(* FIXME aren't this aux funs shared with its? *)
definition split_leaf :: "constants \<Rightarrow> ('k*'v)list \<Rightarrow> (('k*'v)list * 'k * ('k*'v) list)" where
"split_leaf c kvs = (
  (* FIXME what is the best choice? min is probably too small; could split in two, but what if order is not dense? we may never insert any more keys at this point *)
  (* FIXME following assumes leaf has size max_leaf_size+1, not anything more? *)
  let cut_point = (c|>max_leaf_size+1 - c|>min_leaf_size) in  
  let (l,r) = split_at cut_point kvs in 
  let _ = assert_true' (List.length l \<ge> c|>min_leaf_size & List.length r \<ge> c|>min_leaf_size) in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible1 (STR ''key_value, split_leaf'')) in
  (l,k,r)
)"

(* let max and min be the relevant bounds; suppose node has max+1 keys; we could divide by 2 to get
max+1/2; but here we try to get the most in the left hand tree; 

we need min in rhs; 1 for the middle, so we need max+1 -1 -min = max-min in left (assumes that the node has
max+1 size; obviously we need to be more careful otherwise FIXME for bulk insert

*)

definition split_node :: 
  "constants \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" where
"split_node c n = (
  let (ks,rs) = n in
  let cut_point = (c|>max_node_keys-c|>min_node_keys) in  (* FIXME see above *)
  let (ks1,k,ks2) = split_at_3 cut_point ks in
  let _ = assert_true' (List.length ks2 \<ge> c|>min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  ((ks1,rs1),k,(ks2,rs2))
)"

end
