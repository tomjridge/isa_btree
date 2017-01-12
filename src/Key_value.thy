theory Key_value
imports Key_value_types
begin


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
  (List.length ks < 2) |  
  (! i : set(from_to 0 (length ks -2)). key_lt (ks!i) (ks!(i+1)))
)"

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

(* for leaf *)
primrec kvs_insert :: "(key*value_t) \<Rightarrow> kvs_t \<Rightarrow> kvs_t" where
"kvs_insert kv [] = [kv]"
| "kvs_insert kv (kv'#kvs') = (
  let (k,v) = kv in
  let (k',v') = kv' in
  let i = key_ord k' k in
  if i < 0 then (k',v')#(kvs_insert kv kvs')
  else if i=0 then (k,v)#kvs' else
  (k,v)#(k',v')#kvs'
)"

definition kvs_delete :: "key \<Rightarrow> kvs \<Rightarrow> kvs" where
"kvs_delete k kvs = List.filter (% kv. fst kv \<noteq> k) kvs"
  
(* insert aux funs --------------------------------------------------------------- *)

(* FIXME aren't this aux funs shared with its? *)
definition split_leaf :: "kvs \<Rightarrow> (kvs * k * kvs)" where
"split_leaf kvs = (
  (* FIXME what is the best choice? min is probably too small; could split in two, but what if order is not dense? we may never insert any more keys at this point *)
  (* FIXME following assumes leaf has size max_leaf_size+1, not anything more? *)
  let cut_point = (max_leaf_size+1 - min_leaf_size) in  
  let (l,r) = split_at cut_point kvs in 
  let _ = assert_true' (List.length l \<ge> min_leaf_size & List.length r \<ge> min_leaf_size) in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible1 ''key_value, split_leaf'') in
  (l,k,r)
)"

(* let max and min be the relevant bounds; suppose node has max+1 keys; we could divide by 2 to get
max+1/2; but here we try to get the most in the left hand tree; 

we need min in rhs; 1 for the middle, so we need max+1 -1 -min = max-min in left

*)


definition split_node :: "(ks * 'a list) \<Rightarrow> (ks * 'a list) * k * (ks * 'a list)" where
"split_node n = (
  let (ks,rs) = n in
  let cut_point = (max_node_keys-min_node_keys) in  (* FIXME see above *)
  let (ks1,k,ks2) = split_at_3 cut_point ks in
  let _ = assert_true' (List.length ks2 \<ge> min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  ((ks1,rs1),k,(ks2,rs2))
)"


(* search_key_to_index ------------- *)

(* FIXME move *)

(* return the index to the first key k1 st k < k1, or length of list if not found *)
(*tr: assumes xs are sorted *)
definition search_key_to_index :: "key list => key => nat" where
"search_key_to_index ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  i')"

definition split_ks_rs :: "key \<Rightarrow> (ks * 'a list) \<Rightarrow> (ks * 'a list) * 'a * (ks * 'a list)" where
"split_ks_rs k ks_rs = (
  let (ks,rs) = ks_rs in
  let i = search_key_to_index ks k in
  let (ks1,ks2) = split_at i ks in
  let (rs1,r',rs2) = split_at_3 i rs in
  ((ks1,rs1),r',(ks2,rs2))
)"
  
end
