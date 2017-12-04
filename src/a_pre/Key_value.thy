theory Key_value
imports Prelude
begin

(* NOTE definitions are polymorphic in the key type *)

(* FIXME what does this mean? equality is just hol equality, so we use
this rather than a compare function *)

(* 'k ord, kv ops --------------------------------------------------- *)


(* keys are ordered *)
type_synonym 'k ord = "'k \<Rightarrow> 'k \<Rightarrow> int"
  
(* NOTE variables of type 'k ord are typically called ord, or (better) cmp *)

(* operations on keys and values (in fact, just a key comparison function) *)
record ('k,'v) kv_ops =
  compare_k :: "'k ord"
  

(* check two lists of kv for equality; patched because values may have
some non-standard equality *)

definition kvs_equal :: "('k*'v) list \<Rightarrow> ('k*'v) list \<Rightarrow> bool" where
"kvs_equal = failwith (STR ''FIXME patch'')"


(* NOTE 'v is only compared for equality in wf checks; we assume these
are only tested for simple 'v for which ocaml's = is satisfactory; in
fact, in the isa code we only compare trees for equality, so we can
drop this altogether *)

(*
definition v_equal :: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
"v_equal = failwith (STR ''FIXME patch'')"
*)


(* key ordering, generic defns key_lt etc --------------------------- *)

definition key_lt :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_lt ord k1 k2 = ( ord k1 k2 < 0)"

definition key_eq :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_eq ord k1 k2 = ( ord k1 k2 = 0)"

definition key_le :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_le ord k1 k2 = ( ord k1 k2 <= 0)"

(* simple abbrev - no need to mention in axioms *)
definition key_gt :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_gt ord k1 k2 = (~ ( key_le ord k1 k2))"

(* FIXME this is horrible - we require merely that it is a total order *)
definition wf_key_ord :: "'k ord \<Rightarrow> bool" where
"wf_key_ord ord = (
  let le = key_le ord in
  (! k1 k2. le k1 k2 = (key_lt ord k1 k2 | key_eq ord k1 k2)) &  (* true by defn *)
  (! k1. le k1 k1) &
  (! k1 k2 k3. le k1 k2 & le k2 k3 \<longrightarrow> le k1 k3) &
  (! k1 k2. le k1 k2 | le k2 k1) &
  (! k1 k2. key_eq ord k1 k2 \<longrightarrow> (k1=k2))  (* FIXME may need this? *)
)"

(* lt on kv pair is just lt on k components *)
definition kv_lt :: "'k ord \<Rightarrow> ('k*'v) \<Rightarrow> ('k*'v) \<Rightarrow> bool" where
"kv_lt ord kv1 kv2 = (key_lt ord (fst kv1) (fst kv2))"


(* ordererd key list ------------------------------------------------ *)

(* ordered key list, defined pointwise rather than inductively *)
definition ordered_key_list :: "'k ord \<Rightarrow> 'k list \<Rightarrow> bool" where
"ordered_key_list ord ks = (
  (List.length ks < 2) |  
  (! i : set(from_to 0 (length ks -2)). key_lt ord (ks!i) (ks!(i+1))))"

definition nat_ord :: "nat \<Rightarrow> nat \<Rightarrow> int" where
"nat_ord x y = (
  let n2i = Int.int in
  (n2i x)-(n2i y))"

definition okl_tests :: "unit" where
"okl_tests = (
  let _ = assert_true(ordered_key_list nat_ord [0,1,2,3]) in
  let _ = assert_true(~(ordered_key_list nat_ord [0,1,1,3])) in
  ())"


(* check keys ------------------------------------------------------- *)

(* check key set is bounded *)
definition check_keys :: "'k ord \<Rightarrow> 'k option => 'k set => 'k option => bool" where
"check_keys cmp kl ks kr = (
  let b1 = (case kl of None => True | Some kl => (! k : ks. key_le cmp kl k)) in
  let b2 = (case kr of None => True | Some kr => (! k : ks. key_lt cmp k kr)) in
  b1 & b2)"

definition ck_tests :: unit where
"ck_tests = (
  let _ = assert_true (check_keys nat_ord (Some 1) (set[1,2,3]) (Some 4)) in
  let _ = assert_true (~(check_keys nat_ord (Some 1) (set[1,2,3]) (Some 3))) in
  ())"


(* xs < l \<le> ks < u \<le> zs; an extended version of the above *)
definition check_keys_2 :: "'k ord \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> bool" where
"check_keys_2 cmp xs l ks u zs = (
  (case l=None of True \<Rightarrow> xs={} | _ \<Rightarrow> True) &
  (case u=None of True \<Rightarrow> zs={} | _ \<Rightarrow> True) &
  (check_keys cmp None xs l) &
  (check_keys cmp l ks u) &
  (check_keys cmp u zs None)
)"

definition ck2_tests :: unit where
"ck2_tests = (
  let _ = assert_true (check_keys_2 nat_ord (set[0]) (Some 1) (set[1,2,3]) (Some 4) (set[4,5])) in
  ())"


(* insert and delete in list of kv ---------------------------------- *)

(* insert a new kv into a list of kvs; used to insert new binding into a leaf *)
primrec kvs_insert :: "'k ord \<Rightarrow> 'k*'v \<Rightarrow> ('k*'v)list \<Rightarrow> ('k*'v)list" where
"kvs_insert cmp kv [] = [kv]"
| "kvs_insert cmp kv (kv'#kvs') = (
  let (k,v) = kv in
  let (k',v') = kv' in
  if key_lt cmp k' k then (k',v')#(kvs_insert cmp kv kvs')
  else if (key_eq cmp k k') then (k,v)#kvs' else
  (k,v)#(k',v')#kvs'
)"

definition kvs_insert_tests :: unit where
"kvs_insert_tests = (
  let _ = assert_true (kvs_insert nat_ord (2,2) (List.map (% x. (x,x)) [0,1,3,4]) = 
    (List.map (% x. (x,x)) [0,1,2,3,4]))
  in
  let _ = assert_true (kvs_insert nat_ord (6,6) (List.map (% x. (x,x)) [0,1,3,4]) = 
    (List.map (% x. (x,x)) [0,1,3,4,6]))
  in
  ())"


(* delete a pair with a particular key from a list of pairs *)
definition kvs_delete :: "'k ord \<Rightarrow> 'k \<Rightarrow> ('k*'v)list \<Rightarrow> ('k*'v)list" where
"kvs_delete ord k kvs = List.filter (% kv. ~ (key_eq ord (fst kv) k)) kvs"
  

(* search_key_to_index ---------------------------------------------- *)

(* FIXME move *)

(* return the index to the first key k1 st k < k1, or length of list if not found *)
(*tr: assumes xs are sorted *)
definition search_key_to_index :: "'k ord \<Rightarrow> 'k list => 'k => nat" where
"search_key_to_index cmp ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt cmp k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  i')"

definition sk2i_tests :: unit where
"sk2i_tests = (
  let sk2i = search_key_to_index nat_ord in
  let _ = assert_true (sk2i [0,10,20,30,40] 20 = 3) in
  ())"


(* split_ks_rs ------------------------------------------------------ *)

(* when splitting leaves and nodes, we need to split based on a
particular key; also used when constructing frames *)

(* this version is high level but slow; prefer following defn which
TODO should be equivalent (!) *)

definition split_ks_rs' :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" where
"split_ks_rs' cmp k ks_rs = (
  let (ks,rs) = ks_rs in
  let _ = check_true (% _. List.length rs = List.length ks + 1) in
  let i = search_key_to_index cmp ks k in
  let _ = check_true (% _. i \<le> List.length ks) in
  let (ks1,ks2) = split_at i ks in
  let (rs1,r',rs2) = split_at_3 i rs in
  ((ks1,rs1),r',(ks2,rs2))
)"
  

(* NB ks_rs1 stored in reverse *)
function aux :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) \<Rightarrow> 
    ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"aux cmp k0 ks_rs1 ks_rs2 = (
  let (ks1,rs1) = ks_rs1 in
  let (ks,rs) = ks_rs2 in
  let (r,rs') = (List.hd rs,List.tl rs) in
  case ks of 
  [] \<Rightarrow> ( 
    ( (List.rev ks1,List.rev rs1), r, (ks,rs')))
  | k#ks' \<Rightarrow> (
    if key_lt cmp k0 k then
      (* reached the right place *)
      ( (List.rev ks1,List.rev rs1), r, (ks,rs'))
    else 
      aux cmp k0  (k#ks1,r#rs1) (ks',rs'))
)"
apply (force)+ done
termination aux
 by (force intro:FIXME)


(* search through a list, and stop when we reach a position where
k1\<le>k<k2, or equivalently (given ordered list) k < k2 *)

definition split_ks_rs :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"split_ks_rs cmp k ks_rs = (
  let res = aux cmp k ([],[]) ks_rs in
  let _ = check_true (% _. split_ks_rs' cmp k ks_rs = res) in
  res)"
  
(* NOTE tested via split_ks_rs' *)


(* insert aux funs: split_leaf and split_node ----------------------- *)

(* FIXME aren't these aux funs shared with its? *)

(* FIXME for insert_many we want to parameterize split_leaf so that it
results in a full left leaf *)

(* FIXME document *)

definition split_leaf :: "constants \<Rightarrow> ('k*'v)list \<Rightarrow> (('k*'v) list * 'k * ('k*'v) list)" where
"split_leaf c kvs = (
  let _ = check_true (% _. List.length kvs \<ge> c|>max_leaf_size+1) in
  (* FIXME what is the best choice? min is probably too small; could
  split in two, but what if order is not dense? we may never insert
  any more keys at this point *)
  (* FIXME following assumes leaf has size max_leaf_size+1, not anything more? *)
  let cut_point = (c|>max_leaf_size+1 - c|>min_leaf_size) in  
  let _ = check_true (% _ . cut_point \<le> List.length kvs) in
  let (l,r) = split_at cut_point kvs in 
  let _ = check_true (% _. List.length l \<ge> c|>min_leaf_size & List.length r \<ge> c|>min_leaf_size) in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible1 (STR ''key_value, split_leaf'')) in
  (l,k,r)
)"

(* let max and min be the relevant bounds; suppose node has max+1
keys; we could divide by 2 to get max+1/2; but here we try to get the
most in the left hand tree;

we need min in rhs; 1 for the middle, so we need max+1 -1 -min =
max-min in left (assumes that the node has max+1 size; obviously we
need to be more careful otherwise FIXME for bulk insert
*)

definition split_node :: 
  "constants \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" 
where
"split_node c n = (
  let (ks,rs) = n in

  let cut_point = (c|>max_node_keys-c|>min_node_keys) in  
  (* FIXME see above; FIXME prefer to split equally even in insert_many case? *)

  let (ks1,k,ks2) = split_at_3 cut_point ks in
  let _ = check_true (%_.List.length ks2 \<ge> c|>min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  (* FIXME check that uses of split_leaf and split_node enforce wellformedness *)
  ((ks1,rs1),k,(ks2,rs2))
)"

  

end