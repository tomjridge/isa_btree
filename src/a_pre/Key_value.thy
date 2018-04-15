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

(* FIXME following looks a bit strange for l,u=None; what is the semantics of this function? *)
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

(* FIXME may want to use binary search; but this assumes an array-like implementation *)

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
  


end