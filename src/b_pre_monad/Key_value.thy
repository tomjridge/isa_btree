theory Key_value
imports A_start_here
begin

(* k ord ------------------------------------------------------------ *)

(* use "ord" or "cmp" as var names; "k_cmp", "k_ord" *)
type_synonym 'k ord = "'k \<Rightarrow> 'k \<Rightarrow> int"

definition key_lt :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_lt ord k1 k2 = ( ord k1 k2 < 0)"

definition key_eq ::  "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_eq ord k1 k2 = ( ord k1 k2 = 0)"

(* key ordering, generic defns key_lt etc --------------------------- *)

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

definition okl_tests :: "bool" where
"okl_tests = assert_true (% _.
  (ordered_key_list nat_ord [0,1,2,3]) &
  (~(ordered_key_list nat_ord [0,1,1,3])))"


(* check keys ------------------------------------------------------- *)

(* check key set is bounded *)
definition check_keys :: "'k ord \<Rightarrow> 'k option => 'k set => 'k option => bool" where
"check_keys cmp kl ks kr = (
  let b1 = (case kl of None => True | Some kl => (! k : ks. key_le cmp kl k)) in
  let b2 = (case kr of None => True | Some kr => (! k : ks. key_lt cmp k kr)) in
  b1 & b2)"

definition check_keys_tests :: bool where
"check_keys_tests = assert_true (% _.
  (check_keys nat_ord (Some 1) (set[1,2,3]) (Some 4)) &
  (~(check_keys nat_ord (Some 1) (set[1,2,3]) (Some 3))))"

(* FIXME following looks a bit strange for l,u=None; what is the semantics of this function? *)
(* xs < l \<le> ks < u \<le> zs; an extended version of the above *)
definition check_keys_2 :: "'k ord \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> 'k option \<Rightarrow> 'k set \<Rightarrow> bool" where
"check_keys_2 cmp xs l ks u zs = (
  (case l=None of True \<Rightarrow> xs={} | _ \<Rightarrow> True) &
  (case u=None of True \<Rightarrow> zs={} | _ \<Rightarrow> True) &
  (check_keys cmp None xs l) &
  (check_keys cmp l ks u) &
  (check_keys cmp u zs None))"

definition check_keys_2_tests :: bool where
"check_keys_2_tests = assert_true (% _.
  (check_keys_2 nat_ord (set[0]) (Some 1) (set[1,2,3]) (Some 4) (set[4,5])))"



end


(* old

(* lt on kv pair is just lt on k components *)
definition kv_lt :: "'k ord \<Rightarrow> ('k*'v) \<Rightarrow> ('k*'v) \<Rightarrow> bool" where
"kv_lt ord kv1 kv2 = (key_lt ord (fst kv1) (fst kv2))"

datatype compare_t = LT | EQ | GT

definition key_compare :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> compare_t" where
"key_compare ord k1 k2 = (
   let n = ord k1 k2 in
   if n < 0 then LT else
   if n = 0 then EQ else
   GT)"


(* insert and delete in list of kv ---------------------------------- *)

(* FIXME may want to use binary search; but this assumes an array-like implementation *)

(*
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
*)



definition kvs_insert :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k*'v) s \<Rightarrow> ('k * 'v) s" where "
kvs_insert k_cmp k v kvs = (
  iter_step (% (kvs,kvs').
    case kvs' of 
    [] \<Rightarrow> None
    | (k',v')#kvs' \<Rightarrow> (
      case key_lt k_cmp k k' of 
      True \<Rightarrow> None
      | False \<Rightarrow> (
        case key_eq k_cmp k k' of 
        True \<Rightarrow> Some(kvs,kvs') 
        | False \<Rightarrow> (Some((k',v')#kvs,kvs')))))
    ([],kvs)
  |> (% (kvs,kvs'). (List.rev ((k,v)#kvs))@kvs'))"


(* check two lists of kv for equality; patched because values may have
some non-standard equality; used for debugging *)

definition kvs_equal :: "('k*'v) list \<Rightarrow> ('k*'v) list \<Rightarrow> bool" where
"kvs_equal = failwith (STR ''FIXME patch'')"

definition kvs_insert_tests :: bool where
"kvs_insert_tests = check_true (% _.
  let _ = assert_true (kvs_insert nat_ord 2 2 (List.map (% x. (x,x)) [0,1,3,4]) = 
    (List.map (% x. (x,x)) [0,1,2,3,4]))
  in
  let _ = assert_true (kvs_insert nat_ord 6 6 (List.map (% x. (x,x)) [0,1,3,4]) = 
    (List.map (% x. (x,x)) [0,1,3,4,6]))
  in
  True)"


(* delete a pair with a particular key from a list of pairs *)
definition kvs_delete :: "'k ord \<Rightarrow> 'k \<Rightarrow> ('k*'v)list \<Rightarrow> ('k*'v)list" where
"kvs_delete ord k kvs = List.filter (% kv. ~ (key_eq ord (fst kv) k)) kvs"
  

*)