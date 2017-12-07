theory Searching_and_splitting
imports Key_value Disk_node Split_node
begin

(* Various definitions related to searching for a key in an ordered list of kv pairs, or a node
frame *)

(* construct an rsplit_node from a node and a search key *)

(* NB ks_rs1 stored in reverse *)
function aux' :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) \<Rightarrow> 
    ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"aux' cmp k0 ks_rs1 ks_rs2 = (
  let (ks1,rs1) = ks_rs1 in
  let (ks,rs) = ks_rs2 in
  let (r,rs') = (List.hd rs,List.tl rs) in
  case ks of 
  [] \<Rightarrow> ( (ks1,rs1), 
          r, 
          (ks,rs'))
  | k#ks' \<Rightarrow> (
    if key_lt cmp k0 k then
      (* reached the right place *)
      ( (ks1,rs1), 
        r, 
        (ks,rs'))
    else 
      aux' cmp k0  (k#ks1,r#rs1) (ks',rs'))
)"
apply (force)+ done
termination aux'
 by (force intro:FIXME)


definition mk_rsplit_node :: "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'r list) \<Rightarrow> ('k,'r)rsplit_node" where
"
mk_rsplit_node cmp k ks_rs = (
  let ((ks1,rs1),r,(ks2,rs2)) = aux' cmp k ([],[]) ks_rs in
  \<lparr>
    r_ks1=ks1,
    r_ts1=rs1,
    r_t=r,
    r_ks2=ks2,
    r_ts2=rs2
  \<rparr>)"

(* FIXME replace all the following with versions based on rsplit *)



(* split_ks_rs ------------------------------------------------------ *)

(* when splitting leaves and nodes, we need to split based on a
particular key; also used when constructing frames *)


definition split_ks_rs :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"split_ks_rs cmp k ks_rs = (
  let r = mk_rsplit_node cmp k ks_rs in
  let f = rsplit_to_split r in
  (((f|>f_ks1),(f|>f_ts1)),(f|>f_t),((f|>f_ks2),(f|>f_ts2))))"
  
(* FIXME tested? *)


(* insert aux funs: split_leaf and split_node ----------------------- *)

(* FIXME these functions don't really belong here - they are a different kind
of splitting, based on size not search key *)

(* FIXME aren't these aux funs shared with its? *)

(* FIXME for insert_many we want to parameterize split_leaf so that it
results in a full left leaf *)

(* FIXME document *)

(* if a leaf is too big, we split it to get two leaves (lists of kv); we also return the separator
key k such that l < k \<le> r *)

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
  let _ = check_true (% _. List.length ks2 \<ge> c|>min_node_keys) in
  let (rs1,rs2) = split_at (cut_point+1) rs in
  (* FIXME check that uses of split_leaf and split_node enforce wellformedness *)
  ((ks1,rs1),k,(ks2,rs2))
)"

  
end


(* old ============================================================== *)



(*
(* search_key_to_index ---------------------------------------------- *)

(* FIXME move *)

(* return the index to the first key k1 st k < k1, or length of list if not found *)
(*tr: assumes xs are sorted *)
definition search_key_to_index :: "'k ord \<Rightarrow> 'k list => 'k => nat" where
"search_key_to_index cmp ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt cmp k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  let _ = check_true (% _. i' \<le> List.length ks) in
  i')"

definition sk2i_tests :: unit where
"sk2i_tests = (
  let sk2i = search_key_to_index nat_ord in
  let _ = assert_true (sk2i [0,10,20,30,40] 20 = 3) in
  let _ = assert_true (sk2i [0,10,20,30,40] 50 = 5) in
  ())"
*)




(*

(* this version is high level but slow; prefer following defn which
TODO should be equivalent (!) *)

(* given a key k and a list of (ks,rs), split and identify the child that 
may contain k *)

definition split_ks_rs' :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" where
"split_ks_rs' cmp k ks_rs = (
  let (ks,rs) = ks_rs in
  let _ = check_true (% _. check_length_ks_rs (ks,rs)) in
  let i = search_key_to_index cmp ks k in
  let (ks1,ks2) = split_at i ks in
  let (rs1,r',rs2) = split_at_3 i rs in
  ((ks1,rs1),r',(ks2,rs2))
)"
  
*)





(*
(* search through a list, and stop when we reach a position where
k1\<le>k<k2, or equivalently (given ordered list) k < k2 *)

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
  [] \<Rightarrow> ( (List.rev ks1,List.rev rs1), 
          r, 
          (ks,rs'))
  | k#ks' \<Rightarrow> (
    if key_lt cmp k0 k then
      (* reached the right place *)
      ( (List.rev ks1,List.rev rs1), 
        r, 
        (ks,rs'))
    else 
      aux cmp k0  (k#ks1,r#rs1) (ks',rs'))
)"
apply (force)+ done
termination aux
 by (force intro:FIXME)
*)