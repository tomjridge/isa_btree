theory Searching_and_splitting
imports Key_value
begin

(* Various definitions related to searching for a key in an ordered list of kv pairs, or a node
frame *)

(* alternative split_node, with reversed ks1,ts1 for efficiency ------------------ *)

type_synonym 'a s = "'a list"

record ('k,'a) rsplit_node =
  r_ks1 :: "'k list"
  r_ts1 :: "'a list"
  r_t :: 'a
  r_ks2 :: "'k list"
  r_ts2 :: "'a list"

(* functional projection a bit clumsy when writing functional update; 
often better to project to pairs first *)
definition dest_rsplit_node :: "('k,'a) rsplit_node \<Rightarrow> 'k s * 'a s * 'a * 'k s * 'a s" where
"dest_rsplit_node r = (r|>r_ks1,r|>r_ts1,r|>r_t,r|>r_ks2,r|>r_ts2)"

definition rsplit_node_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) rsplit_node \<Rightarrow> ('k,'b) rsplit_node" where
"rsplit_node_map g f = (
  \<lparr>
    r_ks1=(f|>r_ks1),
    r_ts1=(f|>r_ts1|>List.map g),
    r_t=(f|>r_t|>g),
    r_ks2=(f|>r_ks2),
    r_ts2=(f|>r_ts2|>List.map g)
  \<rparr>)"


(* get_lu_bounds for rsplit_node ---------------------------- *)

definition get_lu_bounds :: "('k,'a) rsplit_node \<Rightarrow> ('k option * 'k option)" where
"get_lu_bounds rn = (
  let l = case rn|>r_ks1 of [] \<Rightarrow> None | x # xs \<Rightarrow> Some x in
  let u = case rn|>r_ks2 of [] \<Rightarrow> None | x # xs \<Rightarrow> Some x in
  (l,u))"


(* split node based on search key ------------------------------ *)

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
"mk_rsplit_node cmp k ks_rs = (
  let ((ks1,rs1),r,(ks2,rs2)) = aux' cmp k ([],[]) ks_rs in
  \<lparr>
    r_ks1=ks1,
    r_ts1=rs1,
    r_t=r,
    r_ks2=ks2,
    r_ts2=rs2
  \<rparr>)"


(* convert a rsplit_node to a disk node FIXME move to searching and splitting? *)
definition unsplit_node :: "('k,'a) rsplit_node \<Rightarrow> ('k list * 'a list)" where
"unsplit_node r = (
  let ks = (List.rev (r|>r_ks1))@(r|>r_ks2) in
  let rs = (List.rev (r|>r_ts1))@[r|>r_t]@(r|>r_ts2) in
  (ks,rs))"


  
end


(* old -------- *)



(*
(* old search_key_to_index ---------------------------------------------- *)

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




(*
(* old split_ks_rs ------------------------------------------------------ *)

(* when splitting leaves and nodes, we need to split based on a
particular key; also used when constructing frames *)


definition split_ks_rs' :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"split_ks_rs' cmp k ks_rs = (
  let r = mk_rsplit_node cmp k ks_rs in
  let f = rsplit_to_split r in
  (((f|>f_ks1),(f|>f_ts1)),(f|>f_t),((f|>f_ks2),(f|>f_ts2))))"
  
(* FIXME tested? *)

definition rsplit_ks_rs :: "'k ord \<Rightarrow> 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k,'a) rsplit_node" where
"rsplit_ks_rs cmp k ks_rs = mk_rsplit_node cmp k ks_rs"

*)
