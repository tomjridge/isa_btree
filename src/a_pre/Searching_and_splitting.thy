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

definition rsplit_get_bounds :: "('k,'a) rsplit_node \<Rightarrow> ('k option * 'k option)" where
"rsplit_get_bounds rn = (
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


(* convert a rsplit_node to a disk node *)
definition unsplit_node :: "('k,'a) rsplit_node \<Rightarrow> ('k list * 'a list)" where
"unsplit_node r = (
  let ks = (List.rev (r|>r_ks1))@(r|>r_ks2) in
  let rs = (List.rev (r|>r_ts1))@[r|>r_t]@(r|>r_ts2) in
  (ks,rs))"


  
end
