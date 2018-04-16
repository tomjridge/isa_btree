theory Split_node
imports Prelude Disk_node
begin





end







(* old =================================================================== *)

(* treestack split_node (aka frame) ---------------------------------------- *)

(*

(* A treestack frame is essentially a node with a hole for some child;
suppose the node is Node(ks1@ks2,ts1@[t]@ts2); then a frame focused on t can be
represented as the following record. 'k is the key type; 'a is the
"child" type, which is either a tree, or a pointer to a tree depending
on whether we are taking the ADT view or the blocks-and-pointers view *)

(* FIXME ks1,ts1 stored in reverse? *)
record ('k,'a) split_node =
  f_ks1 :: "'k list"
  f_ts1 :: "'a list"
  f_t :: 'a
  f_ks2 :: "'k list"
  f_ts2 :: "'a list"

type_synonym ('k,'a) frame = "('k,'a) split_node"
  

definition dest_split_node :: 
  "('k,'a) split_node \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" 
where
"dest_split_node f = (
  (f|>f_ks1,f|>f_ts1),
  f|>f_t,
  (f|>f_ks2, f|>f_ts2))"


definition split_node_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) split_node \<Rightarrow> ('k,'b) split_node" where
"split_node_map g f = (
  \<lparr>
    f_ks1=(f|>f_ks1),
    f_ts1=(f|>f_ts1|>List.map g),
    f_t=(f|>f_t|>g),
    f_ks2=(f|>f_ks2),
    f_ts2=(f|>f_ts2|>List.map g)
  \<rparr>)"


definition with_t :: "'a \<Rightarrow> ('k,'a) split_node \<Rightarrow> ('k,'a) split_node" where
"with_t x f = f \<lparr> f_t:=x  \<rparr>"


definition split_node_equal:: "('k,'a) split_node \<Rightarrow> ('k,'a) split_node \<Rightarrow> bool" where
"split_node_equal f1 f2 = failwith (STR ''FIXME patch'')"
*)



(*
definition rsplit_to_split :: "('k,'a) rsplit_node \<Rightarrow> ('k,'a) split_node" where
"rsplit_to_split r = (
  let f= \<lparr>
    f_ks1=(r|>r_ks1|>List.rev),
    f_ts1=(r|>r_ts1|>List.rev),
    f_t=(r|>r_t),
    f_ks2=(r|>r_ks2),
    f_ts2=(r|>r_ts2) \<rparr>
  in
  f)"
*)

