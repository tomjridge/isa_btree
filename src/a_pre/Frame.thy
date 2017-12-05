theory Frame
imports Prelude
begin

(* blocks on disk correspond to frames, which are like tree nodes, but
with pointers rather than children *)

(* type variable naming conventions:

'k - keys
'v - values
'r - references to disk blocks

*)

datatype ('k,'v,'r) frame = 
  Node_frame "'k list * 'r list" 
  | Leaf_frame "('k*'v) list"

(* type_synonym pfr = "(key,value_t) t" *)

definition dest_Node_frame :: "('k,'v,'r) frame \<Rightarrow> ('k list * 'r list)" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Node_frame''))"

definition dest_Leaf_frame :: "('k,'v,'r) frame \<Rightarrow> ('k*'v) list" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Leaf_frame''))"







(* old ================================== *)

(* there are local wf constraints relative to some particular
constants; but prefer to convert to tree and check wf *)

(*
definition wf_node_frame :: "constants \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"wf_node_frame c kn rn = ((kn + 1 = rn) & (c|>min_node_keys \<le> kn) & (kn \<le> c|>max_node_keys))"

definition wf_leaf_frame :: "constants \<Rightarrow> nat \<Rightarrow> bool" where
"wf_leaf_frame c n = ( c|>min_leaf_size \<le> n & n \<le> c|>max_leaf_size )"
*)

end