theory Frame
imports Key_value
begin

(* blocks on disk correspond to frames, which are like tree nodes, but with pointers rather than
children *)

datatype ('k,'v) t = Node_frame "'k list * r list" | Leaf_frame "('k*'v) list"
(* type_synonym pfr = "(key,value_t) t" *)

definition dest_Node_frame :: "('k,'v) t \<Rightarrow> ('k list * r list)" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Node_frame''))"

definition dest_Leaf_frame :: "('k,'v) t \<Rightarrow> ('k*'v) list" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Leaf_frame''))"


end