theory Constants_and_size_types imports A_start_here begin

(* min/max size constants ------------------------------------------- *)


(* `constants` record type, which is used to record min and max bounds
for leaves and nodes *)

record constants = 
  min_leaf_size :: nat
  max_leaf_size :: nat
  min_node_keys :: nat
  max_node_keys :: nat

definition make_constants :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> constants" where
"make_constants a b c d = \<lparr> min_leaf_size=a, max_leaf_size=b, min_node_keys=c, max_node_keys=d \<rparr>"

(* FIXME add wf constraint following docs $l'>=2l-1$ and $m' >= 2m$ *)


(* small node or leaf ----------------------------------------------- *)

(* `min_size_t` is a datatype which flags whether nodes and leaves
are small or not; a small root can potentially have no children *)

datatype min_size_t = 
  Small_root_node_or_leaf
  | Small_node
  | Small_leaf

type_synonym ms_t = "min_size_t option"

end