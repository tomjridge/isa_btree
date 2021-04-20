theory Constants_and_size_types imports A_start_here begin

(* min/max size constants ------------------------------------------- *)

(* `constants` record type, which is used to record min and max bounds
for leaves and nodes *)

datatype_record constants = 
  min_leaf_size :: nat
  max_leaf_size :: nat
  min_node_keys :: nat
  max_node_keys :: nat

definition make_constants :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> constants" where
"make_constants a b c d = \<lparr> min_leaf_size=a, max_leaf_size=b, min_node_keys=c, max_node_keys=d \<rparr>"
(* NOTE the parsing ambiguity seems to be a clash between record and datatype_record; not sure
best way to fix *)
(* FIXME add wf constraint following docs $l'>=2l-1$ and $m' >= 2m$ *)


end