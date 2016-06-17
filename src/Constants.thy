theory Constants 
imports Main
begin

consts min_leaf_size :: nat
consts max_leaf_size :: nat
consts min_node_keys :: nat
consts max_node_keys :: nat

definition wf_constants :: "bool" where
"wf_constants == (
let wf_node_constants =
(1 <= min_node_keys 
&
  (max_node_keys = 2 * min_node_keys
  | max_node_keys = Suc (2 * min_node_keys))
)
in
let (wf_leaf_constants) =
(1 <= min_leaf_size
& 
 (max_leaf_size = 2 * min_leaf_size 
 | max_leaf_size = Suc (2 * min_leaf_size))
)
in
wf_node_constants & wf_leaf_constants
)"
end