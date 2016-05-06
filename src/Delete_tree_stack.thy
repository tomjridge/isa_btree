theory Delete_tree_stack
imports Tree Insert_tree_stack
begin
(*I need new datatypes in tree stack*)



(*BEGIN -this should go in the Utils theory*)
(*remove nth from list*)
fun remove_at :: "nat => 'a list => 'a list" where
"remove_at i [] = []" |
"remove_at 0 (x#xs) = xs" |
"remove_at (Suc i) (x#xs) = x#(remove_at i xs)"

definition remove_key_child :: "nat => Tree => Tree" where
"remove_key_child i t == (
case t of 
Leaf ls => Leaf (remove_at i ls)
| Node (ks,rs) => (*when I remove from a Node, there has been a merge, so I know I MUST delete a key and a child*)
  if i = length rs 
  then Node((remove_at (i-1) ks),(remove_at i rs))
  else Node((remove_at i ks),(remove_at i rs))
)
"
(*END - this should go in the Utils theory*)

(*BEGIN - this should go in a del_tree_stack theory*)

(*begin delete types*)
datatype up_or_delete = DUp "Tree" | DDelete "(Tree * nat)"

type_synonym del_focus_t = "up_or_delete"

datatype del_tree_stack = Del_tree_stack "del_focus_t * context_t"

definition dest_del_ts :: "del_tree_stack => (del_focus_t * context_t)" where
"dest_del_ts dts== (
case dts of Del_tree_stack ts => ts)
"
(*end delete types*)
definition is_too_slim :: "Tree => bool" where
"is_too_slim t = (
case t of
Leaf xs =>
 let leaf_size = length xs in
 (1 < leaf_size) & (leaf_size < min_leaf_size)
| Node (ks,_) =>
 let node_keys = length ks in
 (1 < node_keys) & (node_keys < min_node_keys)
)
"

(*begin step del tree stack*)
definition update_del_focus_at_position :: "node_t => nat => del_focus_t => del_focus_t" where
"update_del_focus_at_position n i f == (
let (ks,rs) = n in
case f of
DUp t => 
(let rs2 = dest_Some(list_replace_1_at_n rs i t) in
DUp(Node(ks,rs2)))
| DDelete (t,d_index) => 
(* I need to delete in focus_t, and restructure by using rs if the children size of focus_t is too small*)
let t' = (remove_key_child d_index t) in
(*now I need to check if the current sizes require a steal or a merge*)
(case is_too_slim t' of
False => 
 (let rs2 = dest_Some(list_replace_1_at_n rs i t') in
 DUp(Node(ks,rs2)))
| True =>
(*in this case I can both steal or merge.
  
  * I will steal if the right sibling is not slim or the left sibling is not slim;

  * otherwise, I will merge with the right sibling, if it exists, or with the left sibling.
*)
f
)
)
"


definition step_del_tree_stack :: "del_tree_stack => del_tree_stack option" where
"step_del_tree_stack ts == (
let (f,stk) = dest_del_ts ts in
case stk of 
Nil => None
| ((lb,(n,i),rb)#xs) => (
let f2 = update_del_focus_at_position n i f in
Some(Del_tree_stack(f2,xs))
)

)

"
(*end step del tree stack*)
(*END*)

(*BEGIN delete wf statements*)
definition wellformed_del_focus :: "del_focus_t => bool => bool" where
"wellformed_del_focus f stack_empty == (
case f of
DUp t => (wellformed_tree (Rmbs stack_empty) t)
| DDelete (t,_) => (wellformed_tree (Rmbs stack_empty) t)  
)"

definition wellformed_del_ts :: "del_tree_stack => bool" where
"wellformed_del_ts ts == (
let (f,stk) = dest_del_ts ts in
wellformed_del_focus f (stk=[])
& wellformed_context stk
(* maybe later..
& wellformed_del_ts_1 ts*))"
(*END delete wf statements*)
end