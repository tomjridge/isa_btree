(* [[file:~/workspace/agenda/myTasks.org::tree_stack_src][tree_stack_src]] *)
theory Tree_stack
imports Tree
begin

(*begin focus definition*)
datatype 'f focus_t = Focus 'f
(*end focus definition*)

(*begin context definition*)
type_synonym left_bound = "key option"

type_synonym right_bound = "key option"

type_synonym context_t =
 "(left_bound * (node_t * nat) * right_bound) list"
(*end context definition*)

definition ctx_to_map :: "context_t => (key,value_t) map" where
"ctx_to_map ctx == (
let leaves = List.map (% (_,(n,_),_). List.concat(tree_to_leaves (Node(n)))) ctx in
map_of(List.concat leaves))"

(*begin treestack definition*)
datatype 'f tree_stack = Tree_stack "'f focus_t * context_t"
(*end treestack definition*)

(*begin wfcontext definition*)
definition subtree_indexes :: "node_t => nat set" where
"subtree_indexes n == (
  case n of (l,_) =>  { 0 .. (length l)})"

definition is_subnode 
 :: "node_t => (node_t * nat) => bool"
where
"is_subnode n pi == (
  let ((ks,rs),i) = pi in
  Node n = (rs!i))"

fun linked_context 
 :: "(left_bound * (node_t * nat) * right_bound) => context_t => bool"
where
"linked_context ni [] = True" |
"linked_context (lb,(n,i),rb) ((plb,pi,prb)#pis) = (
  is_subnode n pi & linked_context (plb,pi,prb) pis)"

definition get_lower_upper_keys_for_node_t
 :: "key list => left_bound => nat => right_bound => (key option * key option)"
where
"get_lower_upper_keys_for_node_t ls lb i rb == (
let l = if (i = 0) then lb else Some(ls ! (i - 1))     in
let u = if (i = (length ls)) then rb else Some(ls ! i) in
(l,u)
)"

definition wellformed_context_1
 :: "ms_t => (left_bound * (node_t * nat) * right_bound) => bool "
where
"wellformed_context_1 ms lbnirb == (
let (lb,((ls,cs),i),rb) = lbnirb in
let (l,u) = get_lower_upper_keys_for_node_t ls lb i rb  in
let node = (Node(ls,cs)) in
wellformed_tree ms node
& i : (subtree_indexes (ls,cs))
& check_keys lb (keys (cs!i)) rb)"

fun wellformed_context :: "context_t => bool" where
"wellformed_context Nil = True" |
"wellformed_context ((lb,((ls,rs),i),rb) # Nil) =
(
let (l,u) = get_lower_upper_keys_for_node_t ls lb i rb  in
(if i = 0 then lb = None else lb = l)
&
(if i = length ls then rb = None else rb = u)
&
wellformed_context_1 (Some Small_root_node_or_leaf) (lb,((ls,rs),i),rb))" |
"wellformed_context (x1 # (x2 # rest)) = (
let (lb,((ls,_),i),rb) = x1 in
let (lb',_,rb') = x2 in
wellformed_context_1 None x1
& 
(let (l,u) = get_lower_upper_keys_for_node_t ls lb i rb  in
 (if i = 0 then lb = lb' else lb = l)
 & (if i = (length ls) then rb = rb' else rb = u)
)
& linked_context x1 (x2#rest)
& wellformed_context (x2#rest)
)
"
(*end wfcontext definition*)


definition dest_ts :: "'f tree_stack => 'f * context_t" where
"dest_ts ts == (case ts of Tree_stack((Focus f),c) => (f,c))"

end
(* tree_stack_src ends here *)
