theory Tree_stack
imports Tree
begin

(*begin focus definition*)
datatype 'f focus_t = Focus 'f
(*end focus definition*)

(*begin context definition*)
type_synonym left_bound = "key option"

type_synonym right_bound = "key option"

type_synonym context_t = "(left_bound * (node_t * nat) * right_bound) list"
(*end context definition*)

(*begin treestack definition*)
datatype 'f tree_stack = Tree_stack "'f focus_t * context_t"
(*end treestack definition*)

(*begin wfcontext definition*)
definition subtree_indexes :: "node_t => nat set" where
"subtree_indexes n == (
  case n of (l,_) =>  { 0 .. (length l)})"

definition is_subnode :: "(node_t * nat) => (node_t * nat) => bool" where
"is_subnode ni pi == (
  let (n,_) = ni in
  let ((ks,rs),i) = pi in
  Node n = (rs!i))"
                                        
fun linked_context :: "(left_bound * (node_t * nat) * right_bound) => context_t => bool" where
"linked_context ni [] = True" |
"linked_context (lb,ni,rb) ((plb,pi,prb)#pis) = (
  is_subnode ni pi & linked_context (plb,pi,prb) pis)"

definition wellformed_context_1 :: "rmbs_t => (left_bound * (node_t * nat) * right_bound) => bool " where
"wellformed_context_1 rmbs lbnirb == (
let (lb,((l,cs),i),rb) = lbnirb in
let node = (Node(l,cs)) in(
wellformed_tree rmbs node
& i : (subtree_indexes (l,cs)))
& check_keys lb (keys node) rb)"

definition get_lower_upper_keys_for_node_t :: "key list => left_bound => nat => right_bound => (key option * key option)" where
"get_lower_upper_keys_for_node_t ls lb i rb == (
let l = if (i = 0) then lb else Some(ls ! (i - 1))     in
let u = if (i = (length ls)) then rb else Some(ls ! i) in
(l,u)
)"

fun wellformed_context :: "context_t => bool" where
"wellformed_context Nil = True" |
"wellformed_context (x # Nil) = wellformed_context_1 (Rmbs True) x" |
"wellformed_context (x1 # (x2 # rest)) = (
let (lb,((ls,_),i),rb) = x2 in
let (l2,u2) = get_lower_upper_keys_for_node_t ls lb i rb in
let (l1,_,u1) = x1 in
wellformed_context_1 (Rmbs False) x1
& (l1,u1) = (l2,u2)
& linked_context x1 (x2#rest)
& wellformed_context (x2#rest)
)
"
(*end wfcontext definition*)


definition dest_ts :: "'f tree_stack \<Rightarrow> 'f * context_t" where
"dest_ts ts == (case ts of Tree_stack((Focus f),c) \<Rightarrow> (f,c))"
end