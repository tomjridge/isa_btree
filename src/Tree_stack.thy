theory Tree_stack
imports Tree
begin

(*begin focus definition*)
datatype One_or_two = 
Inserting_one "Tree"
| Inserting_two "Tree * key * Tree"

type_synonym inserting_two_t =  "Tree * key * Tree"

type_synonym ins_focus_t = One_or_two
(*end focus definition*)

datatype 'f focus_t = Focus 'f

definition split_node :: "node_t \<Rightarrow> inserting_two_t" where
"split_node n == (
let (l,cs) = n in
let n0 = min_node_keys in
let left_ks = take n0 l in
let (k,right_ks) = (case drop n0 l of (k#ks) \<Rightarrow> (k,ks)) in
let left_rs = take (1+n0) cs in
let right_rs = drop (1+n0) cs in
(Node(left_ks,left_rs),k,Node(right_ks,right_rs))
)"

definition update_focus_at_position :: "node_t \<Rightarrow> nat \<Rightarrow> ins_focus_t \<Rightarrow> ins_focus_t" where
"update_focus_at_position n i f == (
let (ks,rs) = n in
case f of
Inserting_one t \<Rightarrow> (
let rs2 = dest_Some(list_replace_1_at_n rs i t) in
Inserting_one(Node(ks,rs2)))
| Inserting_two (tl_,k,tr) \<Rightarrow> (
let ks2 = list_insert_at_n ks i [k] in
let rs2 = list_replace_at_n rs i [tl_,tr] |> dest_Some in
case (length ks2 \<le> max_node_keys) of
True \<Rightarrow> Inserting_one(Node(ks2,rs2))
| False \<Rightarrow> (
Inserting_two(split_node(ks2,rs2))
)
)
)"

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


definition step_tree_stack :: "'f tree_stack \<Rightarrow> ('f tree_stack) option" where
"step_tree_stack ts == (
let (f,stk) = dest_ts ts in
case stk of 
Nil \<Rightarrow> None
| ((lb,(n,i),rb)#xs) \<Rightarrow> (
let f2 = update_focus_at_position n i f in
Some(Tree_stack((Focus f2),xs))
)

)

"

declare [[code abort: key_lt key_le min_node_keys max_node_keys]]
export_code step_tree_stack in Scala module_name Insert_tree_stack file "/tmp/Insert_tree_stack.scala"
end