theory Tree_stack
imports Tree
begin

(*begin focus definition*)
datatype One_or_two = 
Inserting_one "Tree"
| Inserting_two "Tree * key * Tree"

type_synonym inserting_two_t =  "Tree * key * Tree"

type_synonym focus_t = One_or_two
(*end focus definition*)

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

definition update_focus_at_position :: "node_t \<Rightarrow> nat \<Rightarrow> focus_t \<Rightarrow> focus_t" where
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
datatype tree_stack = Tree_stack "focus_t * context_t"
(*end treestack definition*)

definition dest_ts :: "tree_stack \<Rightarrow> focus_t * context_t" where
"dest_ts ts == (case ts of Tree_stack(f,c) \<Rightarrow> (f,c))"

definition step_tree_stack :: "tree_stack \<Rightarrow> tree_stack option" where
"step_tree_stack ts == (
let (f,stk) = dest_ts ts in
case stk of 
Nil \<Rightarrow> None
| ((lb,(n,i),rb)#xs) \<Rightarrow> (
let f2 = update_focus_at_position n i f in
Some(Tree_stack(f2,xs))
)

)

"

declare [[code abort: key_lt key_le min_node_keys max_node_keys]]
export_code step_tree_stack in Scala module_name Insert_tree_stack file "/tmp/Insert_tree_stack.scala"
end