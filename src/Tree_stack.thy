theory Tree_stack
imports Tree
begin

datatype One_or_two = 
Inserting_one "Tree"
| Inserting_two "Tree * key * Tree"

type_synonym inserting_two_t =  "Tree * key * Tree"

type_synonym focus_t = One_or_two

definition split_node :: "node_t \<Rightarrow> inserting_two_t" where
"split_node == FIXME"

definition update_focus_at_position :: "node_t \<Rightarrow> nat \<Rightarrow> focus_t \<Rightarrow> focus_t" where
"update_focus_at_position n i f == (
let (ks,rs) = n in
case f of
Inserting_one t \<Rightarrow> (
let rs2 = dest_Some(list_replace_1_at_n rs i t) in
Inserting_one(Node(ks,rs2)))
| Inserting_two (tl_,k,tr) \<Rightarrow> (
let ks2 = list_insert_at_n (n|>fst) i [k] in
let rs2 = list_replace_at_n (n|>snd) i [tl_,tr] |> dest_Some in
case (length ks2 \<le> max_node_keys) of
True \<Rightarrow> Inserting_one(Node(ks2,rs2))
| False \<Rightarrow> (
Inserting_two(split_node(ks2,rs2))
)
)
)"

type_synonym context_t = "(node_t * nat) list"

datatype tree_stack = Tree_stack "focus_t * context_t"

definition dest_ts :: "tree_stack \<Rightarrow> focus_t * context_t" where
"dest_ts ts == (case ts of Tree_stack(f,c) \<Rightarrow> (f,c))"

definition step_tree_stack :: "tree_stack \<Rightarrow> tree_stack option" where
"step_tree_stack ts == (
let (f,stk) = dest_ts ts in
case stk of 
Nil \<Rightarrow> None
| ((n,i)#xs) \<Rightarrow> (
let f2 = update_focus_at_position n i f in
Some(Tree_stack(f2,xs))
)

)

"

end