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
case f of
Inserting_one t \<Rightarrow> (
let rs2 = update_child_at_position n i t in
Inserting_one(t))
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

datatype tree_stack = Tree_stack "focus_t * (node_t * nat) list"

definition step_tree_stack :: "tree_stack \<Rightarrow> tree_stack option" where
"step_tree_stack == FIXME"

end