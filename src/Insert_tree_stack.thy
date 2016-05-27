theory Insert_tree_stack
imports Tree_stack
begin

(*begin ins focus definition*)
datatype One_or_two = 
Inserting_one "Tree"
| Inserting_two "Tree * key * Tree"

type_synonym inserting_two_t =  "Tree * key * Tree"

type_synonym ins_focus_t = One_or_two
(*end ins focus definition*)

(*begin ins_tree_stack definition*)
type_synonym ins_tree_stack = "ins_focus_t tree_stack"
(*end ins_tree_stack definition*)

(*begin step ins_tree_stack*)
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


definition step_up :: "ins_tree_stack \<Rightarrow> (ins_tree_stack) option" where
"step_up ts == (
let (f,stk) = dest_ts ts in
case stk of 
Nil \<Rightarrow> None
| ((lb,(n,i),rb)#xs) \<Rightarrow> (
let f2 = update_focus_at_position n i f in
Some(Tree_stack((Focus f2),xs))
)
)
"

definition ins_step_tree_stack :: "ins_tree_stack \<Rightarrow> (ins_tree_stack) option" where
"ins_step_tree_stack ts == (
step_up ts)
"

declare [[code abort: key_lt key_le min_node_keys max_node_keys]]
export_code ins_step_tree_stack in Scala module_name Insert_tree_stack file "/tmp/Insert_tree_stack.scala"
(*end step ins_tree_stack*)

(*begin wffocus definition*)
definition wellformed_focus :: "ins_focus_t => bool => bool" where
"wellformed_focus f stack_empty == (
case f of
Inserting_one t => (wellformed_tree (Rmbs stack_empty) t)
| Inserting_two (tl_,k0,tr) => (
wellformed_tree (Rmbs False) tl_ 
& wellformed_tree (Rmbs False) tr
& check_keys None (keys (tl_)) (Some k0)
& check_keys (Some k0) (keys tr) None)
)"
(*end wffocus definition*)

(*begin wfts1 definition*)
definition wellformed_ts_1 :: "ins_tree_stack => bool" where
"wellformed_ts_1 ts == (
let (f,stk) = dest_ts ts in
(case stk of 

Nil => (True) (* Nil - focus is wf *)

| ((lb,((l,cs),i),rb)#nis) => (
let (kl,kr) = get_lower_upper_keys_for_node_t l lb i rb in
case f of
Inserting_one t => (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 = (height (cs!i) = height t) in
let b4 = (check_keys kl (keys t) kr)
in
(* keys ordered *)
let b5 = True in
let wf = b1&b2&b3&b4&b5 in
wf
)  (* Inserting_one *)

| Inserting_two (tl_,k0,tr) => (
let b1 = True in
let b2 = True in
let b3 = (
  let h = height (cs!i) in
  (height tl_ = h) & (height tr = h)
)
in
(* keys consistent *)
let b4 = (
  check_keys kl (keys tl_) (Some k0)
  & check_keys (Some k0) (keys tr) kr
)
in
(* keys ordered *)
let b5 = (
check_keys kl [k0] kr
)
in
let wf = b1&b2&b3&b4&b5 in
wf
)

)


))"
(*end wfts1 definition*)

(*begin wftreestack definition*)
definition wellformed_ts :: "ins_tree_stack => bool" where
"wellformed_ts ts == (
let (f,stk) = dest_ts ts in
wellformed_focus f (stk=[])
& wellformed_context stk
& wellformed_ts_1 ts)"
(*end wftreestack definition*)

end
