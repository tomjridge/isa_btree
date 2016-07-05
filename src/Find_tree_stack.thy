theory Find_tree_stack
imports Util Constants Tree Key_value Tree_stack "~~/src/HOL/Library/Code_Target_Nat"
begin

(* tr: we return a pair of a focus and the context; the focus is just
   the tree at the position; at the end of Find, this is
   guaranteed to be a leaf; also include the key we are looking
   for; also include bounds on the keys that we may find
*)

(*begin f focus definition*)
type_synonym f_focus_t = "key * Tree"
(*end f focus definition*)

type_synonym f_tree_stack = "f_focus_t tree_stack"

definition dest_f_tree_stack :: "f_tree_stack => (key * Tree * context_t)" where
"dest_f_tree_stack fts = (case fts of (Tree_stack (Focus (k,t), ctx)) => (k,t,ctx))"

definition tree_to_fts :: "key => Tree => f_tree_stack" where
"tree_to_fts k t == (
Tree_stack (Focus (k,t),Nil))"

(* tr: link between focus and context?*)
definition wellformed_fts_focus :: "ms_t => Tree => bool" where
"wellformed_fts_focus ms t == (
wellformed_tree ms t)"

definition wellformed_fts_1 :: "f_tree_stack => bool" where
"wellformed_fts_1 fts == (
let (k,t,ctx) = dest_f_tree_stack fts in
(case ctx of
Nil => True
| x#xs =>
 let (lb,((ks,rs),i),rb) = x in
 let (l,u) = get_lower_upper_keys_for_node_t ks lb i rb in
 (t = rs!i) (*tr: the keys of the focus are bounded by constraints on context*)
 &
 (check_keys l [k] u)
))"

definition wellformed_fts :: "f_tree_stack => bool" where
"wellformed_fts fts == (
let (k,t,ctx) = dest_f_tree_stack fts in
let ms = if (ctx = Nil) then (Some Small_root_node_or_leaf) else None in
wellformed_fts_focus ms t
& wellformed_context ctx
& wellformed_fts_1 fts)"

(*tr: stops when gets to leaf; no "errors"*)
definition step_fts :: "f_tree_stack => f_tree_stack option" where
"step_fts fts == (
let (k,t,ctx) = dest_f_tree_stack fts in
let (lb,rb) =
 case ctx of Nil => (None,None)
 | (lb,_,rb)#_ => (lb, rb) 
in
(case t of
Leaf _ => None
| Node(ks,rs) =>
 let i = search_key_to_index ks k in
 let (l,u) = get_lower_upper_keys_for_node_t ks lb i rb in
 let ctx2 = (l,((ks,rs),i),u)#ctx in
 Some(Tree_stack(Focus(k,(rs!i)),ctx2))
))"

declare [[code abort: key_lt]]
export_code step_fts in Scala module_name Find_tree_stack file "/tmp/Find_tree_stack.scala"
end

