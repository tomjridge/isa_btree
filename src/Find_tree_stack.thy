theory Find_tree_stack imports Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin

(* tr: we return a pair of a focus and the context; the focus is just
   the tree at the position; at the end of Find, this is
   guaranteed to be a leaf; also include the key we are looking
   for; also include bounds on the keys that we may find
*)


datatype fts_state_t = Fts_state "key * Tree * tree_stack_t"  (* k,t,ts *)
definition dest_fts_state_t :: "fts_state_t \<Rightarrow> key * Tree * tree_stack_t" where 
"dest_fts_state_t fts = (case fts of Fts_state (k,t,ts) \<Rightarrow> (k,t,ts))"

(* FIXME tr: prefer to bring types into line with scala? *)


definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (Fts_state (k,t,Nil))"

(* wellformed_fts ---------------------------------------- *)

(* tr: link between focus and context?*)
(*begin wf fts focus definition*)
definition wellformed_fts_focus :: "ms_t => Tree => bool" where
"wellformed_fts_focus ms t =
  (wellformed_tree ms t)"
(*end wf fts focus definition*)

(*begin wf fts1 definition*)
definition wellformed_fts_1 :: "fts_state_t => bool" where
"wellformed_fts_1 fts == (
  let (k,t,ts) = dest_fts_state_t fts in
  case ts of
  Nil => True
  | x#xs => (
    let (n,i,x) = dest_cnode_t x in
    let (l,u) = dest_xtra_t x in
    let b1 = check_keys l [k] u in
    let b2 = t = (let (ks,rs) = n in rs!i) in
    b1&b2))
"
(*end wf fts1 definition*)

(*begin wf fts definition*)
definition wellformed_fts :: "fts_state_t => bool" where
"wellformed_fts fts = (
  let (k,t,ts) = dest_fts_state_t fts in
  let ms = if (ts = Nil) then (Some Small_root_node_or_leaf) else None in
  wellformed_fts_focus ms t
  & wellformed_context ts
  & wellformed_fts_1 fts)"
(*end wf fts definition*)


(* step_fts ---------------------------------------- *)

(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (k,t,ts) = dest_fts_state_t fts in
  let parent_bounds = (
    case ts of Nil \<Rightarrow> Xtra(None,None) | cn# a_ \<Rightarrow> (let (n,i,x) = dest_cnode_t cn in x)) in
  case (t :: Tree) of
  Leaf kvs => None
  | Node(ks,rs) => (
    let i = search_key_to_index ks k in
    let xtra :: xtra_t = (
      let (l1,u1) = get_lu_for_child ((ks,rs),i) in
      let (pb_l,pb_u) = dest_xtra_t parent_bounds in
      let l2 = (case l1 of None \<Rightarrow> pb_l | _ \<Rightarrow> l1) in
      let u2 = (case u1 of None \<Rightarrow> pb_u | _ \<Rightarrow> u1) in
      Xtra(l2,u2))
    in
    let cn :: cnode_t = Cnode((ks,rs),i,xtra) in
    let ts2 :: cnode_t list = (cn # ts) in
    Some(Fts_state(k,rs!i,ts2)) ))
"


(* old

(*begin f focus definition*)
type_synonym f_focus_t = "key * Tree"
(*end f focus definition*)

type_synonym f_tree_stack = "f_focus_t tree_stack"

definition dest_f_tree_stack 
 :: "f_tree_stack => (key * Tree * context_t)"
where
"dest_f_tree_stack fts = (
case fts of (Tree_stack (Focus (k,t), ctx)) => (k,t,ctx))
"

definition fts_to_map1
 :: "f_tree_stack => (key,value_t) map"
where
"fts_to_map1 fts = (
let (_,t,ctx) = dest_f_tree_stack fts in
tree_to_map t ++ ctx_to_map(ctx)
)"

function fts_to_tree
 :: "f_tree_stack => Tree"
where
"fts_to_tree (Tree_stack(Focus f,[])) = (
let (k,t) = f in
t)" |
"fts_to_tree (Tree_stack(Focus f,(_,((ks,rs),i),_)#ctx_t)) = (
let (k,t) = f in
let rs' = the (list_replace_1_at_n rs i t) in
fts_to_tree (Tree_stack(Focus (k,Node(ks,rs')),ctx_t))
)"
by pat_completeness auto
termination fts_to_tree
 apply (relation "measure (\<lambda>ts. case ts of (Tree_stack(Focus _,ctx)) => length ctx)")
 apply auto
done

definition fts_to_map
 :: "f_tree_stack => (key,value_t) map"
where
"fts_to_map fts = (
fts |> fts_to_tree |> tree_to_map
)"


*)

declare [[code abort: key_lt]]
export_code step_fts in Scala module_name Find_tree_stack file "/tmp/Find_tree_stack.scala"



end
