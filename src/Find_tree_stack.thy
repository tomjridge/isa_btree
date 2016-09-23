theory Find_tree_stack imports Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin


record fts_focus_t = 
  fts_key :: key
  fts_l :: "key option"
  fts_t :: Tree
  fts_u :: "key option"

type_synonym fts_state_t = "fts_focus_t * tree_stack_t"

definition dest_fts_focus :: "fts_focus_t \<Rightarrow> key * key option * Tree * key option" where 
"dest_fts_focus fts = (fts|>fts_key,fts|>fts_l,fts|>fts_t,fts|>fts_u)"

lemma dest_fts_focus_def_2: "dest_fts_focus \<lparr> fts_key=k, fts_l=l, fts_t=t, fts_u=u\<rparr>
 = (k,l,t,u)"
apply(simp add: dest_fts_focus_def)
by (simp add: rev_apply_def)

definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (\<lparr> fts_key=k,fts_l=None,fts_t=t,fts_u=None \<rparr>,Nil)"


(* wellformed_fts ---------------------------------------- *)

(* tr: link between focus and context?*)
(*begin wf fts focus definition*)

definition wellformed_fts_focus :: "ms_t \<Rightarrow> fts_focus_t => bool" where
"wellformed_fts_focus ms f = (
  let (k,l,t,u) = dest_fts_focus f in
  let b1 = wellformed_tree ms t in
  let b2 = check_keys l (k#(keys t)) u in
  b1&b2)"

(*end wf fts focus definition*)

(*begin wf fts1 definition*)
(* tr: interaction between focus and context *)
definition wellformed_fts_1 :: "fts_state_t => bool" where
"wellformed_fts_1 fts == (
  let (f,ts) = fts in
  case ts of
  Nil => True
  | cn#xs => (    
    let (k,l,t,u) = dest_fts_focus f in
    let (n,i,b) = dest_cnode_t cn in
    let (ks,rs) = n in
    let b0 = (t = rs!i) in
    let b2 = (cnode_to_bound cn = (l,u)) in  (* ensure bounds are linked *)
    b0&b2))
"
(*end wf fts1 definition*)

(*begin wf fts definition*)
definition wellformed_fts :: "fts_state_t => bool" where
"wellformed_fts fts = (
  let (f,ts) = fts in
  let ms = ts_to_ms ts in
  wellformed_context ts
  & wellformed_fts_focus ms f
  & wellformed_fts_1 fts)"
(*end wf fts definition*)


(* step_fts ---------------------------------------- *)

(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (f,ts) = fts in
  let (k,l,t,u) = dest_fts_focus f in
  case t of Leaf kvs => None
  | Node(ks,rs) => (
    let i = search_key_to_index ks k in
    let cn = Cnode((ks,rs),i,(l,u)) in
    let ts2 = (cn # ts) in
    let t2 = rs!i in
    let (l2,u2) = cnode_to_bound cn in
    let f2 = \<lparr> fts_key=k,fts_l=l2,fts_t=t2,fts_u=u2 \<rparr> in
    Some(f2,ts2) ))
"

declare [[code abort: key_lt]]
export_code step_fts in Scala module_name Find_tree_stack file "/tmp/Find_tree_stack.scala"



end
