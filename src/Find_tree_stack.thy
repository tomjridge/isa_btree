theory Find_tree_stack imports Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin

(* the search key is not really needed - it is a parameter of all these defns *)
datatype fts_focus_t = Focus "key * key option * Tree * key option"

type_synonym fts_state_t = "fts_focus_t * tree_stack_t"

definition dest_fts_focus :: "fts_focus_t \<Rightarrow> key * key option * Tree * key option" where 
"dest_fts_focus f = (case f of Focus(k,l,t,u) \<Rightarrow> (k,l,t,u))"

lemma dest_fts_focus_def_2: "dest_fts_focus (Focus(k,l,t,u)) = (k,l,t,u)"
apply(simp add: dest_fts_focus_def)
done

definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (Focus(k,None,t,None),Nil)"


(*
definition focus_to_map :: "fts_focus_t \<Rightarrow> (key \<Rightarrow> value_t option)" where
"focus_to_map f = (
  let (k,l,t,u) = dest_fts_focus f in
  tree_to_map t)"
*)

(* wellformed_fts ---------------------------------------- *)

(* tr: link between focus and context?*)
(*begin wf fts focus definition*)

(*
FIXME we also need that, not only is the focus bounded, but any key in the bound must be in the leaves of this tree

its not just that lu is a bound, it is that the subtree is the unique subtree which contains entries from this bound
*)


definition wellformed_fts_focus :: "key \<Rightarrow> ms_t \<Rightarrow> fts_focus_t => bool" where
"wellformed_fts_focus k0 ms f = (
  let (k,l,t,u) = dest_fts_focus f in
  let b1 = wellformed_tree ms t in
  let b2 = check_keys l (set (k#(keys t))) u in
  b1&b2&(k=k0))"

(*end wf fts focus definition*)

(*begin wf fts1 definition*)
(* tr: interaction between focus and context *)
definition wellformed_fts_1 :: "fts_state_t => bool" where
"wellformed_fts_1 fts = (
  let (f,ts) = fts in
  case ts of
  Nil => True
  | cn#xs => (    
    let (k,l,t,u) = dest_fts_focus f in
    let (_,_,rs,i,_) = dest_cnode cn in
    let b0 = (t = rs!i) in
    let b2 = (cnode_to_bound cn = (l,u)) in  (* ensure bounds are linked *)
    b0&b2)
)"
(*end wf fts1 definition*)

(*begin wf fts definition*)
definition wellformed_fts :: "key \<Rightarrow> fts_state_t => bool" where
"wellformed_fts k0 fts = (
  let (f,ts) = fts in
  let ms = ts_to_ms ts in
  wellformed_ts k0 ts
  & wellformed_fts_focus k0 ms f
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
    let cn = Cnode(l,ks,rs,i,u) in
    let ts2 = (cn # ts) in
    let t2 = rs!i in
    let (l2,u2) = cnode_to_bound cn in
    let f2 = Focus(k,l2,t2,u2) in
    Some(f2,ts2) ))
"


(* fts_reass ---------------------------------------- *)
definition fts_reass :: "fts_state_t \<Rightarrow> Tree" where
"fts_reass fts = (
  let (f,ts) = fts in
  let (k,l,t,u) = dest_fts_focus f in
  reass t ts
)"

(* lemmas ------------------------------------------- *)

(*begin find invariant*)
definition invariant_wf_fts :: "bool" where
"invariant_wf_fts = (! k0 fts fts'.
  (step_fts fts = Some (fts')) &
  wellformed_fts k0 fts \<longrightarrow> wellformed_fts k0 fts')
"
(*end find invariant*)

(* prefer lem2; k0 is located in the focus; proof by induction on ts; perhaps better to do this for the step case explicitly?*)
definition lem1 :: "bool" where
"lem1 = (
  ! k0 f ts.
  let (k,l,t,u) = dest_fts_focus f in
  let (ks,rs) = ts_to_t0 ts |> dest_Some in
  (ts \<noteq> []) &
  wellformed_fts k0 (f,ts) & 
  k0 : tree_to_map (Node(ks,rs)) |> dom \<longrightarrow>
  k0 : tree_to_map t |> dom 
)"

definition lem2 :: "bool" where
"lem2 = (! k0 f ts f' ts'.
  let (_,_,t,_) = dest_fts_focus f in
  let (_,_,t',_) = dest_fts_focus f' in
  wellformed_fts k0 (f,ts) &
  k0 : (t|>tree_to_map|>dom) &
  (step_fts (f,ts) = Some(f',ts')) \<longrightarrow>
  k0 : (t'|>tree_to_map|>dom)
)"


definition lemma_fts_reass :: "bool" where
"lemma_fts_reass = (! k0 f ts.
  wellformed_fts k0 (f,ts) \<longrightarrow> (
  let (k,_,t,_) = dest_fts_focus f in
  ? xs zs. 
    let t' = fts_reass (f,ts) in 
    (t' |> tree_to_leaves = xs@(tree_to_leaves t)@zs) & 
    (k0 : tree_to_map t' |> dom \<longrightarrow> k0 : tree_to_map t |> dom))
)"  



end
