theory Find_tree_stack imports Prelude Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin


(* FIXME use a record type for this *)

(* the search key is not really needed - it is a parameter of all these defns; the xs and zs are the other leaves not in t *)
datatype fts_focus_t = Focus core_t

type_synonym fts_state_t = "fts_focus_t * tree_stack_t"

(* this is OK for a simp *)
definition dest_fts_focus :: "fts_focus_t \<Rightarrow> dest_core_t" where 
"dest_fts_focus f = (case f of Focus(c) \<Rightarrow> dest_core c)"

definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (Focus( mk_core (k,[],None,t,None,[])), [])"


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
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  let b1 = wellformed_tree ms t in
  let b2 = check_keys_2 (xs|>leaves_to_map|>dom) l (set (k#(keys t))) u (zs|>leaves_to_map|>dom) in
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
    let (k,xs,l,t,u,zs) = dest_fts_focus f in
    let (rs,i) = (cn|>cc_rs,cn|>cc_i) in
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

definition indexes_to_trees :: "Tree list \<Rightarrow> nat list \<Rightarrow> Tree list" where
"indexes_to_trees rs is = (is |> List.map (% i. rs!i))"

(*
definition indexes_to_leaves :: "Tree list \<Rightarrow> nat list \<Rightarrow> leaves_t" where
"indexes_to_leaves rs is = (indexes_to_trees rs is |> List.map tree_to_leaves |> List.concat)"
*)


(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (f,ts) = fts in
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  case t of Leaf kvs => None
  | Node(ks,rs) => (
    let i = search_key_to_index ks k in
    let core = mk_core (k,xs,l,t,u,zs) in
    let cn = core_t.extend core (| cc_ks=ks,cc_rs=rs,cc_i=i |) in
    let ts2 = (cn # ts) in
    let (isx,i,isy) = (from_to 0 (i-1), i, from_to (i+1) (ks_to_max_child_index ks)) in 
    let (tsx,t2,tsy) = (indexes_to_trees rs isx, rs!i, indexes_to_trees rs isy) in 
    let (xs',zs') = 
      (tsx |> List.map tree_to_leaves |> List.concat, tsy |> List.map tree_to_leaves |> List.concat) 
    in 
    let (l2,u2) = cnode_to_bound cn in
    let f2 = Focus( mk_core(k,xs@xs',l2,t2,u2,zs'@zs)) in
    Some(f2,ts2) ))
"


(* fts_reass ---------------------------------------- *)
definition fts_reass :: "fts_state_t \<Rightarrow> Tree" where
"fts_reass fts = (
  let (f,ts) = fts in
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  reass t ts
)"

(* fts_invariant ----------------------------------------- *)

definition fts_invariant :: "(fts_state_t \<Rightarrow> bool) \<Rightarrow> bool" where
"fts_invariant P = (! fts fts'. (step_fts fts = Some fts') & P fts \<longrightarrow> P fts' )"


(* lemmas ------------------------------------------- *)

(* wf_fts is invariant *)
(*begin find invariant*)
definition invariant_wf_fts_b :: "bool" where
"invariant_wf_fts_b = (! k0 P.
  ((% fts. wellformed_fts k0 fts) = P) \<longrightarrow>
  fts_invariant P
)"
(*end find invariant*)

definition focus_to_leaves :: "fts_focus_t \<Rightarrow> leaves_t" where
"focus_to_leaves f = (
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  xs@(t|>tree_to_leaves)@zs
)"

(* the focus leaves are invariant *)
definition invariant_leaves_b :: "bool" where
"invariant_leaves_b = (! ls P.
  ((% fts. focus_to_leaves (fst fts) = ls) = P) \<longrightarrow>
  fts_invariant P )"

(* this is enough to ensure that the result of find is the correct leaf *)

end
