theory Find_tree_stack imports Prelude Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin

(* the search key is not really needed - it is a parameter of all these defns; the xs and zs are the other leaves not in t *)
datatype fts_focus_t = Focus "key * leaves_t * key option * Tree * key option * leaves_t" (* k,xs,l,t,u,zs *)


type_synonym fts_state_t = "fts_focus_t * tree_stack_t"

definition dest_fts_focus :: "fts_focus_t \<Rightarrow> key * leaves_t * key option * Tree * key option * leaves_t" where 
"dest_fts_focus f = (case f of Focus(k,xs,l,t,u,zs) \<Rightarrow> (k,xs,l,t,u,zs))"

lemma dest_fts_focus_def_2: "dest_fts_focus (Focus(k,xs,l,t,u,zs)) = (k,xs,l,t,u,zs)"
apply(simp add: dest_fts_focus_def)
done

definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (Focus(k,[],None,t,None,[]),[])"


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
    let (_,_,_,rs,i,_,_) = dest_cnode cn in
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


definition indexes_to_leaves :: "Tree list \<Rightarrow> nat list \<Rightarrow> leaves_t" where
"indexes_to_leaves rs is = (is |> List.map (% j. tree_to_leaves (rs!j)) |> List.concat)"

(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (f,ts) = fts in
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  case t of Leaf kvs => None
  | Node(ks,rs) => (
    let i = search_key_to_index ks k in
    let cn = Cnode(xs,l,ks,rs,i,u,zs) in
    let ts2 = (cn # ts) in
    let t2 = rs!i in
    let (l2,u2) = cnode_to_bound cn in
    let xs' = (from_to 0 (i-1)) |> indexes_to_leaves rs in
    let zs' = (from_to (i+1) (ks_to_max_child_index ks)) |> indexes_to_leaves rs in
    let f2 = Focus(k,xs@xs',l2,t2,u2,zs'@zs) in
    Some(f2,ts2) ))
"


(* fts_reass ---------------------------------------- *)
definition fts_reass :: "fts_state_t \<Rightarrow> Tree" where
"fts_reass fts = (
  let (f,ts) = fts in
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  reass t ts
)"

(* invariant ----------------------------------------- *)

definition fts_invariant :: "(fts_state_t \<Rightarrow> bool) \<Rightarrow> bool" where
"fts_invariant P = (
  ! fts fts'. 
    (step_fts fts = Some fts') & P fts \<longrightarrow> P fts'  
)"


(* lemmas ------------------------------------------- *)

(*begin find invariant*)
definition invariant_wf_fts :: "bool" where
"invariant_wf_fts = (! k0 P.
  ((% fts. wellformed_fts k0 fts) = P) \<longrightarrow>
  fts_invariant P
)"
(*end find invariant*)

(* prefer lem2; k0 is located in the focus; proof by induction on ts; perhaps better to do this for the step case explicitly?*)
(*
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
*)

(* for find, the following is all we need, but may be preferable to prove something stronger needed
for insert and delete *)
(*
definition lem2 :: "bool" where you all very much for coming the other night: it was great to see you. Sadly we got a bit carried away by the liberation of not having a baby-sitter to get back to. Did at least
"lem2 = (! k0 f ts f' ts'.
  let (_,_,t,_) = dest_fts_focus f in
  let (_,_,t',_) = dest_fts_focus f' in
  wellformed_fts k0 (f,ts) &
  k0 : (t|>tree_to_map|>dom) &
  (step_fts (f,ts) = Some(f',ts')) \<longrightarrow>
  k0 : (t'|>tree_to_map|>dom)
)"
*)

(* want to talk about all the leaves... *)
(*
definition lem3 :: "bool" where
"lem3 = (! k0 f ts f' ts'.
  let (_,_,t,_) = dest_fts_focus f in
  let (_,_,t',_) = dest_fts_focus f' in
  wellformed_fts k0 (f,ts) &
  k0 : (t|>tree_to_map|>dom) &
  (step_fts (f,ts) = Some(f',ts')) \<longrightarrow>
  k0 : (t'|>tree_to_map|>dom)
)"
*)

(* this still talks about the focus
definition lem5 :: "bool" where
"lem5 = (! k0 f ts.
  wellformed_fts k0 (f,ts) \<longrightarrow> (
  let (k,_,t,_) = dest_fts_focus f in
  ? xs zs. 
    let t' = fts_reass (f,ts) in 
    (t' |> tree_to_leaves = xs@(tree_to_leaves t)@zs) & 
    (k0 : tree_to_map t' |> dom \<longrightarrow> k0 : tree_to_map t |> dom))
)"
*)

(* the lu separate leaves of focus from other leaves of reass *)
definition lem6 :: "bool" where
"lem6 = (! k0 f ts.
  wellformed_fts k0 (f,ts) \<longrightarrow> (
    let (k,xs,l,t,u,zs) = dest_fts_focus f in
    ? xs zs. (
      let t' = fts_reass (f,ts) in 
      (t' |> tree_to_leaves = xs@(tree_to_leaves t)@zs) & 
      (* note None is functioning as +-infinity here, rather than <<dont care>> *)
      check_keys_2 (xs |> leaves_to_map|>dom) l {} u (zs|>leaves_to_map|>dom)))
)"  


(* following should say that if we start with xs=zs={}, then the xs@(leaves of the focus)@zs are the leaves
of the original tree - ie the leaves are invariant; then we know the ordering on xs,leaves,zs, and we
also know the bound lu 

first show that step preserves wellformedness; then show it preserves leaves and check_keys_2

*)

definition lem7 :: "bool" where
"lem7 = (! f trns k0 t0 ts0 f0.
  (trns = { (s,s'). case s of None \<Rightarrow> s'=None | Some fts \<Rightarrow> step_fts fts = s' }) &
  f : (trace_set trns) &
  (tree_to_fts k0 t0 = (f0,ts0)) &
  (Some(f0,ts0) = f 0) 
  \<longrightarrow> (
  ! (n::nat). case f n of None \<Rightarrow> True | Some fn \<Rightarrow> (
  let (f_n,ts_n) = fn in
  let (k,xs,l,t,u,zs) = dest_fts_focus f0 in
  let (k,xs',l',t',u',zs') = dest_fts_focus f_n in
  let ks' = t'|>tree_to_map|>dom in (
  wellformed_fts k0 (f_n,ts_n)) \<longrightarrow> 
  check_keys_2 (xs'|>leaves_to_map|>dom) l' ks' u' (zs'|>leaves_to_map|>dom) &
  (xs'@(t'|>tree_to_leaves)@zs' = xs@(t|>tree_to_leaves)@zs))) 
)"

(* FIXME shouldn't this be part of wf_fts_focus? *)
definition focus_to_check_keys_2 :: "fts_focus_t \<Rightarrow> bool" where
"focus_to_check_keys_2 f = (
  let (k,xs',l',t',u',zs') = dest_fts_focus f in
  check_keys_2 (xs'|>leaves_to_map|>dom) l' ((t'|>tree_to_map|>dom)) u' (zs'|>leaves_to_map|>dom)
)"

definition focus_to_leaves :: "fts_focus_t \<Rightarrow> leaves_t" where
"focus_to_leaves f = (
  let (k,xs,l,t,u,zs) = dest_fts_focus f in
  xs@(t|>tree_to_leaves)@zs
)"

definition lem8 :: "bool" where
"lem8 = (! ls P Q.
  ((% fts. let (f,ts) = fts in focus_to_check_keys_2 f) = P) &
  ((% fts. let (f,ts) = fts in focus_to_leaves f = ls) = Q) \<longrightarrow> 
  fts_invariant (% fts. P fts & Q fts)
)"


(* now we need a nice way of combining the invariants: given that we know wf is invariant, show P and Q assuming wf *)
definition lem9 :: "bool" where
"lem9 = (! k0 ls P Q W.
  ((% fts. wellformed_fts k0 fts) = W) &
  ((% fts. let (f,ts) = fts in focus_to_check_keys_2 f) = P) &
  ((% fts. let (f,ts) = fts in focus_to_leaves f = ls) = Q) \<longrightarrow>
  fts_invariant (% fts. W fts)  \<longrightarrow>
  fts_invariant (% fts. W fts & P fts & Q fts)
)"

(* how to get from lem9 to correctness of eg find? well, we have k bounded and the leaves are the same, so the maps are the same, and equal... *)

lemma btree_find_correct: "! trns f k0 t0 f0 ts0 v0.
(trns = { (s,s'). case s of None \<Rightarrow> s'=None | Some fts \<Rightarrow> step_fts fts = s' }) &
f : (trace_set trns) \<longrightarrow> (
(tree_to_fts k0 t0 = (f0,ts0)) &
(Some(f0,ts0) = f 0) &
(tree_to_map t0 k0 = v0) \<longrightarrow> (
! n f_n ts_n. (f (n::nat) = Some(f_n,ts_n)) \<longrightarrow>
(let (k,xs,l,t,u,zs) = dest_fts_focus f_n in
(tree_to_map t k0 = v0))))
"
sorry

(* FIXME next step to look at insert, using a lem7-like lemma *)


end
