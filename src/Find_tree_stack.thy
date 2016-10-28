theory Find_tree_stack imports Prelude Tree_stack "~~/src/HOL/Library/Code_Target_Nat" begin


(* the search key is not really needed - it is a parameter of all these defns; the xs and zs are the other leaves not in t *)
datatype fts_focus_t = Focus core_t

type_synonym fts_state_t = "fts_focus_t * tree_stack_t"

definition dest_fts_focus :: "fts_focus_t \<Rightarrow> core_t" where 
"dest_fts_focus f = (case f of Focus(c) \<Rightarrow> c)"

lemma [simp]: "(Focus c) |> dest_fts_focus = c"
 apply(simp add: rev_apply_def dest_fts_focus_def)
 done

definition tree_to_fts :: "key => Tree => fts_state_t" where
"tree_to_fts k t = (Focus( mk_core (k,[],None,t,None,[])), [])"


(* wellformed_fts ---------------------------------------- *)

definition wellformed_fts_focus :: "key \<Rightarrow> ms_t \<Rightarrow> fts_focus_t => bool" where
"wellformed_fts_focus k0 ms f = (wellformed_core k0 ms (f|>dest_fts_focus))"

(*begin wf fts1 definition*)
(* tr: interaction between focus and context *)
definition wellformed_fts_1 :: "fts_state_t => bool" where
"wellformed_fts_1 fts = (
  let (f,ts) = fts in
  case ts of
  Nil => True
  | cn#xs => (    
    let (c1,c2) = cn in
    let (k,xs,l,t,u,zs) = f|>dest_fts_focus|>dest_core in
    let (_,rs,i) = c2|>dest_ksrsi in
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

definition split_list :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list * 'a * 'a list)" where
"split_list rs i = (
  let valid = from_to 0 (length rs -1) in (* valid indexes *)
  let xs = valid |> filter (% n. n < i) in
  let zs = valid |> filter (% n. n > i) in
  (xs|>map (% j. rs!j),
   rs!i,
   zs|>map (% j. rs!j))
)"

(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (f,ts) = fts in
  let (k,xs,l,t,u,zs) = f|>dest_fts_focus|>dest_core in
  case t of Leaf kvs => None
  | Node(ks,rs) => (
    let i = search_key_to_index ks k in
    (* new tree stack ----- *)
    let cn = (
      let core = mk_core (k,xs,l,t,u,zs) in
      let ksrsi = (| cc_ks=ks,cc_rs=rs,cc_i=i |) in
      (core,ksrsi))
    in
    let ts2 = (cn # ts) in
    (* new focus ----- *)
    let (tsx,t2,tsy) = split_list rs i in 
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
  let (k,xs,l,t,u,zs) = f|>dest_fts_focus|>dest_core in
  reass t ts
)"

(* fts_invariant ----------------------------------------- *)

definition fts_trans :: "fts_state_t trans_t" where
"fts_trans = { (fts,fts'). (step_fts fts = Some fts') }"

(*
definition fts_invariant :: "(fts_state_t \<Rightarrow> bool) \<Rightarrow> bool" where
"fts_invariant P = (invariant fts_trans P)"
*)

(* lemmas ------------------------------------------- *)

(* wf_fts is invariant *)
(*begin find invariant*)
definition invariant_wf_fts_lem :: "bool" where
"invariant_wf_fts_lem = (! k0 P. ((% fts. wellformed_fts k0 fts) = P) \<longrightarrow> invariant fts_trans P)"
(*end find invariant*)

definition focus_to_leaves :: "fts_focus_t \<Rightarrow> leaves_t" where
"focus_to_leaves f = (
  let (k,xs,l,t,u,zs) = f|>dest_fts_focus|>dest_core in
  xs@(t|>tree_to_leaves)@zs
)"

(* the focus leaves are invariant *)
definition invariant_leaves_lem :: "bool" where
"invariant_leaves_lem = (
  ! ls P. ((% fts. focus_to_leaves (fst fts) = ls) = P) \<longrightarrow> invariant fts_trans P )"

(* this is enough to ensure that the result of find is the correct leaf *)

end
