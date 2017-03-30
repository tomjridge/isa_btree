theory Find_tree_stack 
imports Tree_stack 
begin

(* the search key is not really needed - it is a parameter of all these defns; the xs and zs are the other leaves not in t *)
type_synonym fts_focus_t = "Tree core_t"
  
datatype fts_state_t = Fts_state "fts_focus_t * tree_stack_t"

definition dest_fts_state :: "fts_state_t \<Rightarrow> fts_focus_t * tree_stack_t" where
"dest_fts_state s = (case s of Fts_state x \<Rightarrow> x)"


(* wellformed_fts ---------------------------------------- *)

definition wellformed_fts_focus :: "ms_t \<Rightarrow> fts_focus_t => bool" where
"wellformed_fts_focus ms f = assert_true (ms,f) (
  let t = f|>f_t in
  wf_core (t|>tree_to_keys) f &
  wellformed_tree ms t
)"

(* tr: interaction between focus and context *)
definition wellformed_fts_1 :: "fts_state_t => bool" where
"wellformed_fts_1 fts = assert_true fts (
  let (c,ts) = fts|>dest_fts_state in
  case ts of
  Nil => True
  | p#xs => (mk_child p = c)
)"

definition wellformed_fts :: "fts_state_t => bool" where
"wellformed_fts fts = assert_true fts (
  let (f,ts) = fts|>dest_fts_state in
  let ms = ts_to_ms ts in
  wellformed_ts ts
  & wellformed_fts_focus ms f
  & wellformed_fts_1 fts)"



(* step_fts ---------------------------------------- *)


definition mk_fts_state :: "key => Tree => fts_state_t" where
"mk_fts_state k t = (
  let f = \<lparr>f_k=k, f_tss1=[], f_kl=None,f_t=t,f_ku=None,f_tss2=[] \<rparr> in
  Fts_state(f,[])
)"

(*tr: stops when gets to leaf; no "errors"*)
(*begin find step definition*)
definition step_fts :: "fts_state_t => fts_state_t option" where
"step_fts fts = (
  let (f,xs) = fts|>dest_fts_state in
  case (f|>f_t) of Leaf kvs => None
  | Node(ks,rs) => (
    (* new frame - just push the focus.. with ks,rs *)
    let p = f|>with_t (% _. (ks,rs)) in
    (* new focus ------ *)
    let c = mk_child p in
    Some(Fts_state(c,p#xs)) )
)"

(* FIXME needed? remove? *)
(*
definition dest_fts_state :: "fts_state_t \<Rightarrow> leaf_lbl_t option" where
"dest_fts_state fts = (
  let (f,stk) = fts in
  case (f|>f_t) of
  Leaf kvs \<Rightarrow> Some(kvs)
  | _ \<Rightarrow> None
)"
*)

(* fts_trans ----------------------------------------- *)

definition fts_trans :: "fts_state_t trans_t" where
"fts_trans = { (fts,fts'). (step_fts fts = Some fts') }"


(* lemmas ------------------------------------------- *)

(* wf_fts is invariant *)
definition invariant_wf_fts_lem :: "bool" where
"invariant_wf_fts_lem = (! P. ((% fts. wellformed_fts fts) = P) \<longrightarrow> invariant fts_trans P)"


definition focus_to_leaves :: "fts_focus_t \<Rightarrow> leaves_t" where
"focus_to_leaves f = (
  let (k,tss1,l,t,u,tss2) = f|>dest_core in
  (tss1@[[t]]@tss2)|>tss_to_leaves
)"

(* the focus leaves are invariant *)
definition invariant_leaves_lem :: "bool" where
"invariant_leaves_lem = (
  ! ls P. ((% fts. focus_to_leaves (fts|>dest_fts_state|>fst) = ls) = P) \<longrightarrow> invariant fts_trans P )"

(* this is enough to ensure that the result of find is the correct leaf *)


(* testing ---------------------------------------- *)

(* we want to test wf at each stage, and the focus_to_leaves invariant at each transition 

for wf, it suffices to expose wellformed_fts when we export code

we should also export focus_to_leaves because it is the basis of the map abstraction

*)

definition wf_fts_trans :: "fts_state_t \<Rightarrow> fts_state_t \<Rightarrow> bool" where
"wf_fts_trans s1 s2 = assert_true (s1,s2) (focus_to_leaves (s2|>dest_fts_state|>fst) = focus_to_leaves (s1|>dest_fts_state|>fst))"



end
