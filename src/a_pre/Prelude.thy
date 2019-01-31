theory Prelude 
imports Main Util 
begin


(* min/max size constants ------------------------------------------- *)


(* `constants` record type, which is used to record min and max bounds
for leaves and nodes *)

record constants = 
  min_leaf_size :: nat
  max_leaf_size :: nat
  min_node_keys :: nat
  max_node_keys :: nat

definition make_constants :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> constants" where
"make_constants a b c d = \<lparr> min_leaf_size=a, max_leaf_size=b, min_node_keys=c, max_node_keys=d \<rparr>"

(* FIXME add wf constraint following docs $l'>=2l-1$ and $m' >= 2m$ *)


(* small node or leaf ----------------------------------------------- *)

(* `min_size_t` is a datatype which flags whether nodes and leaves
are small or not; a small root can potentially have no children *)

datatype min_size_t = 
  Small_root_node_or_leaf
  | Small_node
  | Small_leaf

type_synonym ms_t = "min_size_t option"

 
(* transition systems ----------------------------------------------- *)

(* transition system basic definitions *)

type_synonym 's trans_t = "('s * 's) set"

definition trace_set :: "('s * 's) set \<Rightarrow> (nat \<Rightarrow> 's) set" where
"trace_set trns = { f .  (! (n::nat). (f n, f(n+1)) : trns) }"

definition invariant :: "('s * 's) set \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant trns P = (! s s'. (s,s') : trns \<longrightarrow> P s \<longrightarrow> P s')"

(* the main lemma about invariants FIXME prove this *)  
definition invariant_thm :: "'s trans_t \<Rightarrow> bool" where
"invariant_thm trns = (! P f.
  invariant trns P & 
  f : trace_set trns &
  P(f 0) \<longrightarrow> (! n. P (f n)) 
)"


(* Q is invariant, assuming P holds always; allows staging of the proof of various invariants *)
definition invariant_assuming :: "('s * 's) set \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant_assuming trns P Q = (
  let trns = { (s,s'). (s,s') : trns & P s & P s' } in
  invariant trns Q)
"

definition invariant_assuming_thm :: "'s trans_t \<Rightarrow>  ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant_assuming_thm trns P Q = (
  invariant trns P &
  invariant_assuming trns P Q 
  \<longrightarrow> invariant trns (% x. P x & Q x)
)"




end