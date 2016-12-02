theory Prelude 
imports Main Util   
begin

definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"

 
(* transition systems -------------------------------- *)

type_synonym 's trans_t = "('s * 's) set"

definition trace_set :: "('s * 's) set \<Rightarrow> (nat \<Rightarrow> 's) set" where
"trace_set trns = { f .  (! (n::nat). (f n, f(n+1)) : trns) }"

definition invariant :: "('s * 's) set \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant trns P = (! s s'. (s,s') : trns \<longrightarrow> P s \<longrightarrow> P s')"

(* the main lemma about invariants FIXME prove this *)  
definition invariant_b :: "'s trans_t \<Rightarrow> bool" where
"invariant_b trns = (! P f.
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

definition invariant_assuming_b :: "'s trans_t \<Rightarrow>  ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant_assuming_b trns P Q = (
  invariant trns P &
  invariant_assuming trns P Q 
  \<longrightarrow> invariant trns (% x. P x & Q x)
)"




end