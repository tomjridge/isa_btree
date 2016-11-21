theory Prelude 
imports Main Util Constants  
begin

definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"


(* merging maps ------------------------------------------- *)

(*
definition maps_to_map_prop :: "('a,'b) map set \<Rightarrow> ('a,'b) map \<Rightarrow> bool" where
"maps_to_map_prop ms m = (
(! a b. (m a = Some b) = (? m' : ms. m' a = Some b)) &
(! a. (m a = None) = (! m' : ms. m' a = None))
)"

definition maps_to_map :: "('a,'b) map set \<Rightarrow> ('a,'b) map" where
"maps_to_map ms = (SOME m. maps_to_map_prop ms m)"

lemma "maps_to_map_prop ms (maps_to_map ms)"
  apply(force intro:FIXME)
  done

definition leaves_to_map :: "('k * 'v) list list \<Rightarrow> ('k,'v) map" where
"leaves_to_map ls = (image map_of (set ls)) |> maps_to_map"
*)

definition leaves_to_map :: "('k * 'v) list list \<Rightarrow> ('k,'v) map" where
"leaves_to_map ls = ls |> concat |> map_of"

(*
lemma [simp]: "[] |> map_of = Map.empty"
 apply(simp add: rev_apply_def)
 done
 
 lemma [simp]: "xs |> concat = [] \<Longrightarrow> xs |> leaves_to_map = Map.empty" sorry
*)

lemma append_leaves_to_map: "
((xs) |> leaves_to_map |> dom = {}) \<Longrightarrow>
((xs') |> leaves_to_map |> dom = {}) \<Longrightarrow> 
((xs @ xs') |> leaves_to_map |> dom = {})"
 sorry
 
 

 
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