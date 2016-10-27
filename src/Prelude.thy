theory Prelude imports Main Util begin

definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"


(* merging maps ------------------------------------------- *)

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


(* transition systems -------------------------------- *)

definition trace_set :: "('s * 's) set \<Rightarrow> (nat \<Rightarrow> 's) set" where
"trace_set trns = { f .  (! (n::nat). (f n, f(n+1)) : trns) }"

end