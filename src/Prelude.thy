theory Prelude imports Main Util begin

definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"


definition maps_as_map :: "('a,'b) map set \<Rightarrow> ('a,'b) map \<Rightarrow> bool" where
"maps_as_map ms m = (
(! a b. (m a = Some b) = (? m' : ms. m' a = Some b)) &
(! a. (m a = None) = (! m' : ms. m' a = None))
)"

definition merge_maps :: "('a,'b) map set \<Rightarrow> ('a,'b) map" where
"merge_maps ms = (SOME m. maps_as_map ms m)"

lemma "maps_as_map ms (merge_maps ms)"
  apply(force intro:FIXME)
  done

end