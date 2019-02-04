theory Post_monad imports "$SRC/c_monad/Monad" begin

(* ops types -------------------------------------------- *)

datatype_record ('r,'dnode,'t) store_ops =
  read :: "'r \<Rightarrow> ('dnode,'t) MM"
  wrte :: "'dnode \<Rightarrow> ('r,'t) MM"
  rewrite :: "'r \<Rightarrow> 'dnode \<Rightarrow> ('r option,'t) MM"
  free :: "'r s \<Rightarrow> (unit,'t) MM"

end