theory Prelude imports Main begin

(* FIXME move to lib *)
definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"



end