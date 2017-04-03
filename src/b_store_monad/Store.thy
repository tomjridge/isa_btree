theory Store
imports Monad
begin


(* for testing ------------------------------------------------- *)

type_synonym r2f = "r \<Rightarrow> frame option"

(* debugging/proof *)
definition "mk_r2f" :: "store \<Rightarrow> r2f" where
"mk_r2f s = failwith (STR ''FIXME'')"


end
