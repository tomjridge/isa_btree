theory Store
imports Monad
begin

(* store api -------------------------------------------------- *)

definition "store_read" :: "r \<Rightarrow> frame MM" where
"store_read r = failwith (STR ''FIXME'')"

definition "store_alloc" :: "frame \<Rightarrow> r MM" where
"store_alloc frm = failwith (STR ''FIXME'')"

definition "store_free" :: "r list \<Rightarrow> unit MM" where
"store_free rs = failwith (STR ''FIXME'')" 


(* for testing ------------------------------------------------- *)

type_synonym r2f = "r \<Rightarrow> frame option"

(* debugging/proof *)
definition "mk_r2f" :: "store \<Rightarrow> r2f" where
"mk_r2f s = failwith (STR ''FIXME'')"


end
