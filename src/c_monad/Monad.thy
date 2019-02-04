theory Monad imports Main "$SRC/b_pre_monad/Pre_monad" begin

definition dummy :: "unit" where "dummy=Pre_monad.dummy"

(* abstract version; NOTE obviously can't be exported *)
(* NOTE undefined is accepted by the code generator and allows these abstract defns to be exported *)
typedecl ('a,'b) MM

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"fmap x y = undefined"

definition bind :: "('a \<Rightarrow> ('b,'t) MM) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"bind b a = undefined"
  
definition return :: "'a \<Rightarrow> ('a,'t) MM" where
"return x = undefined"

(* for checking within the monad; if checking is disabled, this should just return (), else
it should return the argument *)
definition check_m :: "(unit,'t) MM \<Rightarrow> (unit,'t) MM" where
"check_m x = undefined"


end