theory Monad imports Main "$SRC/b_pre_monad/Pre_monad" begin


(* abstract version; NOTE obviously can't be exported *)
(* NOTE undefined is accepted by the code generator and allows these abstract defns to be exported *)
typedecl ('a,'b) MM

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"fmap x y = undefined"

definition bind :: "('a \<Rightarrow> ('b,'t) MM) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"bind b a = undefined"
  
definition return :: "'a \<Rightarrow> ('a,'t) MM" where
"return x = undefined"


end