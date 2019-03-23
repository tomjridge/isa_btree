
(* Author: Ondrej Kuncar, TU Muenchen *)

section \<open>Pervasive test of code generator\<close>

theory Generate_Efficient_Datastructures
  imports
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.RBT_Mapping"
begin

text \<open>
  The following code equations have to be deleted because they use 
  lists to implement sets in the code generetor. 
\<close>
text \<open>
  If code generation fails with a message like
  \<open>"List.set" is not a constructor, on left hand side of equation: ...\<close>,
  feel free to add an RBT implementation for the corrsponding operation
  of delete that code equation (see above).                                  
\<close>


fun rbt_min' :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option \<Rightarrow> ('a*'b) option" where
"rbt_min' x sofar = (case x of
RBT_Impl.Empty \<Rightarrow> sofar
| Branch c l k v r \<Rightarrow> rbt_min' l (Some(k,v)))"

definition rbt_min :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option" where
"rbt_min x = rbt_min' x None"


fun rbt_max' :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option \<Rightarrow> ('a*'b) option" where
"rbt_max' x sofar = (case x of
RBT_Impl.Empty \<Rightarrow> sofar
| Branch c l k v r \<Rightarrow> rbt_max' r (Some(k,v)))"

definition rbt_max :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option" where
"rbt_max x = rbt_max' x None"


export_code "RBT._" rbt_min rbt_max (* "RBT_Impl.rbt_insert" "RBT_Impl.rbt_delete" *)

in OCaml file "/tmp/generate_efficient_datastructures.ml"

end
