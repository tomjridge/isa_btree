theory Monad
imports "$SRC/b_params/Pre_params" 
begin

(* ('a,'t) MM type_synonym ------------------------------------------ *)

(* NOTE naming convention: 't is for the state type (not the "tree" 
type or something like that *)

(* NOTE in this monad, ALL errors (even unexpected errors eg disk block read fail) are explicit; 
in OCaml we may prefer to keep unexpected errors implicit. By making the errors explicit we
force the proofs to discuss all possible cases... but perhaps if we always just halt on an 
"unexpected" error, and expected errors are returned in 'a, then this is unnecessary?
*)
type_synonym ('a,'t) MM = "'t \<Rightarrow> ('t * 'a res)"



(* monad ------------------------------------------------------------ *)

(* definition of MM is in params *)

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"fmap f m = ( % s.
  m s |> (% (s',r). (s',case r of Ok y \<Rightarrow> Ok (f y) | Error x \<Rightarrow> Error x)))"

definition bind :: "('a \<Rightarrow> ('b,'t) MM) \<Rightarrow> ('a,'t) MM \<Rightarrow> ('b,'t) MM" where
"bind f m = (% s. 
  m s |> (% (s1,r). 
  case r of 
  Error x \<Rightarrow> (s1,Error x) 
  | Ok y \<Rightarrow> f y s1))"
  
definition return :: "'a \<Rightarrow> ('a,'t) MM" where
"return x = (% s. (s,Ok(x)))"

end