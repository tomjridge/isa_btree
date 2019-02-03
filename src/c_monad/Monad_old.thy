theory Monad
imports Pre_monad Find_state Delete_state Insert_many_state Insert_state Leaf_stream_state
begin

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=
  (Find_state.dummy,Delete_state.dummy,Insert_many_state.dummy,Insert_state.dummy,Leaf_stream_state.dummy)
  |> (% x. Params.dummy)"


(* NOTE this depends on Util for the concrete defn *)

(* monad ------------------------------------------------------------ *)

(* FIXME this could come after Util *)

(* NOTE naming convention: 't is for the state type (not the "tree" 
type or something like that *)

(* NOTE in this monad, ALL errors (even unexpected errors eg disk block read fail) are explicit; 
in OCaml we may prefer to keep unexpected errors implicit. By making the errors explicit we
force the proofs to discuss all possible cases... but perhaps if we always just halt on an 
"unexpected" error, and expected errors are returned in 'a, then this is unnecessary?
*)



(*

type_synonym ('a,'t) MM = "'t \<Rightarrow> ('t * 'a res)"
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
*)


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