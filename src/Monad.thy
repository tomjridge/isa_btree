theory Monad
imports Util (* doesn't depend on a lot of stuff from ts *)
begin

(* the generic monad; the more specific version is in monad2 *)

(* monad depends on the store type *)

datatype ('a,'s) M_t = M "'s \<Rightarrow> 's * ('a,e) rresult" 

(*
type_synonym ('a,'s) M = "('a,'s) M_t"  
*)

definition dest_M :: "('a,'s) M_t \<Rightarrow> 's \<Rightarrow> 's * ('a,e) rresult" where
"dest_M m = (case m of M x \<Rightarrow> x)"

(* monad -------------------------------------------------- *)

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'s) M_t \<Rightarrow> ('b,'s) M_t" where
"fmap f m = M ( % s.
  let (s',r) = (dest_M m) s in
  (s',case r of Ok y \<Rightarrow> Ok (f y) | Error x \<Rightarrow> Error x)
)"

(*
definition fmap_error :: "('e \<Rightarrow> 'f) \<Rightarrow> ('a,'s) M_t \<Rightarrow> ('a,'s,'f) M_t" where
"fmap_error f m = M ( % s.
  let (s',r) = (dest_M m) s in
  (s',case r of Ok y \<Rightarrow> Ok y | Error x \<Rightarrow> Error (f x)))"
*)

definition bind :: "('a \<Rightarrow> ('b,'s) M_t) \<Rightarrow> ('a,'s) M_t \<Rightarrow> ('b,'s) M_t" where
"bind f m = M (% s. 
  (case (dest_M m) s of 
  (s1,Error x) \<Rightarrow> (s1,Error x) 
  | (s1,Ok y) \<Rightarrow> ((dest_M (f y)) s1)))"
  
definition return :: "'a \<Rightarrow> ('a,'s) M_t" where
"return x = M (% s. (s,Ok(x)))"




end