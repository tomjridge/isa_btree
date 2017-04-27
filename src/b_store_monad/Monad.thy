theory Monad
imports "$SRC/b_params/Params" 
begin

(* monad -------------------------------------------------- *)

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where
"fmap f m = ( % s.
  m s |> (% (s',r). (s',case r of Ok y \<Rightarrow> Ok (f y) | Error x \<Rightarrow> Error x)))"

definition bind :: "('a \<Rightarrow> 'b MM) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where
"bind f m = (% s. 
  m s |> (% (s1,r). 
  case r of 
  Error x \<Rightarrow> (s1,Error x) 
  | Ok y \<Rightarrow> f y s1))"
  
definition return :: "'a \<Rightarrow> 'a MM" where
"return x = (% s. (s,Ok(x)))"

end