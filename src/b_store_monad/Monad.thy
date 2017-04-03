theory Monad
imports "$SRC/a_pre/Params" 
begin

(* monad -------------------------------------------------- *)


definition dest_MM :: "'a MM \<Rightarrow> (store \<Rightarrow> store * 'a res)" where
"dest_MM x = (case x of MM f \<Rightarrow> f)"

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where
"fmap f m = MM ( % s.
  let (s',r) = (dest_MM m) s in
  (s',case r of Ok y \<Rightarrow> Ok (f y) | Error x \<Rightarrow> Error x)
)"

definition bind :: "('a \<Rightarrow> 'b MM) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where
"bind f m = MM (% s. 
  (case (dest_MM m) s of 
  (s1,Error x) \<Rightarrow> (s1,Error x) 
  | (s1,Ok y) \<Rightarrow> ((dest_MM (f y)) s1)))"
  
definition return :: "'a \<Rightarrow> 'a MM" where
"return x = MM (% s. (s,Ok(x)))"

end