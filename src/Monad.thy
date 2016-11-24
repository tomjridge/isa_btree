theory Monad
imports Key_value Frame
begin

(* parameterize the pure/block implementation *)

type_synonym r = r

type_synonym ks_rs = "ks * r list"

type_synonym stk_frame =  "key option * (ks_rs * ks_rs) * key option" (* the bounds are bounds for the whole frame *) 

type_synonym stk = "stk_frame list"

datatype error = Store_error store_error 
type_synonym e = error

definition se_to_e :: "se \<Rightarrow> e" where 
"se_to_e se = Store_error se"
  
type_synonym 'a MM = "('a,e) M"
 
definition bind :: "('a \<Rightarrow> 'b MM) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where 
"bind f v = Store.bind f v"

definition return :: "'a \<Rightarrow> 'a MM" where
"return x = (% s. (s, Ok x))"

definition page_ref_to_frame :: "r \<Rightarrow> fr MM" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> fmap_error se_to_e"

end