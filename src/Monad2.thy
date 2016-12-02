theory Monad2
imports Frame
begin


(* parameterize the pure/block implementation *)

type_synonym r = r

type_synonym ks_rs = "ks * r list"

datatype error = Store_error store_error

type_synonym e = error

definition se_to_e :: "se \<Rightarrow> e" where 
"se_to_e se = Store_error se"
  
type_synonym 'a MM = "('a,e) M"
 
definition bind :: "('a \<Rightarrow> 'b MM) \<Rightarrow> 'a MM \<Rightarrow> 'b MM" where 
"bind f v = Monad.bind f v"

definition return :: "'a \<Rightarrow> 'a MM" where
"return x = (% s. (s, Ok x))"

definition get_store :: "store MM" where
"get_store = (% s. (s,Ok s))"


definition r_frame_to_t_frame :: "store \<Rightarrow> r frame \<Rightarrow> t frame" where
"r_frame_to_t_frame s = frame_map (r_to_t s)"

definition page_ref_to_frame :: "r \<Rightarrow> pfr MM" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> fmap_error se_to_e"

definition alloc :: "p \<Rightarrow> r MM" where 
"alloc p = (Monad.alloc p |> fmap_error (% se. Store_error se))"

end