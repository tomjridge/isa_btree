theory Monad
imports Key_value Frame Tree_stack
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
"bind f v = Store.bind f v"

definition return :: "'a \<Rightarrow> 'a MM" where
"return x = (% s. (s, Ok x))"

definition get_store :: "store MM" where
"get_store = (% s. (s,Ok s))"

(*
definition r_to_t :: "r \<Rightarrow> t" where
"r_to_t r = (failwith ''r_to_t'')"
*)

definition add_new_stk_frame :: "key \<Rightarrow> (ks * 'a list) \<Rightarrow> 'a stk \<Rightarrow> ('a stk * 'a)" where
"add_new_stk_frame k ks_rs stk = (
  let (ks,rs) = ks_rs in
  let ((ks1,rs1),r',(ks2,rs2)) = split_ks_rs k (ks,rs) in
  let (l,u) = stack_to_lu_of_child stk in
  let frm' = \<lparr>f_ks1=ks1,f_ts1=rs1,f_t=r', f_ks2=ks2,f_ts2=rs2 \<rparr> in
  (frm'#stk,r')
)"

definition r_frame_to_t_frame :: "store \<Rightarrow> r frame \<Rightarrow> t frame" where
"r_frame_to_t_frame s = frame_map (r_to_t s)"

definition prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"prefix xs ys = (take (List.length xs) ys = xs)"

definition wellformed_stk :: "key \<Rightarrow> tree \<Rightarrow> ('a \<Rightarrow> t) \<Rightarrow> 'a stk \<Rightarrow> bool" where
"wellformed_stk k t to_t stk = (
  let stk' = stk|>List.map (frame_map to_t) in
  let t_stk = t|>tree_to_tstk k in
  prefix stk' t_stk
)"

definition page_ref_to_frame :: "r \<Rightarrow> pfr MM" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> fmap_error se_to_e"

definition alloc :: "p \<Rightarrow> r MM" where 
"alloc p = (Store.alloc p |> fmap_error (% se. Store_error se))"

end