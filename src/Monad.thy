theory Monad
imports Key_value Frame
begin

(* parameterize the pure/block implementation *)

type_synonym r = r

type_synonym ks_rs = "ks * r list"

datatype stk_frame = Private_stk_frame  "(ks_rs * ks_rs)" 
definition dest_stk_frame :: "stk_frame \<Rightarrow> (ks_rs * ks_rs)" where
"dest_stk_frame x = (case x of Private_stk_frame y \<Rightarrow> y)"

(* FIXME do we want to make another monad for the stk_frame as well? but then we need to match this with the focus
as well - since the focus also carries l,u etc

or maybe we should make the entire stack abstract; then the focus can be reasonably simple
*)

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

definition add_new_stk_frame :: "key \<Rightarrow> ks_rs \<Rightarrow> stk \<Rightarrow> stk * r" where
"add_new_stk_frame k ks_rs stk = (
        let (ks,rs) = ks_rs in
        let i = search_key_to_index ks k in
        let (ks1,ks2) = split_at i ks in
        let (rs1,r',rs2) = split_at_3 i rs in
        let frm' = Private_stk_frame((ks1,rs1),(ks2,rs2)) in
        (frm'#stk,r')
)"

definition page_ref_to_frame :: "r \<Rightarrow> fr MM" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> fmap_error se_to_e"

definition alloc :: "p \<Rightarrow> r MM" where 
"alloc p = (Store.alloc p |> fmap_error (% se. Store_error se))"

end