theory Store
imports Monad
begin


(* store api -------------------------------------------------- *)

(* really these types are abstract *)
datatype page_ref = Page_ref nat (* r *)
type_synonym r = page_ref
type_synonym rs = "page_ref list"

datatype page = Page nat (* p *)
type_synonym p = page


datatype store = Store "nat" (* page_ref \<Rightarrow> page" (* s *) *)
type_synonym s = store

definition dest_Store :: "store \<Rightarrow> page_ref \<Rightarrow> page" where
"dest_Store s r = (failwith (STR ''FIXME''))"


(* store monad ----------------------------------------------- *)

type_synonym 'a SM_t = "('a,s) M_t"

definition "page_ref_to_page" :: "r \<Rightarrow> p SM_t" where
"page_ref_to_page p = failwith (STR ''FIXME'')"

definition "alloc" :: "p \<Rightarrow> r SM_t" (* p \<Rightarrow> r se_M *) where
"alloc p = failwith (STR ''FIXME'')"

definition "free" :: "r list \<Rightarrow> unit SM_t" where
"free ps = failwith (STR ''FIXME'')" 


end



(*

definition se_bind :: "('a \<Rightarrow> 'b SM_t) \<Rightarrow> 'a SM_t \<Rightarrow> 'b SM_t" where
"se_bind f = (bind f)"

definition se_return :: "'a \<Rightarrow> 'a SM_t" where
"se_return x = return x"

definition  se_fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a SM_t \<Rightarrow> 'b SM_t" where
"se_fmap f x = fmap f x"

*)
(*
definition get_store :: "unit \<Rightarrow> s se_M" where
"get_store _ = (% s. (s,Ok(s)))"
*)

(* this is only for proof - failwith in impl; but also needed for wellformedness checks *)
(*
definition dest_Store :: "store \<Rightarrow> (page_ref \<Rightarrow> page)" where
"dest_Store x = (case x of Store y \<Rightarrow> y)"
*)
