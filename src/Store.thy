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


datatype store = Store "page_ref \<Rightarrow> page" (* s *)
type_synonym s = store

datatype store_error = Store_error string (* se *)
type_synonym se = store_error


(* store monad ----------------------------------------------- *)

type_synonym 'a se_M = "('a,s,se) M"



definition se_bind :: "('a \<Rightarrow> 'b se_M) \<Rightarrow> 'a se_M \<Rightarrow> 'b se_M" where
"se_bind f v = bind f v"

definition se_return :: "'a \<Rightarrow> 'a se_M" where
"se_return x = M (% s. (s,Ok x))"

(*
definition get_store :: "unit \<Rightarrow> s se_M" where
"get_store _ = (% s. (s,Ok(s)))"
*)

(* this is only for proof - failwith in impl; but also needed for wellformedness checks *)
(*
definition dest_Store :: "store \<Rightarrow> (page_ref \<Rightarrow> page)" where
"dest_Store x = (case x of Store y \<Rightarrow> y)"
*)

(* really these are "monad" types *)
definition "page_ref_to_page" :: "r \<Rightarrow> p se_M" where
"page_ref_to_page p = failwith (STR ''FIXME'')"

definition "alloc" :: "p \<Rightarrow> r se_M" (* p \<Rightarrow> r se_M *) where
"alloc p = failwith (STR ''FIXME'')"

definition "free" :: "r list \<Rightarrow> unit se_M" where
"free ps = failwith (STR ''FIXME'')" 


end