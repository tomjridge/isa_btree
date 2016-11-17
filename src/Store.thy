theory Store
imports Util
begin

(* really these types are abstract *)
datatype page_ref = Page_ref nat (* r *)
datatype page = Page nat (* p *)
datatype store = Store nat (* s *)

datatype store_error = string (* e *)

type_synonym 'a M = "('a,store_error) rresult" 

definition "page_ref_to_page" :: "store \<Rightarrow> page_ref \<Rightarrow> page M" where
"page_ref_to_page s p = failwith ''FIXME''"

definition "allocate" :: "store \<Rightarrow> page \<Rightarrow> (store * page_ref)  M" where
"allocate s p = failwith ''FIXME''"


end