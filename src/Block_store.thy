theory Block_store
imports Util
begin

(* really these types are abstract *)
datatype page_ref = Page_ref nat (* r *)
datatype page = Page nat (* p *)
datatype store = Store nat (* s *)

datatype store_error = string (* e *)

type_synonym 'a M = "('a,store_error) rresult" 

definition "write" :: "store \<Rightarrow> page_ref \<Rightarrow> page \<Rightarrow> store M" where
"write s r p = failwith ''FIXME''"

definition "read" :: "store \<Rightarrow> page_ref \<Rightarrow> page M" where
"read s r = failwith ''FIXME''"


end