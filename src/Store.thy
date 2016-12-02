theory Store
imports Util
begin

(* really these types are abstract *)
datatype page_ref = Page_ref nat (* r *)
type_synonym r = page_ref
type_synonym rs = "page_ref list"

datatype page = Page nat (* p *)
type_synonym p = page


datatype store = Store "page_ref \<Rightarrow> page" (* s *)
type_synonym s = store

definition dest_Store :: "store \<Rightarrow> (page_ref \<Rightarrow> page)" where
"dest_Store x = (case x of Store y \<Rightarrow> y)"

datatype store_error = string (* se *)
type_synonym se = store_error



end