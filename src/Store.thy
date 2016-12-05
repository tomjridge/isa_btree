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

(* this is only for proof - failwith in impl *)
definition dest_Store :: "store \<Rightarrow> (page_ref \<Rightarrow> page)" where
"dest_Store x = (case x of Store y \<Rightarrow> y)"

datatype store_error = string (* se *)
type_synonym se = store_error

(* really these are "monad" types *)
definition "page_ref_to_page" :: "r \<Rightarrow> (s \<Rightarrow> (s * (p,se) rresult))" (* r \<Rightarrow> p se_M *) where
"page_ref_to_page p = failwith ''FIXME''"

definition "alloc" :: "p \<Rightarrow> (s \<Rightarrow> (s * (r,se) rresult))" (* p \<Rightarrow> r se_M *) where
"alloc p = failwith ''FIXME''"

(* FIXME remove - store creation is ad hoc depending on store type *)
definition empty_store :: "unit \<Rightarrow> store * r" where "empty_store _ = failwith ''FIXME''"

end