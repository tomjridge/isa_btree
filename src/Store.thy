theory Store
imports Util
begin

(* really these types are abstract *)
datatype page_ref = Page_ref nat (* r *)
type_synonym r = page_ref
type_synonym rs = "page_ref list"

datatype page = Page nat (* p *)
type_synonym p = page


datatype store = Store nat (* s *)
type_synonym s = store

datatype store_error = string (* se *)
type_synonym se = store_error


(* monad -------------------------------------------------- *)

type_synonym ('a,'e) M = "s \<Rightarrow> s * ('a,'e) rresult" 

type_synonym 'a se_M = "('a,se) M"

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'e) M \<Rightarrow> ('b,'e) M" where
"fmap f m s = (
  let (s',r) = m s in
  (s',case r of Ok y \<Rightarrow> Ok (f y) | Error x \<Rightarrow> Error x)
)"

definition fmap_error :: "('e \<Rightarrow> 'f) \<Rightarrow> ('a,'e) M \<Rightarrow> ('a,'f) M" where
"fmap_error f m s = (
  let (s',r) = m s in
  (s',case r of Ok y \<Rightarrow> Ok y | Error x \<Rightarrow> Error (f x)))"

definition bind :: "('a \<Rightarrow> ('b,'e) M) \<Rightarrow> ('a,'e) M \<Rightarrow> ('b,'e) M" where
"bind f v = (% s. (case v s of (s1,Error x) \<Rightarrow> (s1,Error x) | (s1,Ok y) \<Rightarrow> (f y s1)))"

definition se_bind :: "('a \<Rightarrow> 'b se_M) \<Rightarrow> 'a se_M \<Rightarrow> 'b se_M" where
"se_bind f v = bind f v"

definition se_return :: "'a \<Rightarrow> 'a se_M" where
"se_return x = (% s. (s,Ok x))"

definition get_store :: "unit \<Rightarrow> s se_M" where
"get_store _ = (% s. (s,Ok(s)))"



definition "page_ref_to_page" :: "r \<Rightarrow> p se_M" where
"page_ref_to_page p = failwith ''FIXME''"

definition "alloc" :: "p \<Rightarrow> r se_M" where
"alloc p = failwith ''FIXME''"


end