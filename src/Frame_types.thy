theory Frame_types 
imports Store Key_value_types
begin

(* blocks on disk correspond to frames, which are like nodes, but with pointers rather than
children *)

type_synonym ks_rs = "ks * rs"

datatype pframe = Node_frame "ks_rs" | Leaf_frame kvs

type_synonym pfr = pframe

definition page_to_frame :: "p \<Rightarrow> pfr" where "page_to_frame = failwith ''FIXME''"

definition frame_to_page :: "pfr \<Rightarrow> p" where "frame_to_page = failwith ''FIXME''"

definition empty_store :: "store * r" where "empty_store = failwith ''FIXME''"

(* really these are "monad" types *)
definition "page_ref_to_page" :: "r \<Rightarrow> (s \<Rightarrow> (s * (p,se) rresult))" (* r \<Rightarrow> p se_M *) where
"page_ref_to_page p = failwith ''FIXME''"

definition "alloc" :: "p \<Rightarrow> (s \<Rightarrow> (s * (r,se) rresult))" (* p \<Rightarrow> r se_M *) where
"alloc p = failwith ''FIXME''"


end