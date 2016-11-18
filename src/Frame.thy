theory Frame
imports Key_value_types Store
begin

type_synonym ks_rs = "ks * rs"

datatype frame = Node_frame "ks_rs" | Leaf_frame kvs
type_synonym fr = frame

definition page_to_frame :: "p \<Rightarrow> fr" where "page_to_frame = failwith ''FIXME''"

definition frame_to_page :: "fr \<Rightarrow> p" where "frame_to_page = failwith ''FIXME''"

(* FIXME shouldn't access store twice *)
definition page_ref_to_frame :: "r \<Rightarrow> fr se_M" where
"page_ref_to_frame r = ( 
  page_ref_to_page r |> fmap (% p. page_to_frame p)
)"

end