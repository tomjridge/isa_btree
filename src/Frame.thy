theory Frame
imports Key_value_types Store
begin

(* blocks on disk correspond to frames, which are like nodes, but with pointers rather than
children *)

type_synonym ks_rs = "ks * rs"

datatype frame = Node_frame "ks_rs" | Leaf_frame kvs

type_synonym fr = frame

definition page_to_frame :: "p \<Rightarrow> fr" where "page_to_frame = failwith ''FIXME''"

definition frame_to_page :: "fr \<Rightarrow> p" where "frame_to_page = failwith ''FIXME''"

definition page_ref_to_frame :: "r \<Rightarrow> fr se_M" where
"page_ref_to_frame r = ( 
  page_ref_to_page r |> fmap (% p. page_to_frame p)
)"

definition dest_Node_frame :: "frame \<Rightarrow> ks_rs" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith ''dest_Node_frame'')"

definition dest_Leaf_frame :: "frame \<Rightarrow> kvs" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith ''dest_Leaf_frame'')"


end