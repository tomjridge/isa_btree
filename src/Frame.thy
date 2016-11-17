theory Frame
imports Key_value_types Store
begin

type_synonym frame_nf_t = "key list * page_ref list"

datatype frame = Node_frame frame_nf_t | Leaf_frame kvs_t

definition page_to_frame :: "page \<Rightarrow> frame" where "page_to_frame = failwith ''FIXME''"

definition frame_to_page :: "frame \<Rightarrow> page" where "frame_to_page = failwith ''FIXME''"

definition page_ref_to_frame :: "store \<Rightarrow> page_ref \<Rightarrow> frame M" where
"page_ref_to_frame s r = (
  page_ref_to_page s r |> rbind (% p. Ok (p|>page_to_frame))
)"

end