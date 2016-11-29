theory Frame
imports Key_value_types Store Tree  (* FIXME may want to move this to Frame_tree *)
begin

(* FIXME rename page_frame *)

(* blocks on disk correspond to frames, which are like nodes, but with pointers rather than
children *)

type_synonym ks_rs = "ks * rs"

datatype pframe = Node_frame "ks_rs" | Leaf_frame kvs

type_synonym pfr = pframe

definition page_to_frame :: "p \<Rightarrow> pfr" where "page_to_frame = failwith ''FIXME''"

definition frame_to_page :: "pfr \<Rightarrow> p" where "frame_to_page = failwith ''FIXME''"

definition page_ref_to_frame :: "r \<Rightarrow> pfr se_M" where
"page_ref_to_frame r = ( 
  page_ref_to_page r |> fmap (% p. page_to_frame p)
)"

definition dest_Node_frame :: "pframe \<Rightarrow> ks_rs" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith ''dest_Node_frame'')"

definition dest_Leaf_frame :: "pframe \<Rightarrow> kvs" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith ''dest_Leaf_frame'')"

fun r_to_t' :: "store \<Rightarrow> nat \<Rightarrow> r \<Rightarrow> t" where
"r_to_t' s n r = (
  case n of 
  0 \<Rightarrow> failwith ''r_to_t''
  | Suc n \<Rightarrow> (
    s|>dest_Store|>(% f. f r) |> page_to_frame |>
    (% frm. 
      case frm of
      Node_frame(ks,rs) \<Rightarrow> (Node(ks,List.map (r_to_t' s n) rs))
      | Leaf_frame(kvs) \<Rightarrow> Leaf(kvs))
  )
)"

definition r_to_t :: "store \<Rightarrow> r \<Rightarrow> t" where "r_to_t s r = r_to_t' s 1000 r" (* FIXME only for proof *)


end