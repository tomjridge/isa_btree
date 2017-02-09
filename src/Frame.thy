theory Frame
imports Frame_types Tree_stack
(* FIXME may want to move this to Frame_tree *)
begin

(* FIXME rename page_frame *)

(* blocks on disk correspond to frames, which are like nodes, but with pointers rather than
children *)



definition page_ref_to_frame :: "r \<Rightarrow> pfr SM_t" where
"page_ref_to_frame r = ( 
  page_ref_to_page r |> fmap (% p. page_to_frame p)
)"

definition dest_Node_frame :: "pframe \<Rightarrow> ks_rs" where
"dest_Node_frame f = (case f of Node_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Node_frame''))"

definition dest_Leaf_frame :: "pframe \<Rightarrow> kvs" where
"dest_Leaf_frame f = (case f of Leaf_frame x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Leaf_frame''))"


(* mapping a block ref to a tree ----------------  *)


fun r_to_t' :: "store \<Rightarrow> nat \<Rightarrow> r \<Rightarrow> t" where
"r_to_t' s n r = (
  let r_to_p = dest_Store s in
  case n of 
  0 \<Rightarrow> failwith (STR ''r_to_t'')
  | Suc n \<Rightarrow> (
    (r_to_p r) |> (% page.
    page |> page_to_frame |>
      (% frm. 
        case frm of
        Node_frame(ks,rs) \<Rightarrow> (Node(ks,List.map (r_to_t' s n) rs))
        | Leaf_frame(kvs) \<Rightarrow> Leaf(kvs)))) 
)"

definition r_to_t :: "store \<Rightarrow> r \<Rightarrow> t" where "r_to_t s r = r_to_t' s 1000 r" (* FIXME only for proof *)

definition r_stk_to_rs :: "r stk \<Rightarrow> r list" where 
"r_stk_to_rs xs = (xs|>List.map f_t)"


definition r_frame_to_t_frame :: "store \<Rightarrow> r frame \<Rightarrow> t frame" where
"r_frame_to_t_frame s = frame_map (r_to_t s)"

end