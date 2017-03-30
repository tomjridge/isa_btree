theory Todo imports Main begin



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