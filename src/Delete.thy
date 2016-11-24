theory Delete
imports Delete_tree_stack Find
begin

datatype d_t =
  D_small_leaf "leaf_lbl_t"
  | D_small_node "ks * rs"
  | D_updated_subtree "r"
  
type_synonym d_focus_t = d_t

(* FIXME unify type names eg stk and tree_stack_t *)

datatype d_state_t = 
  D_down "find_state_t"
  | D_up "d_focus_t * stk"
  | D_finished r
  
type_synonym up_state = "d_focus_t * stk"
type_synonym u = up_state

datatype d_error = D_find_error find_error | D_store_error store_error | D_error string
type_synonym de = d_error

type_synonym 'a de_M = "('a,de) M"

definition de_bind :: "('a \<Rightarrow> 'b de_M) \<Rightarrow> 'a de_M \<Rightarrow> 'b de_M" where
"de_bind f v = bind f v"

definition d_alloc :: "p \<Rightarrow> r de_M" where 
"d_alloc p = (alloc p |> fmap_error (% se. D_store_error se))"

definition page_ref_to_frame :: "r \<Rightarrow> fr de_M" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r |> fmap_error (% se. D_store_error se))"

definition step_up :: "u \<Rightarrow> d_state_t de_M" where
"step_up du = (
  let (f,stk) = du in
  case stk of
  [] \<Rightarrow> (
    case f of
    D_updated_subtree r \<Rightarrow> (% s. (s,Ok (D_finished r)))  
    | _ \<Rightarrow> failwith ''FIXME''
  )
  | p#stk' \<Rightarrow> (
    case f of
    D_updated_subtree r \<Rightarrow> (
      let (rs1,ks1,_,ks2,rs2) = p in
      let page = Node_frame(ks1@ks2,rs1@[r]@rs2) in
      d_alloc p |> fmap (% r'. D_updated_subtree r')
    )
    | D_small_leaf(kvs) \<Rightarrow> (
      let leaf = True in
      let (p_rs1,p_ks1,_,p_ks2,p_rs2) = p in
      (* FIXME can't we just use a monad at the dts level? *) 
      get_sibling ((p_ks1,p_ts1),(p_ks2,p_ts2)) 
      let (right,(p_1,p_2),s,p_k) = 
    )
  )
)"

end