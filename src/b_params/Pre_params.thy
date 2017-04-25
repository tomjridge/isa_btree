theory Pre_params
imports  "$SRC/a_tree/Tree_stack"
begin

definition dummy :: "unit" where "dummy=()"

(* leaf stream types ----------------------------------------- *)

(* we need these exposed outside functor body in ML *)

datatype ('k,'v,'r) ls_state = 
  LS_down "'r*('k,'r) ts_frame list" 
  | LS_leaf "('k*'v) list * ('k,'r) ts_frame list" 
  | LS_up "('k,'r) ts_frame list"
  
type_synonym ('k,'v,'r) r2f = "('r \<Rightarrow> ('k,'v,'r) Frame.t option)"

type_synonym ('k,'v,'r) r2t = "('r \<Rightarrow> ('k,'v) tree option)"

fun mk_r2t' :: "('k,'v,'r) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r) r2t" where
"mk_r2t' s n r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    case s r of
    None \<Rightarrow> None
    | Some frm \<Rightarrow> (
      case frm of
      Leaf_frame kvs \<Rightarrow> Some(Leaf(kvs))
      | Node_frame(ks,rs) \<Rightarrow> (
        let ts = List.map (mk_r2t' s n) rs in
        case (List.filter is_None ts) of
        [] \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
        | _ \<Rightarrow> None
      )
    )
  )
)"

definition mk_r2t :: "('k,'v,'r) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r) r2t" where
"mk_r2t = mk_r2t'"

end