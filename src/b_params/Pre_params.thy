theory Pre_params
imports  "$SRC/a_tree/Tree_stack"
begin

(* this to force dependency order? *)
definition dummy :: "unit" where "dummy=()"


(* mk_r2t ------------------------------ *)


type_synonym ('k,'v,'r,'t) r2f = "('t \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r) frame option)"

type_synonym ('k,'v,'r,'t) r2t = "('t \<Rightarrow> 'r \<Rightarrow> ('k,'v) tree option)"


fun mk_r2t' :: "('k,'v,'r,'t) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r,'t) r2t" where
"mk_r2t' r2f n t r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    case r2f t r of
    None \<Rightarrow> None
    | Some frm \<Rightarrow> (
      case frm of
      Leaf_frame kvs \<Rightarrow> Some(Leaf(kvs))
      | Node_frame(ks,rs) \<Rightarrow> (
        let ts = List.map (mk_r2t' r2f n t) rs in
        case (List.filter is_None ts) of
        [] \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
        | _ \<Rightarrow> None
      )
    )
  )
)"

(* map a blocks-and-pointers tree to an ADT tree *)

definition mk_r2t :: "('k,'v,'r,'t) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r,'t) r2t" where
"mk_r2t = mk_r2t'"


end