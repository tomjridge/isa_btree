theory Pre_params
imports  "$SRC/a_tree/Tree_stack"
begin

(* this to force dependency order in exported code? *)
definition dummy :: "unit" where "dummy=()"


(* mk_r2t ----------------------------------------------------------- *)


type_synonym ('k,'v,'r,'t) r2f = "('t \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r) dnode option)"

type_synonym ('k,'v,'r,'t) r2t = "('t \<Rightarrow> 'r \<Rightarrow> ('k,'v) tree option)"

(* n is fuel (the height of the tree); t is not needed FIXME? *)
fun mk_r2t' :: "('k,'v,'r,'t) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r,'t) r2t" where
"mk_r2t' r2f n t r = (
  case n of 
  0 \<Rightarrow> None
  | Suc n \<Rightarrow> (
    case r2f t r of
    None \<Rightarrow> None
    | Some frm \<Rightarrow> (
      case frm of
      Disk_leaf kvs \<Rightarrow> Some(Leaf(kvs))
      | Disk_node(ks,rs) \<Rightarrow> (
        let ts = List.map (mk_r2t' r2f n t) rs in
        case (List.filter is_None ts) of
        [] \<Rightarrow> Some(Node(ks,ts|>List.map dest_Some))
        | _ \<Rightarrow> None ))))"

(* map a blocks-and-pointers tree to an ADT tree *)
definition mk_r2t :: "('k,'v,'r,'t) r2f \<Rightarrow> nat \<Rightarrow> ('k,'v,'r,'t) r2t" where
"mk_r2t = mk_r2t'"



(* ('a,'t) MM type_synonym ------------------------------------------ *)

(* NOTE naming convention: 't is for the state type (not the "tree" 
type or something like that *)

(* NOTE in this monad, ALL errors (even unexpected errors eg disk block read fail) are explicit; 
in OCaml we may prefer to keep unexpected errors implicit. By making the errors explicit we
force the proofs to discuss all possible cases... but perhaps if we always just halt on an 
"unexpected" error, and expected errors are returned in 'a, then this is unnecessary?
*)
type_synonym ('a,'t) MM = "'t \<Rightarrow> ('t * 'a res)"


end