theory Tree_stack imports Tree begin

datatype xtra_t = Xtra "(key option * key option)"  (* l,u *)
definition dest_xtra_t :: "xtra_t \<Rightarrow> key option * key option" where
"dest_xtra_t x = (case x of Xtra (l,u) \<Rightarrow> (l,u))"

datatype cnode_t = Cnode "node_t * nat * xtra_t"  (* n,i,x *)
definition dest_cnode_t :: "cnode_t \<Rightarrow> node_t * nat * xtra_t" where
"dest_cnode_t c = (case c of Cnode (n,i,x) \<Rightarrow> (n,i,x))"

(* FIXME remove *)
type_synonym context_t = "cnode_t list"

type_synonym tree_stack_t = "cnode_t list"

(* wellformed_context ---------------------------------------- *)

definition get_parent_bounds :: "context_t \<Rightarrow> xtra_t" where
"get_parent_bounds ts = (
  case ts of 
  Nil \<Rightarrow> Xtra(None,None)
  | cn#_ \<Rightarrow> (let (n,i,x) = dest_cnode_t cn in x))"


(* version of get_lu if parent bound is known *)
(* FIXME dest_xtra_t is a bit boring *)
definition get_lu_for_child_with_parent_default :: "xtra_t \<Rightarrow> (node_t*nat) \<Rightarrow> xtra_t" where
"get_lu_for_child_with_parent_default x2 ni = (
  let x1 = Xtra(get_lu_for_child ni) in
  let (l1,u1) = dest_xtra_t x1 in
  let (l2,u2) = dest_xtra_t x2 in
  let l = (case l1 = None of True \<Rightarrow> l2 | _ \<Rightarrow> l1) in
  let u = (case u1 = None of True \<Rightarrow> u2 | _ \<Rightarrow> u1) in
  Xtra(l,u)
)

(* FIXME adjust scala defns *)      
definition wellformed_cnode :: "ms_t => xtra_t \<Rightarrow> cnode_t => bool " where
"wellformed_cnode ms x2 cn = (
  let (n1,i1,x1) = dest_cnode_t cn in 
  let (ks,rs) = n1 in
  let b1 = wellformed_tree ms (Node(ks,rs)) in  (* FIXME wellformed_kv_tree *)
  let b2 = i1 : set(subtree_indexes (ks,rs)) in
  let (l1,u1) = dest_xtra_t x1 in
  let b3 = check_keys l1 (keys (rs!i1)) u1 in
  let (l2,u2) = dest_xtra_t x2 in
  let b4 = (case (i1 = min_child_index) of True \<Rightarrow> (l1 = l2) | False \<Rightarrow> True) in
  let b5 = (case (i1 = max_child_index(n1)) of True \<Rightarrow> (u1 = u2) | False \<Rightarrow> True) in
  b1&b2&b3&b4&b5)
"

fun wellformed_context :: "context_t => bool" where
"wellformed_context xs = (
  case xs of Nil \<Rightarrow> True
  | cn#cns \<Rightarrow> (
    let ms = (case cns of Nil \<Rightarrow> (Some(Small_root_node_or_leaf)) | _ \<Rightarrow> None) in
    let x2 = get_parent_bounds cns in
    wellformed_cnode ms x2 cn & 
    wellformed_context cns))"
(*end wfcontext definition*)



(* old ---------------------------------------- *)

(* old defintiions? *)

definition ctx_to_map :: "context_t => (key,value_t) map" where
"ctx_to_map ctx == (
let leaves = List.map (% cn. let (n,i,x) = dest_cnode_t cn in List.concat(tree_to_leaves (Node(n)))) ctx in
map_of(List.concat leaves))"

(* FIXME tr: above should use tree to map fun *)

(* FIXME tr: use tree_stack_t for context_t *)


(* FIXME move elsewhere *)
(*begin focus definition*)
datatype 'f focus_t = Focus 'f
(*end focus definition*)



(*begin treestack definition*)
datatype 'f tree_stack = Tree_stack "'f focus_t * context_t"
(*end treestack definition*)

definition is_subnode 
 :: "node_t => (node_t * nat) => bool"
where
"is_subnode n pi == (
  let ((ks,rs),i) = pi in
  Node n = (rs!i))"

(* FIXME in above, make sure is is an index *)


definition dest_ts :: "'f tree_stack => 'f * context_t" where
"dest_ts ts == (case ts of Tree_stack((Focus f),c) => (f,c))"


end
(* tree_stack_src ends here *)
