theory Tree_stack imports Tree begin

datatype xtra_t = Xtra "(key option * key option)"  (* l,u *)
definition dest_xtra_t :: "xtra_t \<Rightarrow> key option * key option" where
"dest_xtra_t x = (case x of Xtra x \<Rightarrow> x)"

datatype cnode_t = Cnode "node_t * nat * xtra_t"  (* n,i,x *)
definition dest_cnode_t :: "cnode_t \<Rightarrow> node_t * nat * xtra_t" where
"dest_cnode_t c = (case c of Cnode x \<Rightarrow> x)"

(* FIXME remove *)
type_synonym context_t = "cnode_t list"

type_synonym tree_stack_t = "cnode_t list"

(* wellformed_context ---------------------------------------- *)

definition wellformed_cnode :: "ms_t => cnode_t => bool " where
"wellformed_cnode ms cn = (
  let (n,i,x) = dest_cnode_t cn in 
  let (l,u) = dest_xtra_t x in
  let (ks,rs) = n in
  let b1 = wellformed_tree ms (Node(ks,rs)) in  (* FIXME wellformed_kv_tree *)
  let b2 = i : set(subtree_indexes (ks,rs)) in
  let b3 = check_keys l (keys (rs!i)) u in
  let b4 = (
    let (l0,u0) = get_lu_for_child(n,i) in
    (if (i > min_child_index) then (l=l0) else True) &
    (if (i < max_child_index(n)) then (u=u0) else True))
  in  
  b1&b2&b3&b4)
"

definition wellformed_context_1 :: "context_t \<Rightarrow> bool" where
"wellformed_context_1 xs = (case xs of
  Nil \<Rightarrow> True
  | cn#Nil \<Rightarrow> (
    let (n,i,x) = dest_cnode_t cn in
    let (l,u) = dest_xtra_t x in
    wellformed_cnode (Some(Small_root_node_or_leaf)) cn &
    (l = None) & (u = None))
  | cn1#cn2#_ \<Rightarrow> (
    let (n1,i1,x1) = dest_cnode_t cn1 in
    let (l1,u1) = dest_xtra_t x1 in
    let (n2,i2,x2) = dest_cnode_t cn2 in
    let (l2,u2) = dest_xtra_t x2 in
    (if (i1 = min_child_index) then (l1 = l2) else True) &
    (if (i1 = max_child_index(n1)) then (u1 = u2) else True)))"


(* FIXME tr check these defns are right *)
(* FIXME defn could be improved *)
fun wellformed_context :: "context_t => bool" where
"wellformed_context xs = (
  wellformed_context_1 xs & (
    case xs of
    Nil \<Rightarrow> True
    | x#xs \<Rightarrow> wellformed_context xs))"
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
