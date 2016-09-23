theory Tree_stack imports Tree begin

(* the bound is a bound on ALL children, not just rs!i *)
datatype cnode_t = Cnode "node_t * nat * bound_t"  (* n,i,b *)


definition dest_cnode_t :: "cnode_t \<Rightarrow> node_t * nat * bound_t" where
"dest_cnode_t c = (case c of Cnode (n,i,b) \<Rightarrow> (n,i,b))"

(* FIXME remove *)
type_synonym context_t = "cnode_t list"

type_synonym tree_stack_t = "cnode_t list"




(* bound from cnode ---------------------------------------- *)

(* make sure we use the existing bound in case i is extremal *)
definition cnode_to_bound :: "cnode_t \<Rightarrow> bound_t" where
"cnode_to_bound cn = (
  let (n,i,b) = dest_cnode_t cn in
  let (ks,rs) = n in
  index_to_bound ks i |> with_parent_bound b)"


(* bound from tree stack ---- *)

(* FIXME disappears ?*)
(*
definition get_parent_bounds :: "context_t \<Rightarrow> bound_t" where
"get_parent_bounds ts = (
  case ts of 
  Nil \<Rightarrow> (None,None)
  | cn#_ \<Rightarrow> (let (n,i,x) = dest_cnode_t cn in x))"
*)


(* wellformed_cnode ---------------------------------------- *)



(* FIXME adjust scala defns *)      
definition wellformed_cnode :: "ms_t => cnode_t => bool " where
"wellformed_cnode ms cn = (
  let (n1,i1,x1) = dest_cnode_t cn in 
  let (l1,u1) = x1 in
  let (ks,rs) = n1 in
  let b1 = wellformed_tree ms (Node(ks,rs)) in  (* FIXME wellformed_kv_tree *)
  let b2 = i1 : set(subtree_indexes (ks,rs)) in
  let b3 = check_keys l1 (keys (Node(ks,rs))) u1 in
  b1&b2&b3)
"

definition ts_to_ms :: "tree_stack_t \<Rightarrow> ms_t" where
"ts_to_ms ts = (case ts of Nil \<Rightarrow> (Some Small_root_node_or_leaf) | _ \<Rightarrow> None)"

lemma ts_to_ms_def_2: "
  (ts_to_ms Nil = (Some Small_root_node_or_leaf)) &
  (! x xs. ts_to_ms (x#xs) = None)"
  apply(simp add:ts_to_ms_def)
  done


(* wellformed_context ---------------------------------------- *)


fun wellformed_context :: "context_t => bool" where
"wellformed_context xs = (
  case xs of Nil \<Rightarrow> True
  | cn#cns \<Rightarrow> (wellformed_cnode (ts_to_ms cns) cn & wellformed_context cns))"
(*end wfcontext definition*)

lemma wellformed_context_def_2: "
  (wellformed_context  Nil = True) &
  (wellformed_context (cn#cns) = (wellformed_cnode (ts_to_ms cns) cn & wellformed_context cns))"
by simp


end
(* tree_stack_src ends here *)
