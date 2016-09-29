theory Tree_stack imports Tree begin

type_synonym  leaves_t = "leaf_lbl_t list" 

(* the bound l,u is a bound on ALL children, not just rs!i; l,u could be calculated from the ts *)
datatype cnode_t = Cnode "leaves_t * key option * key list * Tree list * nat * key option * leaves_t"  (* xs,l,ks,rs,i,u,zs *)


definition dest_cnode :: "cnode_t \<Rightarrow> leaves_t * key option * key list * Tree list * nat * key option * leaves_t" where
"dest_cnode c = (case c of Cnode (xs,l,ks,rs,i,u,zs) \<Rightarrow> (xs,l,ks,rs,i,u,zs))"

lemma dest_cnode_t_def_2: "dest_cnode (Cnode(xs,l,ks,rs,i,u,zs)) = (xs,l,ks,rs,i,u,zs)"
apply(simp add: dest_cnode_def)
done

(* FIXME remove *)

type_synonym tree_stack_t = "cnode_t list"


(* search_key_to_index ------ *)

(*tr: assumes xs are sorted; returns list length if not found*)
(*begin search key to index definition *)
definition search_key_to_index :: "key list => key => nat" where
"search_key_to_index ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  i')"
(*end search key to index definition *)


(* bound from cnode ---------------------------------------- *)

(* make sure we use the existing bound in case i is extremal *)
definition cnode_to_bound :: "cnode_t \<Rightarrow> bound_t" where
"cnode_to_bound cn = (
  let (xs,l,ks,rs,i,u,zs) = dest_cnode cn in
  index_to_bound ks i |> with_parent_bound (l,u))"



(* wellformed_cnode ---------------------------------------- *)


(* FIXME adjust scala defns *)      
definition wellformed_cnode :: "key \<Rightarrow> ms_t => cnode_t => bool " where
"wellformed_cnode k0 ms cn = (
  let (xs,l,ks,rs,i,u,zs) = dest_cnode cn in 
  let b1 = wellformed_tree ms (Node(ks,rs)) in 
  let b2 = search_key_to_index ks k0 = i in
  let b3 = check_keys_2 (xs|>leaves_to_map|>dom) l (set(k0#keys(Node(ks,rs)))) u (zs|>leaves_to_map|>dom) in  (* k0? *)
  b1&b2&b3)
"


(* wellformed_context ---------------------------------------- *)


definition ts_to_ms :: "tree_stack_t \<Rightarrow> ms_t" where
"ts_to_ms ts = (case ts of Nil \<Rightarrow> (Some Small_root_node_or_leaf) | _ \<Rightarrow> None)"

lemma ts_to_ms_def_2: "
  (ts_to_ms Nil = (Some Small_root_node_or_leaf)) &
  (! x xs. ts_to_ms (x#xs) = None)"
  apply(simp add:ts_to_ms_def)
  done


fun wellformed_ts :: "key \<Rightarrow> tree_stack_t => bool" where
"wellformed_ts k0 xs = (
  case xs of Nil \<Rightarrow> True
  | cn#cns \<Rightarrow> (wellformed_cnode k0 (ts_to_ms cns) cn & wellformed_ts k0 cns))"
(*end wfcontext definition*)

lemma wellformed_ts_def_2: "
  (wellformed_ts k0 Nil = True) &
  (wellformed_ts k0 (cn#cns) = (wellformed_cnode k0 (ts_to_ms cns) cn & wellformed_ts k0 cns))"
by simp


(* ts_to_t0 ------------------------------------ *)

(* get the initial tree from which the ts was formed *)
(*
definition ts_to_t0 :: "tree_stack_t \<Rightarrow> node_t option" where
"ts_to_t0 ts = (
  case ts of
  Nil \<Rightarrow> None
  | _ \<Rightarrow> ( 
    let cn = last ts in
    let (l,ks,rs,i,u) = dest_cnode cn in
    Some(ks,rs)))
"
*)

(* stack reassembly ----------------------------------- *)

fun reass :: "Tree \<Rightarrow> tree_stack_t \<Rightarrow> Tree" where
"reass t ts = (
  case ts of
  Nil \<Rightarrow> t
  | cn#cns \<Rightarrow> (
    let (_,_,ks,rs,i,_,_) = dest_cnode cn in
    let t2 = Node(ks,rs[i:=t]) in
    reass t2 cns)
)"


(* lemmas ------------------------------------------------ *)

definition lemma_reass_1 :: bool where
"lemma_reass_1 = (! ts t.
  ? xs zs. (reass t ts) |> tree_to_leaves = xs@(tree_to_leaves t)@zs)"



end
(* tree_stack_src ends here *)
