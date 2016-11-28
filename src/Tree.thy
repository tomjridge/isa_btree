theory Tree
imports Util Constants Key_value
begin

type_synonym leaf_lbl_t = "kvs_t"

type_synonym node_lbl_t = "key list"

type_synonym leaves = "kvs list" (* what you get from the fringe of the tree *)

datatype tree = Node "node_lbl_t * tree list" | Leaf "leaf_lbl_t"

type_synonym t = tree

(*
(* nonsense to get code export to work *)
instantiation Tree :: equal begin
definition equal_Tree :: "Tree \<Rightarrow> Tree \<Rightarrow> bool" where "equal_Tree = (op = )" 
instance by intro_classes (simp add: equal_Tree_def)
end
*)

(* label at node and children ie a Node *)
type_synonym node_t = "node_lbl_t * tree list"

fun dest_Node :: "tree \<Rightarrow> node_t" where
"dest_Node (Node(ks,rs)) = (ks,rs)" | 
"dest_Node (Leaf _) = (failwith ''dest_Node'')"

fun dest_Leaf :: "tree \<Rightarrow> kvs_t" where
"dest_Leaf (Leaf(kvs)) = kvs" | 
"dest_Leaf _ = (failwith ''dest_Leaf'')"

fun is_Leaf :: "tree \<Rightarrow> bool" where
"is_Leaf (Leaf l) = True" |
"is_Leaf (Node _) = False"

type_synonym trees = "tree list"



(* util ---------------------------------------- *)

definition min_child_index  :: nat where "min_child_index = 0"

definition ks_to_max_child_index :: "key list \<Rightarrow> nat" where
"ks_to_max_child_index ks = length ks"

definition subtree_indexes :: "node_t \<Rightarrow> nat list" where
"subtree_indexes node = (let (ks,rs) = node in from_to min_child_index (ks_to_max_child_index ks))"


(* perhaps we keep this defn? otherwise painful to state keys_consistent? *)
definition index_to_bound :: "key list \<Rightarrow> nat \<Rightarrow> (key option * key option)" where
"index_to_bound ks i = (
  let l = if (i=min_child_index) then None else Some(ks!(i-1)) in
  let u = if (i\<ge>ks_to_max_child_index ks) then None else Some(ks!i) in (* really undefined for i> *)
  (l,u))"


(* height ---------------------------------------- *)

(*begin height definition*)
function height :: "tree => nat" where
"height t0 = (
  case t0 of
  Leaf _ => (1::nat)
  | Node(_,cs) => (1 + Max(set(List.map height cs)))
)"
(*end height definition*)
by auto
termination
  apply(force intro:FIXME)
  done

(* tr: note that height is "special" because replacing a subtree that is wf_tree with another doesn't
  preserve balanced property *)

(* to subtrees ---------------------------------------- *)

function tree_to_subtrees :: "tree => tree list" where
"tree_to_subtrees t0 = (
  case t0 of Leaf _ => [t0]
  | Node(l,cs) => (
    t0#((List.map tree_to_subtrees cs) |> List.concat)))
"
by auto
termination
  apply(force intro:FIXME)
  done

definition forall_subtrees :: "(tree => bool) => tree => bool" where
"forall_subtrees P t == (List.list_all P (t |> tree_to_subtrees))"

(* balanced ---------------------------------------- *)

(*begin wfbalanced*)
definition balanced_1 :: "tree => bool" where
"balanced_1 t0 == (
  case t0 of Leaf(l) => True
  | Node(l,cs) => (
  (cs = []) | (List.list_all (% c. height c = height (cs!0)) cs)))"

definition balanced :: "tree => bool" where
"balanced t = assert_true t (forall_subtrees balanced_1 t)"
(*end wfbalanced*)


(* get min size ---------------------------------------- *)

(* begin wfsize*)
definition get_min_size :: "(min_size_t * tree) => nat" where
"
get_min_size mt == (
case mt of
(Small_root_node_or_leaf,Node _) => 1
| (Small_root_node_or_leaf,Leaf _) => 0  (* NB this is smaller than just Small_leaf *)
| (Small_node, Node _) => min_node_keys-1
| (Small_leaf,Leaf _) => min_leaf_size-1
| (_,_) => undefined  (* FIXME failwith *)
)
"

(* wf size ---------------------------------------- *)

definition wf_size_1 :: "tree => bool" where
"wf_size_1 t1 == (
  case t1 of
  Leaf xs => (
    let n = length xs in
    (n >= min_leaf_size) & ( n <= max_leaf_size))
  | Node(l,cs) => (
    let n = length l in
    (1 <= n) & (n >= min_node_keys) & (n <= max_node_keys)  (* FIXME 1\<le>n not needed since constants enforce this *)
))
"

definition wf_size :: "ms_t => tree => bool" where
"wf_size ms t0 = assert_true (ms,t0) (
  case ms of
  None => (forall_subtrees wf_size_1 t0)
  | Some m => (
    let min = get_min_size (m,t0) in
    case t0 of 
    Leaf xs =>
      let n = length xs in
      (min <= n) & (n <= max_leaf_size)
    | Node(l,cs) => (
      let n = length l in
      (min <= n) & (n <= max_node_keys) 
      & (List.list_all (forall_subtrees wf_size_1) cs))
))"


(* wf_ks_rs ---------------------------------------- *)

definition wf_ks_rs_1 :: "tree => bool" where
"wf_ks_rs_1 t0 == (
  case t0 of Leaf _ => True | Node(l,cs) => ((1+ length l) = (length cs)))"

definition wf_ks_rs :: "tree => bool" where
"wf_ks_rs t0 = assert_true t0 (forall_subtrees wf_ks_rs_1 t0)"

(*
export_code wf_ks_rs in Scala module_name Problem file "/tmp/Problem.scala"
*)

(* keys ---------------------------------------- *)

definition keys_1 :: "tree => key list" where
"keys_1 t0 = (case t0 of Leaf xs => (List.map fst xs) | Node (l,cs) => (l))"

definition keys :: "tree => key list" where
"keys t0 = (t0 |> tree_to_subtrees|> (List.map keys_1) |> List.concat)" 

(* keys consistent ---------------------------------------- *)

definition keys_consistent_1 :: "tree => bool" where
"keys_consistent_1 t0 = (
case t0 of Leaf(l) => True
| Node(ks,rs) => (
  ! i : set(subtree_indexes (ks,rs)). 
  let (l,u) = index_to_bound ks i in
  check_keys l (set (keys(rs!i))) u))
"

definition keys_consistent :: "tree => bool" where
"keys_consistent t = assert_true t (forall_subtrees keys_consistent_1 t)"


(* keys_ordered ---------------------------------------- *)

definition keys_ordered_1 :: "tree => bool" where
"keys_ordered_1 t0 = (t0 |> keys_1 |> ordered_key_list)"

definition keys_ordered :: "tree => bool" where
"keys_ordered t = assert_true t (forall_subtrees keys_ordered_1 t)"


(* wf_kv_tree ---------------------------------------- *)

definition wellformed_tree :: "ms_t => tree => bool" where
"wellformed_tree ms t0 = assert_true (ms,t0) (
  let b1 = wf_size ms t0 in
  let b2 = wf_ks_rs t0 in
  let b3 = balanced t0 in
  let b4 = keys_consistent t0 in
  let b5 = keys_ordered t0 in
  let wf = b1&b2&b3&b4&b5 in
  wf
)"



(* tree_to... etc ---------------------------------------- *)


function tree_to_leaves :: "tree => leaves" where
"tree_to_leaves t0 = (
  case t0 of
  Node(l,cs) => ((cs |> (List.map tree_to_leaves)) |> List.concat)
  | Leaf(l) => [l])
"
by auto
termination
  apply(force intro:FIXME)
  done

declare tree_to_leaves.simps[simp del]

lemma [simp] : "tree_to_leaves (Node(l,cs)) =  ((cs |> (List.map tree_to_leaves)) |> List.concat)" sorry

(* this property enables easy leaves_to_map manipulation *)
(*
definition nice_leaves :: "leaf_lbl_t list \<Rightarrow> bool" where
"nice_leaves ls = (distinct (ls |> List.concat |> List.map fst))"
*)

definition tree_to_kvs :: "tree \<Rightarrow> kvs" where
"tree_to_kvs t = (t |> tree_to_leaves |> concat)"

definition tree_to_keys :: "tree \<Rightarrow> key set" where
"tree_to_keys t =  (t|>tree_to_kvs|>map fst|>set)"

definition trees_to_keys :: "trees \<Rightarrow> key set" where
"trees_to_keys ts = ts|>(map tree_to_kvs)|>concat|>map fst|>set"

definition tree_to_map :: "tree \<Rightarrow> (key,value_t) map" where
"tree_to_map t = (t|>tree_to_kvs|>map_of)"

(*
definition tss_to_leaves :: "tss_t \<Rightarrow> leaves_t" where
"tss_to_leaves tss = (tss|>concat|>map tree_to_leaves|>concat)"

definition tss_to_keys :: "tss_t \<Rightarrow> key set" where
"tss_to_keys tss = tss|>concat|>trees_to_keys"
*)

end

