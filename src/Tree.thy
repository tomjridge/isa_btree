theory Tree
imports Util Constants Key_value
begin

(* begin tree types*)
type_synonym leaf_lbl_t = "(key * value_t) list"
type_synonym node_lbl_t = "key list"


datatype Tree = Node "node_lbl_t * Tree list" | Leaf "leaf_lbl_t"
(* end tree types*)

(* label at node and children ie a Node *)
type_synonym node_t = "node_lbl_t * Tree list"

(* util ---------------------------------------- *)

definition min_child_index  :: nat where "min_child_index = 0"

definition max_child_index :: "node_t \<Rightarrow> nat" where
"max_child_index node = (
  let (ks,rs) = node in
  length rs - 1)"


definition subtree_indexes :: "node_t \<Rightarrow> nat list" where
"subtree_indexes node = from_to min_child_index (max_child_index node)"


(* height ---------------------------------------- *)

(*begin height definition*)
function height :: "Tree => nat" where
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

(* setting up tree_kv.to_map ---------------------------------------- *)

function tree_to_leaves :: "Tree => leaf_lbl_t list" where
"tree_to_leaves t0 = (
  case t0 of
  Node(l,cs) => ((cs |> (List.map tree_to_leaves)) |> List.concat)
  | Leaf(l) => [l])
"
by auto
termination
  apply(force intro:FIXME)
  done


(* conversion to map ---------------------------------------- *)

definition tree_to_map
 :: "Tree => (key,value_t) map"
where
"tree_to_map t = (
map_of (List.concat(tree_to_leaves t))
)"


(* to subtrees ---------------------------------------- *)

(* begin t2s *)
function tree_to_subtrees :: "Tree => Tree list" where
"tree_to_subtrees t0 = (
case t0 of
Leaf _ => [t0]
| Node(l,cs) => (
t0#((List.map tree_to_subtrees cs) |> List.concat)
)
)
"
(* end t2s *)
by auto
termination
  apply(force intro:FIXME)
  done

definition forall_subtrees :: "(Tree => bool) => Tree => bool" where
"forall_subtrees P t == (
List.list_all P (t |> tree_to_subtrees) 
)"

(* balanced ---------------------------------------- *)

(*begin wfbalanced*)
definition balanced_1 :: "Tree => bool" where
"balanced_1 t0 == (
case t0 of Leaf(l) => True
| Node(l,cs) => (
(cs = []) | (
List.list_all (% c. height c = height (cs!0)) cs))
)"

definition balanced :: "Tree => bool" where
"balanced t == forall_subtrees balanced_1 t"
(*end wfbalanced*)


(* get min size ---------------------------------------- *)

(* begin wfsize*)
definition get_min_size :: "(min_size_t * Tree) => nat" where
"
get_min_size mt == (
case mt of
(Small_root_node_or_leaf,Node _) => 1
| (Small_root_node_or_leaf,Leaf _) => 0
| (Small_node, Node _) => min_node_keys-1
| (Small_leaf,Leaf _) => min_leaf_size-1
| (_,_) => undefined  (* FIXME failwith *)
)
"

(* wf size ---------------------------------------- *)

definition wf_size_1 :: "Tree => bool" where
"wf_size_1 t1 == (
case t1 of
Leaf xs => (
let n = length xs in
(n >= min_leaf_size) & ( n <= max_leaf_size))
| Node(l,cs) => (
let n = length l in
(1 <= n) & (n >= min_node_keys) & (n <= max_node_keys)  (* FIXME 1\<le>n not needed since constants enforce this *)

)
)
"

definition wf_size :: "ms_t => Tree => bool" where
"wf_size ms t0 == (
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
(* end wfsize *)

(* wf_ks_rs ---------------------------------------- *)

(* begin wfksrs*)
definition wf_ks_rs_1 :: "Tree => bool" where
"wf_ks_rs_1 t0 == (
case t0 of Leaf _ => True
| Node(l,cs) => ((1+ length l) = (length cs))
)"

definition wf_ks_rs :: "Tree => bool" where
"wf_ks_rs t0 == forall_subtrees wf_ks_rs_1 t0"
(* end wfksrs*)
export_code wf_ks_rs in Scala module_name Problem file "/tmp/Problem.scala"


(* keys ---------------------------------------- *)

(*begin wfkeysconsistent*)
definition keys_1 :: "Tree => key list" where
"keys_1 t0 == (case t0 of
Leaf xs => (List.map fst xs)
| Node (l,cs) => (l)
)"

definition keys :: "Tree => key list" where
"keys t0 == (t0 |> tree_to_subtrees|> (List.map keys_1) |> List.concat)
" 

(* keys consistent ---------------------------------------- *)

definition key_indexes :: "Tree => nat list" where
"key_indexes t == (
  case t of 
  Leaf xs => (from_to 0 (length xs - 1))
  | Node (l,_) => (from_to 0 (length l - 1)))"  

definition get_lu_for_child :: "(node_t*nat) \<Rightarrow> (key option * key option)" where
"get_lu_for_child ni = (
  let ((ks,rs),i) = ni in
  let l = if (i=min_child_index) then None else Some(ks!(i-1)) in
  let u = if (i=max_child_index (ks,rs)) then None else Some(ks!i) in
  (l,u))"

definition keys_consistent_1 :: "Tree => bool" where
"keys_consistent_1 t0 == (
case t0 of Leaf(l) => True
| Node(ks,rs) => (
  ! i : set(subtree_indexes (ks,rs)). 
  let (l,u) = get_lu_for_child((ks,rs),i) in
  check_keys l (keys(rs!i)) u))
"

definition keys_consistent :: "Tree => bool" where
"keys_consistent t == forall_subtrees keys_consistent_1 t"
(*end wfkeysconsistent*)


(* keys_ordered ---------------------------------------- *)

(* begin wfordered*)
definition keys_ordered_1 :: "Tree => bool" where
"keys_ordered_1 t0 == (
t0 |> keys_1 |> ordered_key_list)"

definition keys_ordered :: "Tree => bool" where
"keys_ordered t == forall_subtrees keys_ordered_1 t"
(*end wfordered*)


(* wf_kv_tree ---------------------------------------- *)

(* begin wf tree definition *)
definition wellformed_tree :: "ms_t => Tree => bool" where
"wellformed_tree ms t0 == (
let b1 = wf_size ms t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"
(* end wf tree definition *)

end

