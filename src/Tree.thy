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

function tree_to_leaves :: "Tree => leaf_lbl_t list" where
"tree_to_leaves t0 = (case t0 of
Node(l,cs) => (
(cs |> (List.map tree_to_leaves)) |> List.concat
)
| Leaf(l) => [l]
)
"
by auto
termination
  apply(force intro:FIXME)
  done

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

(* begin wfsize*)
definition wf_size_1 :: "Tree => bool" where
"wf_size_1 t1 == (
case t1 of
Leaf xs => (
let n = length xs in
(n >= min_leaf_size) & ( n <= max_leaf_size))
| Node(l,cs) => (
let n = length l in
(1 <= n) & (n >= min_node_keys) & (n <= max_node_keys)

)
)
"

(* root may be small *)
datatype rmbs_t = Rmbs bool

definition wf_size :: "rmbs_t => Tree => bool" where
"wf_size rmbs t0 == (
case rmbs of
Rmbs False => (forall_subtrees wf_size_1 t0)
| Rmbs True => (
case t0 of 
Leaf xs =>
let n = length xs in
(n <= max_leaf_size)
| Node(l,cs) => (
let n = length l in
(1 <= n) & (n <= max_node_keys) 
& (List.list_all (forall_subtrees wf_size_1) cs))
))"
(* end wfsize *)

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


(*begin wfkeysconsistent*)
definition keys_1 :: "Tree => key list" where
"keys_1 t0 == (case t0 of
Leaf xs => (List.map fst xs)
| Node (l,cs) => (l)
)"

definition keys :: "Tree => key list" where
"keys t0 == (t0 |> tree_to_subtrees|> (List.map keys_1) |> List.concat)
" 

definition key_indexes :: "Tree => nat list" where
"key_indexes t == (
  case t of 
  Leaf xs => (upt 0 (length xs))
  | Node (l,_) => (upt 0 (length l)))"  

definition keys_consistent_1 :: "Tree => bool" where
"keys_consistent_1 t0 == (
case t0 of Leaf(l) => True
| Node(label,children) => (
let b1 = (! i : set(key_indexes t0). 
  let k0 = label!i in
  let kls = keys(children!i) in
  check_keys None kls (Some k0))
in
let b2 = (! i : set(key_indexes t0). 
  let k0 = label!i in
  let krs = keys(children!(i+1)) in
  check_keys (Some k0) krs None)
in
b1 & b2
))
"

definition keys_consistent :: "Tree => bool" where
"keys_consistent t == forall_subtrees keys_consistent_1 t"
(*end wfkeysconsistent*)

(* begin wfordered*)
definition keys_ordered_1 :: "Tree => bool" where
"keys_ordered_1 t0 == (
let is = set (butlast (key_indexes t0)) in
case t0 of
Leaf xs =>
  let ks = (xs |> List.map fst) in
  ! i : is. key_lt (ks!i) (ks!(i+1))
| Node (ks,_) => 
  ! i : is . key_lt (ks!i) (ks!(i+1))
)
"

definition keys_ordered :: "Tree => bool" where
"keys_ordered t == forall_subtrees keys_ordered_1 t"
(*end wfordered*)

(*
definition wellformed_subtree :: "Tree => bool" where
"wellformed_subtree t0 == (
let b1 = wf_size t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"
*)

(* begin wf tree definition *)
definition wellformed_tree :: "rmbs_t => Tree => bool" where
"wellformed_tree rmbs t0 == (
let b1 = wf_size rmbs t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"
(* end wf tree definition *)

end
