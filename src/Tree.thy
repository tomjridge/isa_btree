theory Tree
imports Util Constants Key_value
begin

type_synonym leaf_lbl_t = "(key * value_t) list"
type_synonym node_lbl_t = "key list"


datatype Tree = Node "node_lbl_t * Tree list" | Leaf "leaf_lbl_t"

(* label at node and children ie a Node *)
type_synonym node_t = "node_lbl_t * Tree list"


function height :: "Tree \<Rightarrow> nat" where
"height t0 = (
case t0 of
Leaf _ \<Rightarrow> (1::nat)
| Node(_,cs) \<Rightarrow> (1 + Max(set(List.map height cs)))
)"
by auto
termination
  apply(force intro:FIXME)
  done

function tree_to_leaves :: "Tree \<Rightarrow> leaf_lbl_t list" where
"tree_to_leaves t0 = (case t0 of
Node(l,cs) \<Rightarrow> (
(cs |> (List.map tree_to_leaves)) |> List.concat
)
| Leaf(l) \<Rightarrow> [l]
)
"
by auto
termination
  apply(force intro:FIXME)
  done

(*
definition update_child_at_position :: "node_lbl_t * Tree list \<Rightarrow> nat \<Rightarrow> Tree \<Rightarrow> Tree" where
"update_child_at_position node i child == FIXME"
*)

function tree_to_subtrees :: "Tree \<Rightarrow> Tree list" where
"tree_to_subtrees t0 = (
case t0 of
Leaf _ \<Rightarrow> [t0]
| Node(l,cs) \<Rightarrow> (
t0#((List.map tree_to_subtrees cs) |> List.concat)
)
)
"
by auto
termination
  apply(force intro:FIXME)
  done

definition forall_subtrees :: "(Tree \<Rightarrow> bool) \<Rightarrow> Tree \<Rightarrow> bool" where
"forall_subtrees P t == (
List.list_all P (t |> tree_to_subtrees) 
)"

definition balanced_1 :: "Tree \<Rightarrow> bool" where
"balanced_1 t0 == (
case t0 of Leaf(l) \<Rightarrow> True
| Node(l,cs) \<Rightarrow> (
(cs = []) | (
List.list_all (% c. height c = height (cs!0)) cs))
)"

definition balanced :: "Tree \<Rightarrow> bool" where
"balanced t == forall_subtrees balanced_1 t"




definition wf_size_1 :: "Tree \<Rightarrow> bool" where
"wf_size_1 t1 == (
case t1 of
Leaf xs \<Rightarrow> (
let n = length xs in
(n \<ge> min_leaf_size) & ( n \<le> max_leaf_size))
| Node(l,cs) \<Rightarrow> (
let n = length l in
(1 \<le> length l) & (n \<ge> min_node_keys) & (n \<le> max_node_keys)

)
)
"

(* root may be small *)
datatype rmbs_t = Rmbs bool

definition wf_size :: "rmbs_t \<Rightarrow> Tree \<Rightarrow> bool" where
"wf_size rmbs t0 == (
case rmbs of
Rmbs False \<Rightarrow> (forall_subtrees wf_size_1 t0)
| Rmbs True \<Rightarrow> (
case t0 of 
Leaf(l) \<Rightarrow> (length l \<le> Constants.max_leaf_size)
| Node(l,cs) \<Rightarrow> (
1 \<le> length l &
length l \<le> max_node_keys 
& List.list_all wf_size_1 cs)
))"

definition wf_ks_rs_1 :: "Tree \<Rightarrow> bool" where
"wf_ks_rs_1 t0 == (
case t0 of Leaf _ \<Rightarrow> True
| Node(l,cs) \<Rightarrow> ((1+ length l) = (length cs))
)"

definition wf_ks_rs :: "Tree \<Rightarrow> bool" where
"wf_ks_rs t0 == forall_subtrees wf_ks_rs_1 t0"

definition keys_1 :: "Tree \<Rightarrow> key list" where
"keys_1 t0 == (case t0 of
Leaf xs \<Rightarrow> (List.map fst xs)
| Node (l,cs) \<Rightarrow> (l)
)"

definition keys :: "Tree \<Rightarrow> key list" where
"keys t0 == (t0 |> tree_to_subtrees|> (List.map keys_1) |> List.concat)
" 

definition key_indexes :: "Tree \<Rightarrow> nat list" where
"key_indexes t == (
  case t of 
  Leaf xs \<Rightarrow> (upt 0 (length xs))
  | Node (l,_) \<Rightarrow> (upt 0 (length l)))"  

definition keys_consistent_1 :: "Tree \<Rightarrow> bool" where
"keys_consistent_1 t0 == (
case t0 of Leaf(l) \<Rightarrow> True
| Node(label,children) \<Rightarrow> (
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

definition keys_consistent :: "Tree \<Rightarrow> bool" where
"keys_consistent t == forall_subtrees keys_consistent_1 t"


definition keys_ordered_1 :: "Tree \<Rightarrow> bool" where
"keys_ordered_1 t0 == (
let is = set (butlast (key_indexes t0)) in
case t0 of
Leaf xs \<Rightarrow>
  let ks = (xs |> List.map fst) in
  ! i : is. key_lt (ks!i) (ks!(i+1))
| Node (ks,_) \<Rightarrow> 
  ! i : is . key_lt (ks!i) (ks!(i+1))
)
"

definition keys_ordered :: "Tree \<Rightarrow> bool" where
"keys_ordered t == forall_subtrees keys_ordered_1 t"

(*
definition wellformed_subtree :: "Tree \<Rightarrow> bool" where
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

definition wellformed_tree :: "rmbs_t \<Rightarrow> Tree \<Rightarrow> bool" where
"wellformed_tree rmbs t0 == (
let b1 = wf_size rmbs t0 in
let b2 = wf_ks_rs t0 in
let b3 = balanced t0 in
let b4 = keys_consistent t0 in
let b5 = keys_ordered t0 in
let wf = b1&b2&b3&b4&b5 in
wf
)"


end
