theory Tree
imports A_start_here Constants_and_size_types Key_value
begin

(* We need two models for trees: the algebraic datatype model, and the
"blocks and pointers" model. This is the ADT model. *)

(* small node or leaf ----------------------------------------------- *)

(* `min_size_t` is a datatype which flags whether nodes and leaves
are small or not; a small root can potentially have no children *)

datatype min_size_t = 
  Small_root_node_or_leaf
  | Small_node
  | Small_leaf

type_synonym ms_t = "min_size_t option"

(* tree algebraic datatype ------------------------------------------ *)

(* NOTE an alternative might be tree = Tree of (...tree...,_) dnode. For the
moment we keep this abstract tree type separate. *)

(*:bc:*)
datatype ('k,'v) tree = 
  Node "('k list * ('k,'v) tree list)" 
  | Leaf "('k*'v)list"
(*:bd:*)

type_synonym ('k,'v) t = "('k,'v) tree"

type_synonym ('k,'v) node = "('k list * ('k,'v) tree list)"
type_synonym ('k,'v) leaf = "('k*'v)list"

fun dest_Node :: "('k,'v) tree \<Rightarrow> ('k list * ('k,'v) tree list)" where
"dest_Node (Node(ks,rs)) = (ks,rs)" | 
"dest_Node (Leaf _) = (failwith (STR ''dest_Node''))"

fun dest_Leaf :: "('k,'v) tree \<Rightarrow> ('k*'v) list" where
"dest_Leaf (Leaf(kvs)) = kvs" | 
"dest_Leaf _ = (failwith (STR ''dest_Leaf''))"

fun is_Leaf :: "('k,'v)tree \<Rightarrow> bool" where
"is_Leaf (Leaf l) = True" |
"is_Leaf (Node _) = False"

(* patch this in generated ocaml - just use ocaml equality; in isa,
this defn suppresses the HOL.equal dictionary passing in generated
OCaml *)

definition tree_equal :: "('k,'v) tree \<Rightarrow> ('k,'v) tree \<Rightarrow> bool" where
"tree_equal t1 t2 = failwith (STR ''FIXME patch'')"



(* util ------------------------------------------------------------- *)

definition min_child_index  :: nat where "min_child_index = 0"

definition ks_to_max_child_index :: "'k list \<Rightarrow> nat" where
"ks_to_max_child_index ks = length ks"

definition subtree_indexes :: "('k,'v)node \<Rightarrow> nat list" where
"subtree_indexes node = (
  let (ks,rs) = node in 
  from_to min_child_index (ks_to_max_child_index ks))"


(* perhaps we keep this defn? otherwise painful to state keys_consistent? *)
(* FIXME this is a derived operation; where is it used? replace? FIXME this is 
derived from the splitting code in Key_value *)
definition index_to_bound :: "'k list \<Rightarrow> nat \<Rightarrow> ('k option * 'k option)" where
"index_to_bound ks i = (
  let l = if (i=min_child_index) then None else Some(ks!(i-1)) in
  let u = if (i\<ge>ks_to_max_child_index ks) then None else Some(ks!i) in (* really undefined for i> *)
  (l,u))"


(* height ----------------------------------------------------------- *)

function height :: "('k,'v)tree => nat" where
"height t0 = (
  case t0 of
  Leaf _ => (1::nat)
  | Node(_,cs) => (1 + max_of_list(List.map height cs)))"
by auto
termination
  apply(force intro:FIXME)
  done

(* tr: note that height is "special" because replacing a subtree that
  is wf_tree with another doesn't preserve balanced property *)



(* to subtrees ------------------------------------------------------ *)

fun tree_to_subtrees :: "('k,'v)tree => ('k,'v) tree list" where
"tree_to_subtrees t0 = (
  case t0 of Leaf _ => [t0]
  | Node(l,cs) => (
    t0#((List.map tree_to_subtrees cs) |> List.concat)))"

definition forall_subtrees :: "(('k,'v)tree => bool) => ('k,'v)tree => bool" where
"forall_subtrees P t = (List.list_all P (t |> tree_to_subtrees))"



(* balanced --------------------------------------------------------- *)

definition balanced_1 :: "('k,'v)tree => bool" where
"balanced_1 t0 = (
  case t0 of Leaf(l) => True
  | Node(l,cs) => (
  (cs \<noteq> []) & (List.list_all (% c. height c = height (cs!0)) cs)))"

definition balanced :: "('k,'v)tree => bool" where
"balanced t = (forall_subtrees balanced_1 t)"


(* FIXME height and balanced could be combined - might make proofs shorter? *)



(* get min size ----------------------------------------------------- *)

definition get_min_size :: "constants \<Rightarrow> (min_size_t * ('k,'v) tree) => nat" where
"get_min_size c mt = (
  let min_leaf_size = c|>min_leaf_size in
  let min_node_keys = c|>min_node_keys in
  case mt of
    (Small_root_node_or_leaf,Node _) => 1
    | (Small_root_node_or_leaf,Leaf _) => 0  (* NB this is smaller than just Small_leaf *)
    | (Small_node, Node _) => min_node_keys-1
    | (Small_leaf,Leaf _) => min_leaf_size-1
    | (_,_) => failwith (STR ''get_min_size'') )"



(* wf size, ie respects min/max bounds ------------------------------ *)

definition wf_size_1 :: "constants \<Rightarrow> ('k,'v) tree => bool" where
"wf_size_1 c t1 = (
  case t1 of
  Leaf xs => (
    let n = length xs in
    (n >= c|>min_leaf_size) & ( n <= c|>max_leaf_size))
  | Node(l,cs) => (
    let n = length l in
    (1 <= n) & (n >= c|>min_node_keys) & (n <= c|>max_node_keys)  
    (* FIXME 1\<le>n not needed since constants enforce this *) ))"

(* NOTE this treats the root differently, depending on ms; wf_size_1 has no ms *)
definition wf_size :: "constants \<Rightarrow> ms_t => ('k,'v) tree => bool" where
"wf_size c ms t0 = (
  case ms of
  None => (forall_subtrees (wf_size_1 c) t0)
  | Some m => (
    let min = get_min_size c (m,t0) in
    case t0 of 
    Leaf xs =>
      let n = length xs in
      (min <= n) & (n <= c|>max_leaf_size)
    | Node(l,cs) => (
      let n = length l in
      (min <= n) & (n <= c|>max_node_keys) 
      & (List.list_all (forall_subtrees (wf_size_1 c)) cs)) ))"



(* wf_ks_rs, ie |rs|=|ks|+1 ----------------------------------------- *)

definition wf_ks_rs_1 :: "('k,'v)tree => bool" where
"wf_ks_rs_1 t0 = (
  case t0 of Leaf _ => True | Node(l,cs) => ((1+ length l) = (length cs)))"

definition wf_ks_rs :: "('k,'v)tree => bool" where
"wf_ks_rs t0 = (forall_subtrees wf_ks_rs_1 t0)"




(* keys in tree (nodes and leaves) ---------------------------------- *)

(* NOTE we return the keys as a list so that we can use this to check 
keys_ordered *)

definition keys_1 :: "('k,'v) tree => 'k list" where
"keys_1 t0 = (case t0 of Leaf xs => (List.map fst xs) | Node (l,cs) => (l))"

definition keys :: "('k,'v) tree => 'k list" where
"keys t0 = (t0 |> tree_to_subtrees|> (List.map keys_1) |> List.concat)" 



(* keys consistent ie node keys bounds subtrees --------------------- *)

definition keys_consistent_1 :: "'k ord \<Rightarrow> ('k,'v) tree => bool" where
"keys_consistent_1 cmp t0 = (
case t0 of Leaf(l) => True
| Node(ks,rs) => (
  ! i : set(subtree_indexes (ks,rs)). 
  let (l,u) = index_to_bound ks i in
  check_keys cmp l (set (keys(rs!i))) u))"

(* NOTE this is usually the most difficult part of wf to prove *)
definition keys_consistent :: "'k ord \<Rightarrow> ('k,'v) tree => bool" where
"keys_consistent cmp t = (forall_subtrees (keys_consistent_1 cmp) t)"




(* keys_ordered ie in nodes and leaves the keys are sorted ---------- *)

definition keys_ordered_1 :: "'k ord \<Rightarrow> ('k,'v) tree => bool" where
"keys_ordered_1 cmp t0 = (t0 |> keys_1 |> ordered_key_list cmp)"

definition keys_ordered :: "'k ord \<Rightarrow> ('k,'v)tree => bool" where
"keys_ordered cmp t = (forall_subtrees (keys_ordered_1 cmp) t)"




(* wellformed_tree -------------------------------------------------- *)

(* This is the main wellformedness constraint *)

definition wf_tree :: "constants \<Rightarrow> ms_t \<Rightarrow> 'k ord => ('k,'v) tree => bool" where
"wf_tree c ms cmp t0 = (
  let b1 = wf_size c ms t0 in
  let b2 = wf_ks_rs t0 in
  let b3 = balanced t0 in
  let b4 = keys_consistent cmp t0 in
  let b5 = keys_ordered cmp t0 in
  let wf = b1&b2&b3&b4&b5 in
  wf)"



(* tree_to_leaves, tree_to_map etc ---------------------------------- *)

fun tree_to_leaves :: "('k,'v)tree => ('k,'v) leaf list" where
"tree_to_leaves t0 = (
  case t0 of
  Node(l,cs) => ((List.map tree_to_leaves cs) |> List.concat)
  | Leaf(l) => [l])"
  
  
declare tree_to_leaves.simps[simp del]

lemma [simp]: 
  "tree_to_leaves (Node(l,cs)) =  ((cs |> (List.map tree_to_leaves)) |> List.concat)" sorry

(* this property enables easy leaves_to_map manipulation *)
(*
definition nice_leaves :: "leaf_lbl_t list \<Rightarrow> bool" where
"nice_leaves ls = (distinct (ls |> List.concat |> List.map fst))"
*)

definition tree_to_kvs :: "('k,'v) tree \<Rightarrow> ('k * 'v) list" where
"tree_to_kvs t = (t |> tree_to_leaves |> concat)"

definition tree_to_keys :: "('k,'v)tree \<Rightarrow> 'k set" where
"tree_to_keys t =  (t|>tree_to_kvs|>map fst|>set)"


(* FIXME use tree_to_keys? *)
definition trees_to_keys :: "('k,'v) tree list \<Rightarrow> 'k set" where
"trees_to_keys ts = ts|>(map tree_to_kvs)|>concat|>map fst|>set"

definition tree_to_map :: "('k,'v)tree \<Rightarrow> ('k,'v) map" where
"tree_to_map t = (t|>tree_to_kvs|>map_of)"


end