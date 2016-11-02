theory Insert_tree_stack
imports Find_tree_stack "~~/src/HOL/Library/Code_Target_Nat"
begin

type_synonym inserting_two_t =  "Tree * key * Tree"

datatype its_t = 
  Inserting_one "Tree"
  | Inserting_two "Tree * key * Tree"

type_synonym its_focus_t = "its_t core_t"

datatype its_state_t =
  Its_down "fts_state_t * value_t"
  | Its_up "its_focus_t * tree_stack_t"

type_synonym its_down_t = "fts_state_t * value_t"
  
type_synonym its_up_t = "its_focus_t * tree_stack_t"


definition its_to_keys :: "its_t \<Rightarrow> key set" where
"its_to_keys its = (
  case its of
  Inserting_one t \<Rightarrow> (t|>tree_to_keys)
  | Inserting_two (t1,_,t2) \<Rightarrow> ((t1|>tree_to_keys) Un (t2|>tree_to_keys))
)"


(* its height ------------------------- *)

definition its_to_h :: "its_t \<Rightarrow> nat" where
"its_to_h its = (
  case its of 
  Inserting_one t \<Rightarrow> (height t)
  | Inserting_two (t1,_,t2) \<Rightarrow> (height t1)  (* wf implies h t1 = h t2 *)
)"


(* wellformedness ---------------------------------------- *)

definition wellformed_its :: " bool \<Rightarrow> its_t \<Rightarrow> bool" where
"wellformed_its stack_empty its = (
  case its of
  Inserting_one t => (
    let ms = case stack_empty of 
      True => (Some Small_root_node_or_leaf)
      | _ => None
    in
    wellformed_tree ms t)
  | Inserting_two (t1,k,t2) => (
    (height t2 = height t1) & 
    wellformed_tree None t1 & 
    wellformed_tree None t2 & 
    check_keys None (t1|>tree_to_keys) (Some k) & 
    check_keys (Some k) (t2|>tree_to_keys) None)
)"


definition wellformed_its_focus :: "key \<Rightarrow> bool \<Rightarrow> its_focus_t => bool" where
"wellformed_its_focus k0 stack_empty f = (
  let its = f|>f_t in
  wf_core k0 (its|>its_to_keys) f &
  wellformed_its stack_empty its 
)"


definition wellformed_iup_1 :: "its_up_t => bool" where
"wellformed_iup_1 iu = (
  let (f,stk) = iu in
  case stk of
  Nil \<Rightarrow> True
  | p#xs \<Rightarrow> (
    (f|>without_t = (mk_child p|>without_t)) &
    (f|>f_t|>its_to_h = (p|>mk_child|>f_t|>height))
  )
)"
  

definition wellformed_iup :: "key \<Rightarrow> its_up_t => bool" where
"wellformed_iup k0 iu = (
  let (f,stk) = iu in
  wellformed_its_focus k0 (stk=[]) f &
  wellformed_ts k0 stk &   (* FIXME wf_stk *)
  wellformed_iup_1 iu )"

  
(* step_up ---------------------------------------- *)

(* FIXME isn't this elsewhere? *)
definition split_node :: "node_t => inserting_two_t" where
"split_node n = (
  let (ks,ts) = n in
  let min = min_node_keys in
  let (ks1,k,ks2) = split_at_3 min ks in
  let (ts1,ts2) = split_at (min+1) ts in
  (Node(ks1,ts1),k,Node(ks2,ts2))
)"

(* step focus, given parent frame *)
definition step_focus :: "nf_t => its_focus_t => its_focus_t" where
"step_focus x f = (
  let k = x|>f_k in
  let (ks,rs) = x|>f_t in
  let (_,ts1,ks1,_,ks2,ts2)= nf_to_aux k x in
  let t' = (
    case f|>f_t of
    Inserting_one t => (
      Inserting_one(Node(ks,ts1@[t]@ts2)))
    | Inserting_two (tl_,k,tr) => (
      let ks' = ks1@[k]@ks2 in
      let ts' = ts1@[tl_,tr]@ts2 in
      case (length ks' <= max_node_keys) of
        True => Inserting_one(Node(ks',ts'))
        | False => (Inserting_two(split_node(ks',ts')) ) ) )
  in
  x|>with_t (% _. t'))"

definition step_up :: "its_up_t => its_up_t option" where
"step_up iu = (
  let (f,stk) = iu in
  case stk of 
    Nil => None
    | x#xs => Some(step_focus x f,xs))"



(* step_bottom ---------------------------------------- *)

(* tr: want to split a too-large leaf *)

definition split_leaf_kvs :: "kv_t list => kv_t list * key * kv_t list" where
"split_leaf_kvs kvs = (
  let min = min_leaf_size in
  let (kvs1,kv,kvs2) = split_at_3 min kvs in
  (kvs1,fst kv,kvs2)
)"

definition step_bottom :: "its_down_t => its_up_t option" where
"step_bottom down = (
  let (fts,v0) = down in
  let (f,stk) = fts in
  let k = f|>f_k in
  case f|>f_t of
  Leaf kvs => (
    (*tr:need to check whether the leaf is small enough to insert directly*)
    let kvs2 = lf_ordered_insert kvs k v0 in
    let its = (
      case (length kvs < max_leaf_size) of
      True \<Rightarrow> (Inserting_one(Leaf kvs2))
      | False \<Rightarrow> (
        (*tr:we need to split*)
        let (left,k,right) = split_leaf_kvs kvs2 in
        Inserting_two(Leaf left, k,Leaf right)))
    in
    Some(f|>with_t (% _. its),stk))
  | _ => None (* impossible: find returns leaf *))
"


(* step_its ---------------------------------------- *)

definition step_its :: "its_state_t => its_state_t option" where
"step_its its = (
  case its of
  Its_down (fts,v0) => (
    case (step_fts fts) of 
    None \<Rightarrow> (
      step_bottom (fts,v0) |> map_option (% iu. Its_up(iu)))
    | Some fts => Some(Its_down(fts,v0)))
  | Its_up iu => (
    step_up iu |> map_option (% x. Its_up(x)))) 
"

(* to map ---------------------------------------- *)

(* FIXME use core_to_map *)

end
