theory Delete_tree_stack imports Find_tree_stack begin

datatype dir_t = Right | Left

(* 
D_small_leaf: A small leaf arises when a minimal leaf has an key removed.

D_small_node: If a small leaf is merged with a sibling, then the parent node may become small.

D_updated_subtree: The usual case, where the subtree has been updated, but the width of the 
parent is unchanged.

*)

datatype dts_t = 
  D_small_leaf "leaf_lbl_t"
  | D_small_node "node_t"
  | D_updated_subtree "Tree"

type_synonym dts_focus_t = "dts_t core_t"
  
datatype dts_state_t = 
  Dts_down "fts_state_t"
  | Dts_up "dts_focus_t * tree_stack_t"
  | Dts_finished "Tree"  (* FIXME remove this - complicates cases *)
  
type_synonym dts_down_t = fts_state_t
type_synonym dts_up_t = "dts_focus_t * tree_stack_t"

(* parent ks1 k ks2, ts1 ts2; and two children separated by k, and the direction to steal *)
type_synonym node_steal_t = "key list * key * key list * 
  Tree list * Tree list  * 
  node_t * node_t * dir_t"
  
definition dest_list :: "'a list \<Rightarrow> ('a * 'a list)" where
"dest_list xs = (case xs of x#xs \<Rightarrow> (x,xs) | _ \<Rightarrow> failwith ''dest_list'')"

definition dest_list' :: "'a list \<Rightarrow> ('a list * 'a)" where
"dest_list' xs = (case xs of [] \<Rightarrow> failwith ''dest_list' '' | _ \<Rightarrow> (butlast xs,last xs))"

definition dts_to_tree :: "dts_t \<Rightarrow> Tree" where
"dts_to_tree dts = (
  case dts of
  D_small_leaf kvs \<Rightarrow> Leaf(kvs)
  | D_small_node(ks,ts) \<Rightarrow> Node(ks,ts)
  | D_updated_subtree(t) \<Rightarrow> t
)"

definition dts_to_ms :: "bool \<Rightarrow> dts_t \<Rightarrow> ms_t" where
"dts_to_ms stack_empty dts = (
  case stack_empty of
    True \<Rightarrow> Some(Small_root_node_or_leaf)
  | False \<Rightarrow> (
    case dts of
    D_small_leaf kvs \<Rightarrow> Some Small_leaf
    | D_small_node(ks,ts) \<Rightarrow> Some Small_node
    | D_updated_subtree(t) \<Rightarrow> None)
)"

definition mk_dts_state :: "key \<Rightarrow> Tree \<Rightarrow> dts_state_t" where
"mk_dts_state k0 t = (Dts_down(mk_fts_state k0 t))"


(* wellformedness ----------------------------------------- *) 

definition wellformed_dts :: "bool \<Rightarrow> dts_t \<Rightarrow> bool" where
"wellformed_dts stack_empty dts = assert_true dts (
  let t = dts |> dts_to_tree in
  let ms = dts |> dts_to_ms stack_empty in 
  wellformed_tree ms t
)"

definition wellformed_dts_focus :: "bool \<Rightarrow> dts_focus_t \<Rightarrow> bool" where
"wellformed_dts_focus stack_empty f = assert_true (stack_empty,f) (
  let dts = f|>f_t in
  wf_core (dts|>dts_to_tree|>tree_to_keys) f &
  wellformed_dts stack_empty dts
)"

definition wellformed_dup_1 :: "dts_up_t \<Rightarrow> bool" where
"wellformed_dup_1 dup = assert_true dup (
  let (f,stk) = dup in
  case stk of 
  Nil \<Rightarrow> True
  | p#xs \<Rightarrow> (
    (f|>without_t = (mk_child p |> without_t)) &
    (f|>f_t|>dts_to_tree|>height = (p|>mk_child|>f_t|>height))
  )
)"

definition wellformed_dup :: "dts_up_t \<Rightarrow> bool" where
"wellformed_dup dup = assert_true dup (
  let (f,stk) = dup in
  wellformed_dts_focus (stk=[]) f &
  wellformed_ts stk &
  wellformed_dup_1 dup
)"


definition wellformed_dts_state :: "dts_state_t \<Rightarrow> bool" where
"wellformed_dts_state s = assert_true s (
  case s of
  Dts_down(fts) \<Rightarrow> (wellformed_fts fts)
  | Dts_up(f,stk) \<Rightarrow> (wellformed_dup (f,stk))
  | Dts_finished(t) \<Rightarrow> (wellformed_tree (Some Small_root_node_or_leaf) t)
)"



(* steal ----------------------------------------------- *)

definition node_steal_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_steal_right k0 p stk c1 = (
  let (c1_ks,c1_ts) = c1 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2 = dest_Node q_c in
  let (c2_ks,c2_ts) = c2 in
  let (c2_k',c2_ks') = dest_list c2_ks in
  let (c2_t',c2_ts') = dest_list c2_ts in
  let c1' = Node(c1_ks @ [q_k],c1_ts @ [c2_t']) in
  let k' = c2_k' in
  let c2' = Node(c2_ks',c2_ts') in
  let f' = D_updated_subtree(Node(q_ks1 @ [k'] @ q_ks2',q_ts1 @ [c1',c2'] @ q_ts2')) in
  (p|>with_t (% _. f'),stk)
)"
 
definition node_steal_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_steal_left k0 p stk c2 = (
  let (c2_ks,c2_ts) = c2 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1 = dest_Node q_c in
  let (c1_ks,c1_ts) = c1 in
  let c2' = Node([q_k] @ c2_ks,[q_c] @ c2_ts) in
  let (c1_ks',c1_k') = dest_list' c1_ks in
  let (c1_ts',c1_t') = dest_list' c1_ts in
  let k' = c1_k' in
  let c1' = Node(c1_ks',c1_ts') in
  let f' = D_updated_subtree(Node(q_ks1' @ [k'] @ q_ks2,q_ts1' @ [c1',c2'] @ q_ts2)) in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_steal_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_steal_right k0 p stk c1_kvs = (
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2_kvs = dest_Leaf q_c in
  let (c2_kv',c2_kvs') = dest_list c2_kvs in
  let c1' = Leaf(c1_kvs @ [c2_kv']) in
  let c2' = Leaf(c2_kvs') in
  let k' = List.hd c2_kvs'|>fst in
  let f' = D_updated_subtree(Node(q_ks1 @ [k'] @ q_ks2',q_ts1 @ [c1',c2'] @ q_ts2')) in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_steal_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_steal_left k0 p stk c2_kvs = (
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1_kvs = dest_Leaf q_c in
  let (c1_kvs',c1_kv') = dest_list' c1_kvs in
  let c2' = Leaf([c1_kv']@c2_kvs) in
  let c1' = Leaf(c1_kvs') in
  let k' = fst c1_kv' in
  let f' = D_updated_subtree(Node(q_ks1' @ [k'] @ q_ks2,q_ts1' @ [c1',c2'] @ q_ts2)) in
  (p|>with_t (% _. f'),stk)
)"


(* merging ----------------------------------------------------------- *)

definition take_care :: "key list \<Rightarrow> Tree list \<Rightarrow> Tree \<Rightarrow> dts_t" where
"take_care ks' ts' c1' = (
    (* we have to be careful here about a root node with 1 key *)
    if (ks' = []) then D_updated_subtree(c1') else
    if (List.length ks' < Constants.min_node_keys) then D_small_node(ks',ts') else 
    D_updated_subtree(Node(ks',ts'))
)"

definition node_merge_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_merge_right k0 p stk c1 = (
  let (c1_ks,c1_ts) = c1 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2 = dest_Node q_c in
  let (c2_ks,c2_ts) = c2 in
  let c1' = Node(c1_ks @ [q_k] @ c2_ks,c1_ts @ c2_ts) in
  let ks' = q_ks1 @ q_ks2' in
  let ts' = q_ts1 @ [c1'] @ q_ts2' in
  let f' = take_care ks' ts' c1' in
  (p|>with_t (% _. f'),stk)
)"

definition node_merge_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_merge_left k0 p stk c2 = (
  let (c2_ks,c2_ts) = c2 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1 = dest_Node q_c in
  let (c1_ks,c1_ts) = c1 in
  let c1' = Node(c1_ks @ [q_k] @c2_ks, c1_ts @ c2_ts) in
  let ks' = q_ks1' @ q_ks2 in
  let ts' = q_ts1' @ [c1'] @ q_ts2 in
  let f' = take_care ks' ts' c1' in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_merge_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_merge_right k0 p stk c1_kvs = (
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2_kvs = dest_Leaf q_c in
  let c1' = Leaf(c1_kvs @ c2_kvs) in
  let ks' = q_ks1 @ q_ks2' in
  let ts' = q_ts1 @ [c1'] @ q_ts2' in
  let f' = take_care ks' ts' c1' in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_merge_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_merge_left k0 p stk c2_kvs = (
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1_kvs = dest_Leaf q_c in
  let c1' = Leaf(c1_kvs @ c2_kvs) in
  let ks' = q_ks1' @ q_ks2 in
  let ts' = q_ts1' @ [c1'] @ q_ts2 in
  let f' = take_care ks' ts' c1' in
  (p|>with_t (% _. f'),stk)
)"


(* can_steal_or_merge ---------------------------------- *)

(* FIXME change these to return bool rathe rthan tree option *)

definition steal_b :: "Tree \<Rightarrow> bool" where
"steal_b t = (
  case t of
  Leaf(kvs) \<Rightarrow> (List.length kvs > Constants.min_leaf_size)
  | Node(ks,ts) \<Rightarrow> (List.length ks > Constants.min_node_keys)
)"

definition can :: "key \<Rightarrow> (Tree \<Rightarrow> bool) \<Rightarrow> dir_t \<Rightarrow> nf_t \<Rightarrow> Tree option" where
"can k0 steal_or_merge dir p = (
  let q = p |> nf_to_aux k0 in
  let (i,ts1,ks1,t,ks2,ts2) = q in
  case dir of
  Right \<Rightarrow> (
    case ts2 of 
    Nil \<Rightarrow> None
    | t#ts \<Rightarrow> (if steal_or_merge t then Some(t) else None)
  )
  | Left \<Rightarrow> (
    case ts1 of 
    Nil \<Rightarrow> None
    | _ \<Rightarrow> (
      let (ts,t) = dest_list' ts1 in
      if steal_or_merge t then Some(t) else None)
  )
)"

definition can_steal_right :: "key \<Rightarrow> nf_t \<Rightarrow> Tree option" where
"can_steal_right k0 p = (can k0 steal_b Right p)"
  
definition can_steal_left :: "key \<Rightarrow> nf_t \<Rightarrow> Tree option" where
"can_steal_left k0 p = (can k0 steal_b Left p)"

definition merge_b :: "Tree \<Rightarrow> bool" where
"merge_b t = (
  case t of
  Leaf(kvs) \<Rightarrow> (List.length kvs + Constants.min_leaf_size \<le> Constants.max_leaf_size +1) (* assume merging into something of size min_leaf_size  - 1 *)
  | Node(ks,ts) \<Rightarrow> (List.length ks + Constants.min_node_keys \<le> Constants.max_node_keys +1)
)"

definition can_merge_right :: "key \<Rightarrow> nf_t \<Rightarrow> Tree option" where
"can_merge_right k0 p = (can k0 merge_b Right p)"

definition can_merge_left :: "key \<Rightarrow> nf_t \<Rightarrow> Tree option" where
"can_merge_left k0 p = (can k0 merge_b Left p)"


(* main routine ------------------------------------ *)

definition step_up :: "dts_up_t \<Rightarrow> dts_state_t" where
"step_up du = (
  let (f,stk) = du in
  let k0 = f|>f_k in
  case stk of 
  Nil \<Rightarrow> (
    let dts = f|>f_t in
    (* FIXME root may have lost all its keys? should we take care here or before? if here, we break invariant, so take care before *)    
    Dts_finished(dts|>dts_to_tree))
  | p#stk' \<Rightarrow> (
    case f|>f_t of
    D_small_leaf(kvs) \<Rightarrow> (
      case can_steal_right k0 p of
      Some(_) \<Rightarrow> Dts_up(leaf_steal_right k0 p stk' kvs)
      | _ \<Rightarrow> (
        case can_steal_left k0 p of
        Some(_) \<Rightarrow> Dts_up(leaf_steal_left k0 p stk' kvs)
        | _ \<Rightarrow> (
          case can_merge_right k0 p of
          Some(_) \<Rightarrow> Dts_up(leaf_merge_right k0 p stk' kvs)
          | _ \<Rightarrow> (
            case can_merge_left k0 p of
            Some(_) \<Rightarrow> Dts_up(leaf_merge_left k0 p stk' kvs)
            | _ \<Rightarrow> (failwith ''step_up: impossible, leaf has no siblings but stack not nil'')
          )
        )
      )
    )
    | D_small_node(ks,ts) \<Rightarrow> (  
      case can_steal_right k0 p of
      Some(_) \<Rightarrow> Dts_up(node_steal_right k0 p stk' (ks,ts))
      | _ \<Rightarrow> (
        case can_steal_left k0 p of
        Some(_) \<Rightarrow> Dts_up(node_steal_left k0 p stk' (ks,ts))
        | _ \<Rightarrow> (
          case can_merge_right k0 p of
          Some(_) \<Rightarrow> Dts_up(node_merge_right k0 p stk' (ks,ts))
          | _ \<Rightarrow> (
            case can_merge_left k0 p of
            Some(_) \<Rightarrow> Dts_up(node_merge_left k0 p stk' (ks,ts))
            | _ \<Rightarrow> (failwith ''step_up: impossible, node has no siblings but stack not nil'')
          )
        )
      )
    )
    | D_updated_subtree(t') \<Rightarrow> (
      let q = p |> nf_to_aux k0 in
      let (i,ts1,ks1,t,ks2,ts2) = q in
      Dts_up(p|> with_t (% _. D_updated_subtree(Node(ks1@ks2,ts1@[t']@ts2))),stk')
    )
  )
)"

(* NB we try to keep the executable parts self-contained (no passing -in k v); for wf, we pass in
k v *)
definition step_dts :: "dts_state_t \<Rightarrow> dts_state_t option" where
"step_dts dts = (
  case dts of
  Dts_down(fts) \<Rightarrow> (
    case Find_tree_stack.step_fts fts of
    None \<Rightarrow> (
      let (f,stk) = fts|>dest_fts_state in
      let (k,tss1,kl,t,ku,tss2) = f|>dest_core in
      let kvs = t|>dest_Leaf in
      case k : set (kvs|>List.map fst) of
      True \<Rightarrow> (
        (* something to delete *)
        let kvs' = kvs|>List.filter (% x. ~ (key_eq (fst x) k)) in
        case (List.length kvs' < Constants.min_leaf_size) of
        True \<Rightarrow> Some(Dts_up(f|>with_t(% _. D_small_leaf(kvs')),stk))
        | False \<Rightarrow> Some(Dts_up(f|>with_t(% _. D_updated_subtree(Leaf(kvs'))),stk)))
      | False \<Rightarrow> (
        (* nothing to delete *)
        case stk of
        Nil \<Rightarrow> Some(Dts_finished(Leaf(kvs)))
        | _ \<Rightarrow> Some(Dts_finished(Node(stk|>List.last|>f_t)))
      )
    )
    | Some(fts') \<Rightarrow> Some(Dts_down(fts'))
  )
  | Dts_up(f,stk) \<Rightarrow> (Some(step_up (f,stk)))
  | Dts_finished(_) \<Rightarrow> None (* exit *)
)"

definition dest_dts_state :: "dts_state_t \<Rightarrow> Tree option" where
"dest_dts_state s = (
  case s of
  Dts_finished(t) \<Rightarrow> Some(t)
  | _ \<Rightarrow> None
)" 

(* testing ------------------------------------------------------------ *)

definition dts_to_leaves :: "dts_t \<Rightarrow> leaves_t" where
"dts_to_leaves dts = (dts|>dts_to_tree|>tree_to_leaves)"

definition focus_to_leaves :: "dts_focus_t \<Rightarrow> leaves_t" where
"focus_to_leaves f = (
  let (k,tss1,l,dts,u,tss2) = f|>dest_core in
  (tss1@[[dts|>dts_to_tree]]@tss2)|>tss_to_leaves
)"

definition wf_dts_trans :: "dts_state_t \<Rightarrow> dts_state_t \<Rightarrow> bool" where
"wf_dts_trans s1 s2 = assert_true (s1,s2) (
  case (s1,s2) of 
  (Dts_down(fts),Dts_down(fts')) \<Rightarrow> (wf_fts_trans fts fts')
  | (Dts_down(_),Dts_up(_)) \<Rightarrow> True
  | (Dts_down(_),Dts_finished(t)) \<Rightarrow> True
  | (Dts_up(du),Dts_up(du')) \<Rightarrow> (
    (* no reason to expect that the leaves are preserved exactly *)
    focus_to_leaves (fst du')|>List.concat = focus_to_leaves (fst du)|>List.concat)
  | (Dts_up(du),Dts_finished(t)) \<Rightarrow> (focus_to_leaves (fst du) = tree_to_leaves t)
)"


end