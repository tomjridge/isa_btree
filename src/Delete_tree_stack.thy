theory Delete_tree_stack imports Find_tree_stack begin

datatype dir_t = Right | Left

datatype dts_t = 
  D_small_leaf "leaf_lbl_t"
  | D_small_node "node_t"
  | D_updated_subtree "Tree"

type_synonym dts_focus_t = "dts_t core_t"
  
datatype dts_state_t = 
  Dts_down "fts_state_t"
  | Dts_up "dts_focus_t * tree_stack_t"
  | Dts_finished "Tree"
  
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


(* steal ----------------------------------------------- *)

definition node_steal_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_steal_right k0 p stk c1 = (
  let f = % x :: nat. failwith (''node_steal_right'',x) in
  let (c1_ks,c1_ts) = c1 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2 = (case q_c of Node(ks,ts) \<Rightarrow> (ks,ts) | _ \<Rightarrow> f 5) in
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
  let f = % x :: nat. failwith (''node_steal_left'',x) in
  let (c2_ks,c2_ts) = c2 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1 = (case q_c of Node(ks,ts) \<Rightarrow> (ks,ts) | _ \<Rightarrow> f 5) in
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
  let f = % x :: nat. failwith (''leaf_steal_right'',x) in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2_kvs = (case q_c of Leaf(kvs) \<Rightarrow> kvs | _ \<Rightarrow> f 5) in
  let (c2_kv',c2_kvs') = dest_list c2_kvs in
  let c1' = Leaf(c1_kvs @ [c2_kv']) in
  let c2' = Leaf(c2_kvs') in
  let k' = List.hd c2_kvs'|>fst in
  let f' = D_updated_subtree(Node(q_ks1 @ [k'] @ q_ks2',q_ts1 @ [c1',c2'] @ q_ts2')) in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_steal_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_steal_left k0 p stk c2_kvs = (
  let f = % x :: nat. failwith (''leaf_steal_left'',x) in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1_kvs = (case q_c of Leaf(kvs) \<Rightarrow> kvs | _ \<Rightarrow> f 5) in
  let (c1_kvs',c1_kv') = dest_list' c1_kvs in
  let c2' = Leaf([c1_kv']@c2_kvs) in
  let c1' = Leaf(c1_kvs') in
  let k' = fst c1_kv' in
  let f' = D_updated_subtree(Node(q_ks1' @ [k'] @ q_ks2,q_ts1' @ [c1',c2'] @ q_ts2)) in
  (p|>with_t (% _. f'),stk)
)"


(* merging ----------------------------------------------------------- *)

definition node_merge_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_merge_right k0 p stk c1 = (
  let f = % x :: nat. failwith (''node_merge_right'',x) in
  let (c1_ks,c1_ts) = c1 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2 = (case q_c of Node(ks,ts) \<Rightarrow> (ks,ts) | _ \<Rightarrow> f 5) in
  let (c2_ks,c2_ts) = c2 in
  let c1' = Node(c1_ks @ [q_k] @ c2_ks,c1_ts @ c2_ts) in
  let f' = D_updated_subtree(Node(q_ks1 @ q_ks2', q_ts1 @ [c1'] @ q_ts2')) in
  (p|>with_t (% _. f'),stk)
)"

definition node_merge_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> node_t \<Rightarrow> dts_up_t" where
"node_merge_left k0 p stk c2 = (
  let f = % x :: nat. failwith (''node_merge_left'',x) in
  let (c2_ks,c2_ts) = c2 in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1 = (case q_c of Node(ks,ts) \<Rightarrow> (ks,ts) | _ \<Rightarrow> f 5) in
  let (c1_ks,c1_ts) = c1 in
  let c1' = Node(c1_ks @ [q_k] @c2_ks, c1_ts @ c2_ts) in
  let f' = D_updated_subtree(Node(q_ks1' @ q_ks2, q_ts1' @ [c1'] @ q_ts2)) in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_merge_right :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_merge_right k0 p stk c1_kvs = (
  let f = % x :: nat. failwith (''leaf_merge_right'',x) in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_k,q_ks2') = dest_list q_ks2 in
  let (q_c,q_ts2') = dest_list q_ts2 in
  let c2_kvs = (case q_c of Leaf(kvs) \<Rightarrow> kvs | _ \<Rightarrow> f 5) in
  let c1' = Leaf(c1_kvs @ c2_kvs) in
  let f' = D_updated_subtree(Node(q_ks1 @ q_ks2',q_ts1 @ [c1'] @ q_ts2')) in
  (p|>with_t (% _. f'),stk)
)"

definition leaf_merge_left :: "key \<Rightarrow> nf_t \<Rightarrow> tree_stack_t \<Rightarrow> kvs_t \<Rightarrow> dts_up_t" where
"leaf_merge_left k0 p stk c2_kvs = (
  let f = % x :: nat. failwith (''leaf_merge_left'',x) in
  let q = p |> nf_to_aux k0 in
  let (q_i,q_ts1,q_ks1,q_t,q_ks2,q_ts2) = q in
  let (q_ks1',q_k) = dest_list' q_ks1 in
  let (q_ts1',q_c) = dest_list' q_ts1 in
  let c1_kvs = (case q_c of Leaf(kvs) \<Rightarrow> kvs | _ \<Rightarrow> f 5) in
  let c1' = Leaf(c1_kvs @ c2_kvs) in
  let f' = D_updated_subtree(Node(q_ks1' @ q_ks2, q_ts1' @ [c1'] @ q_ts2)) in
  (p|>with_t (% _. f'),stk)
)"

(* can_steal_or_merge ---------------------------------- *)

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

definition step_up :: "key \<Rightarrow> dts_up_t \<Rightarrow> dts_state_t" where
"step_up k0 du = (
  let (f,stk) = du in
  case stk of 
  Nil \<Rightarrow> (
    case f|>f_t of
    D_small_leaf(kvs) \<Rightarrow> Dts_finished(Leaf(kvs))
    | D_small_node(ks,ts) \<Rightarrow> Dts_finished(Node(ks,ts))
    | D_updated_subtree(t) \<Rightarrow> Dts_finished(t))
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
    | D_updated_subtree(t) \<Rightarrow> (
      let q = p |> nf_to_aux k0 in
      let (i,ts1,ks1,t,ks2,ts2) = q in
      Dts_up(p|> with_t (% _. D_updated_subtree(Node(ks1@ks2,ts1@[t]@ts2))),stk')
    )
  )
)"

end