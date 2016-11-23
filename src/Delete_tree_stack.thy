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



(* take care ----------------------------------------------------------- *)

(* FIXME where should this appear now? *)
definition take_care :: "key list \<Rightarrow> Tree list \<Rightarrow> Tree \<Rightarrow> dts_t" where
"take_care ks' ts' c1' = (
    (* we have to be careful here about a root node with 1 key *)
    if (ks' = []) then D_updated_subtree(c1') else
    if (List.length ks' < Constants.min_node_keys) then D_small_node(ks',ts') else 
    D_updated_subtree(Node(ks',ts'))
)"


(* alternative defs -------------------------------------- *)

type_synonym 'a frac_t = "ks * 'a list"

definition frac_mult :: "'a frac_t \<Rightarrow> 'a frac_t \<Rightarrow> 'a frac_t"  where
"frac_mult xs ys = (
let (a,b) = xs in
let (a',b') = ys in
(a@a',b@b')
)"

(* 'a - the tree type; 'v - the values in the children; 't - the values in the parent
'c - child type = ks * 'v list
'p - parent type = ks * 't list
*)

type_synonym right_t = bool
type_synonym is_leaf_t = bool

datatype 'a d12_t = D1 "'a" | D2 "'a * key * 'a"

(* FIXME what about take_care? *)

(* this defn rather horrible; apologies; it is needed to avoid duplication at the block level *)
definition steal_or_merge :: 
  "right_t \<Rightarrow>
  is_leaf_t \<Rightarrow> 
  ((ks * 'v list) \<Rightarrow> 'c) \<Rightarrow> 
  (ks * 'v list) \<Rightarrow> key \<Rightarrow> (ks * 'v list) \<Rightarrow> 'c d12_t" where
"steal_or_merge right is_leaf mk_c c p_k s = ( (* child sibling *)
  let m = frac_mult in
  (* sibling *)
  let (s_ks,s_ts) = s in
  let ((s_k,s_t),s_1) = (
    case right of
    True \<Rightarrow> (let ((k,ks),(t,ts)) = (dest_list s_ks,dest_list s_ts) in ((k,t),(ks,ts)))
    | False \<Rightarrow> (let ((ks,k),(ts,t)) = (dest_list' s_ks,dest_list' s_ts) in ((k,t),(ks,ts))))
  in
  case (1+List.length(fst s_1) > (if is_leaf then min_leaf_size else min_node_keys)) of
  True \<Rightarrow> (
    (* steal *)
    let c' =
      (* slightly different for leaf *)
      let k = (if is_leaf then s_k else p_k) in
      mk_c (if right then m c ([k],[s_t]) else m ([k],[s_t]) c) 
    in 
    let s' = mk_c s_1 in
    (if right then D2(c',p_k,s') else D2(s', p_k, c'))
  )
  | False \<Rightarrow> (
    (* merge *)
    let c' = mk_c (if right then m (m c ([p_k],[])) s  else m s (m ([p_k],[]) c)) in
    D1 c'
  )
)"  


(* main routine ------------------------------------ *)

(* FIXME may want to use this type eg in core *)
type_synonym ks_ts_t = "key list * Tree list"

type_synonym split_p_t = "ks_ts_t * ks_ts_t"

definition get_sibling :: "split_p_t \<Rightarrow> right_t * split_p_t * Tree * key" where
"get_sibling p = (
  let (p_1,p_2) = p in
        case p_2 of
        (p_k#p_ks2,s#p_ts2) \<Rightarrow> (
        let right = True in
        let (p1,p_2) = (p_1,(p_ks2,p_ts2)) in
        (right,(p_1,p_2),s,p_k))
        | _ \<Rightarrow> (
          case p_1 of
          (_#_,_#_) \<Rightarrow> (
            let right = False in
            let (p_ks1,p_ts1) = p_1 in
            let (p_1_ks,p_k) = dest_list' p_ks1 in
            let (p_1_ts,s) = dest_list' p_ts1 in
            let (p_1,p2) = ((p_1_ks,p_1_ts),p_2) in
            (right,(p_1,p_2),s,p_k))
          | _ \<Rightarrow> impossible ()
        ))
"


definition unzip :: "('a*'b) list \<Rightarrow> ('a list * 'b list)" where
"unzip xs = (xs|>List.map fst, xs|>List.map snd)"

(* FIXME rename nf_t to stk_nf *)
definition post_steal_or_merge :: "tree_stack_t \<Rightarrow> nf_t \<Rightarrow> ks_ts_t \<Rightarrow> ks_ts_t \<Rightarrow> Tree d12_t => dts_state_t" where
"post_steal_or_merge stk' p p_1 p_2 x = (
      let m = frac_mult in
      (* FIXME following code is duplicated below *)
      case x of 
      D1 c' \<Rightarrow> (
        let p' = Node(m (m p_1 ([],[c'])) p_2) in
        let f' = (
          case (p'|>dest_Node|>fst|>List.length < min_node_keys) of
          False \<Rightarrow> (p|>with_t (% _. D_updated_subtree(p')))
          | True \<Rightarrow> (p|>with_t (% _. D_small_node(p'|>dest_Node))))
        in 
        Dts_up(f',stk'))
      | D2(c1,k,c2) \<Rightarrow> (
        let f' = p|>with_t (% _. D_updated_subtree(Node(m (m p_1 ([k],[c1,c2])) p_2))) in
        Dts_up(f',stk'))       
)"

definition step_up :: "dts_up_t \<Rightarrow> dts_state_t" where
"step_up du = (
  let (f,stk) = du in
  let k0 = f|>f_k in
  case stk of 
  [] \<Rightarrow> (
    (* FIXME root may have lost all its keys? should we take care here or before? if here, we break invariant, so take care before *)    
    Dts_finished(f|>f_t|>dts_to_tree))
  | p#stk' \<Rightarrow> (
    case f|>f_t of
    D_updated_subtree(t') \<Rightarrow> (
      let q = p |> nf_to_aux k0 in
      let (i,ts1,ks1,t,ks2,ts2) = q in
      Dts_up(p|> with_t (% _. D_updated_subtree(Node(ks1@ks2,ts1@[t']@ts2))),stk')
    )
    | D_small_leaf (kvs) \<Rightarrow> (
      let leaf = True in
      (* FIXME the small cases can be handled uniformly; want steal left,right to be uniform, and take a child as arg; also return option *)  
      (* parent info is already read, but we must read the siblings from disk *)
      let q = p |> nf_to_aux k0 in
      let (i,p_ts1,p_ks1,_,p_ks2,p_ts2) = q in
      let mk_c = (% ks_vs. let (ks,vs) = ks_vs in Leaf(List.zip ks vs)) in 
      let (right,(p_1,p_2),s,p_k) = get_sibling ((p_ks1,p_ts1),(p_ks2,p_ts2)) in
      let x = steal_or_merge right leaf mk_c (kvs|>unzip) p_k (s|>dest_Leaf|>unzip) in
      post_steal_or_merge stk' p p_1 p_2 x
    )
    | D_small_node (ks,ts) \<Rightarrow> (
      let leaf = True in
      (* FIXME the small cases can be handled uniformly; want steal left,right to be uniform, and take a child as arg; also return option *)  
      (* parent info is already read, but we must read the siblings from disk *)
      let q = p |> nf_to_aux k0 in
      let (i,p_ts1,p_ks1,_,p_ks2,p_ts2) = q in
      let mk_c = (% ks_ts. Node(ks,ts)) in 
      let (right,(p_1,p_2),s,p_k) = get_sibling ((p_ks1,p_ts1),(p_ks2,p_ts2)) in
      let x = steal_or_merge right (~ leaf) mk_c (ks,ts) p_k (s|>dest_Node) in
      post_steal_or_merge stk' p p_1 p_2 x
    )
  )
)"
        
 
(* NB we try to keep the executable parts self-contained (no passing-in k v) *)
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

(* FIXME rename dest_dts_finished *)
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