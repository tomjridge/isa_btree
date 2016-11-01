theory Tree_stack imports Tree begin

(* search_key_to_index ------------- *)

(* FIXME move *)

(* return the index to the first key k1 st k < k1, or length of list if not found *)
(*tr: assumes xs are sorted *)
(*begin search key to index definition *)
definition search_key_to_index :: "key list => key => nat" where
"search_key_to_index ks k = (
  let num_keys = length ks in
  let i = List.find (% x. key_lt k (ks!x)) (upt 0 num_keys) in
  let i' = (case i of None => num_keys | Some x => x) in
  i')"
(*end search key to index definition *)


(* splitting lists ------------------------------------ *)
 
definition split_list :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list * 'a * 'a list)" where
"split_list rs i = (
  let valid = from_to 0 (length rs -1) in (* valid indexes *)
  let xs = valid |> filter (% n. n < i) in
  let zs = valid |> filter (% n. n > i) in
  (xs|>map (% j. rs!j),
   rs!i,
   zs|>map (% j. rs!j))
)"


(* core type ------------------------------- *)

(* this is the key type *)
record 'a core_t =
  f_k :: key
  f_tss1 :: tss_t
  f_kl :: "key option"
  f_t :: 'a (* tree or node_t *)
  f_ku :: "key option"
  f_tss2 :: tss_t
  

definition dest_core :: "'a core_t \<Rightarrow> key * tss_t * key option * 'a * key option * tss_t" where
"dest_core f = ( f|>f_k,f|>f_tss1,f|>f_kl,f|>f_t,f|>f_ku,f|>f_tss2 )"

definition wf_core :: "key \<Rightarrow> key set \<Rightarrow> 'a core_t \<Rightarrow> bool" where
"wf_core k0 t_keys x = (
  let (k,tss1,kl,_,ku,tss2) = x|>dest_core in
  (k=k0) &
  check_keys_2 (tss1|>tss_to_keys) kl (insert k t_keys) ku (tss2|>tss_to_keys)
)"

(* poly types won't allow field update to different type  f\<lparr>f_t:=(x|>f_t|>f) \<rparr>*)
definition with_t :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a core_t \<Rightarrow> 'b core_t" where
"with_t f x = ( 
  let (k,tss1,kl,t,ku,tss2) = x|>dest_core in
  \<lparr> f_k=k,f_tss1=tss1,f_kl=kl,f_t=(f t), f_ku=ku,f_tss2=tss2 \<rparr>
)"

definition without_t :: "'a core_t \<Rightarrow> unit core_t" where
"without_t x = (x|>with_t (% _. ()))"


(* node_frame ------------------------------ *)

(* assume key k0 is given; then a node_frame is just a node_t: a list of keys and a list of trees *)

type_synonym nf_t = "node_t core_t" 

definition wf_nf :: "key \<Rightarrow> ms_t \<Rightarrow> nf_t \<Rightarrow> bool" where
"wf_nf k0 ms f = (
  let (ks,ts) = f|>f_t in
  wf_core k0 (Node(ks,ts)|>tree_to_keys) f
)"

(* from ks,ts we can derive additional values *) 
type_synonym nf2_t = (* i,ts1,ks1,t,ks2,ts2 *) 
  "
  nat * 
  Tree list *
  key list * 
  Tree *
  key list *
  Tree list" 


definition split_node :: "key \<Rightarrow> nf_t \<Rightarrow> nf2_t" where
"split_node k0 f = (
  let (k,tss1,kl,(ks,ts),ku,tss2) = f|>dest_core in
  let i = search_key_to_index ks k0 in
  let (ts1,t,ts2) = (take i ts, ts!i, drop (i+1) ts) in
  let (ks1,ks2) = (take i ks, drop i ks) in 
  (i,ts1,ks1,t,ks2,ts2)
)"

(* FIXME do we need this? *)
(*
definition split_node_lem :: "bool" where
"split_node_lem = (! f ms k0.
  wf_nf k0 ms f \<longrightarrow> (
  let (k,tss1,kl,(ks,ts),ku,tss2) = f|>dest_core in
  let (i,ts1,ks1,t,ks2,ts2) = split_node k f in
  (ks1@ks2 = ks) &
  (ts1@[t]@ts2 = ts)))
"
*)
 
type_synonym tree_stack_t = "nf_t list"
 

(* descending the tree ----------------------------------------------- *)

(* we put this here because we also use it to relate parent and child, given arbitrary focus *)

definition mk_child :: "nf_t \<Rightarrow> Tree core_t" where
"mk_child p = (
  let (k,tss1,kl,(ks,rs),ku,tss2) = p|>dest_core in
  let (i,ts1,ks1,t,ks2,ts2) = split_node k p in
  let f2 = \<lparr> 
      f_k=k,
      f_tss1=tss1@[ts1],
      f_kl=(if (i=min_child_index) then kl else Some(last ks1)),
      f_t=t,
      f_ku=(if (i=ks_to_max_child_index ks) then ku else Some(hd ks2)),
      f_tss2=[ts2]@tss2 \<rparr>
  in
  f2
)"

definition mk_next_frame :: "nf_t \<Rightarrow> nf_t option" where
"mk_next_frame p = (
  let c = mk_child p in
  case c|>f_t of Leaf(_) \<Rightarrow> None 
  | Node(ks,ts) \<Rightarrow> Some(c|>with_t (% _. (ks,ts))) 
)"

(* parent, child relation ----------------------------------- *)

(* this is just that the child is the result of splitting the parent... except that we want to also 
use it for ascending the tree - ie the focus is irrelevant *)

definition wf_parent_child :: "nf_t \<Rightarrow> 'a core_t \<Rightarrow> bool" where
"wf_parent_child p c = (
  let c' = mk_child p in
  c'|>without_t = c|>without_t 
)"

(* FIXME the following should derive the properties on the child *)
definition wf_parent_child_lem :: "bool" where
"wf_parent_child_lem = (
True
)"



(* wellformed_ts ---------------------------------------- *)


definition ts_to_ms :: "tree_stack_t \<Rightarrow> ms_t" where
"ts_to_ms ts = (case ts of Nil \<Rightarrow> (Some Small_root_node_or_leaf) | _ \<Rightarrow> None)"

lemma ts_to_ms_def_2: "
  (ts_to_ms Nil = (Some Small_root_node_or_leaf)) &
  (! x xs. ts_to_ms (x#xs) = None)"
  apply(simp add:ts_to_ms_def)
  done


fun wellformed_ts :: "key \<Rightarrow> tree_stack_t => bool" where
"wellformed_ts k0 xs = (
  case xs of 
  Nil \<Rightarrow> True
  | c#xs \<Rightarrow> (
    wf_nf k0 (ts_to_ms xs) c & 
    wellformed_ts k0 xs &
    (case xs of Nil \<Rightarrow> True | p#xs \<Rightarrow> mk_next_frame p = Some c))
)"

lemma wellformed_ts_def_2: "
  (wellformed_ts k0 Nil = True) &
  (wellformed_ts k0 (c#xs) = (
    wf_nf k0 (ts_to_ms xs) c & 
    wellformed_ts k0 xs &
    (case xs of Nil \<Rightarrow> True | p#xs \<Rightarrow> mk_next_frame p = Some c)))"
by simp

declare wellformed_ts.simps[simp del]


end
