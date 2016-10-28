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


(* types ------------------------------ *)

type_synonym  leaves_t = "leaf_lbl_t list" 

record core_t = 
  cc_k :: key
  cc_xs :: leaves_t
  cc_l :: "key option"
  cc_t :: Tree
  cc_u :: "key option"
  cc_zs :: leaves_t
  
type_synonym dest_core_t = "key * leaves_t * key option * Tree * key option * leaves_t"

definition dest_core :: "core_t \<Rightarrow> dest_core_t" where
"dest_core c = (c|>cc_k,c|>cc_xs,c|>cc_l,c|>cc_t,c|>cc_u,c|>cc_zs)"

definition mk_core :: "dest_core_t \<Rightarrow> core_t" where
"mk_core x = (let (k,xs,l,t,u,zs) = x in (| cc_k=k,cc_xs=xs,cc_l=l,cc_t=t,cc_u=u,cc_zs=zs |))"
  
lemma [simp]: "dest_core (mk_core x) = x"
 apply(case_tac x)
 apply(simp add: dest_core_def mk_core_def rev_apply_def)
 done

 lemma [simp] : "(mk_core x) |> dest_core = x"
  apply(simp add: rev_apply_def)
  done

(* cnode comes from a focus, where we know the focus is not a leaf, and we have an index into the leaves *)
record ksrsi_t = 
  cc_ks :: "key list" (* invariant: cc_t is Node(ks,rs) *)
  cc_rs :: "Tree list"
  cc_i :: nat

definition dest_ksrsi :: "ksrsi_t \<Rightarrow> key list * Tree list * nat" where
"dest_ksrsi c = (c|>cc_ks,c|>cc_rs,c|>cc_i)"

lemma [simp]: "dest_ksrsi \<lparr>cc_ks=ks,cc_rs=rs,cc_i=i\<rparr> = (ks,rs,i)"
 apply(simp add: dest_ksrsi_def rev_apply_def)
 done

 lemma [simp]: "\<lparr>cc_ks=ks,cc_rs=rs,cc_i=i\<rparr> |> dest_ksrsi = (ks,rs,i)"
  apply(simp add: rev_apply_def)
  done
 
 
type_synonym cnode_t = "(core_t * ksrsi_t)"
  
type_synonym tree_stack_t = "cnode_t list"
 
(* wellformed_core ------------------------------------------ *)

definition wellformed_core :: "key \<Rightarrow> ms_t \<Rightarrow> core_t => bool" where
"wellformed_core k0 ms f = (
  let (k,xs,l,t,u,zs) = f|>dest_core in
  let b1 = wellformed_tree ms t in
  let b2 = check_keys_2 (xs|>leaves_to_map|>dom) l (set (k#(keys t))) u (zs|>leaves_to_map|>dom) in
  b1&b2&(k=k0))"


(* wellformed_cnode ---------------------------------------- *)


(* FIXME adjust scala defns *)      
definition wellformed_cnode :: "key \<Rightarrow> ms_t => cnode_t => bool " where
"wellformed_cnode k0 ms c = (
  let (c1,c2) = c in
  let (k,xs,l,t,u,zs) = c1|>dest_core in
  let (ks,rs,i) = c2|>dest_ksrsi in
  let b1 = wellformed_core k0 ms c1 in 
  let b2 = search_key_to_index ks k0 = i in
  let b4 = (t = Node(ks,rs)) in
  b1&b2&b4)
"
   
  


(* bound from cnode ---------------------------------------- *)

(* make sure we use the existing bound in case i is extremal *)
definition cnode_to_bound :: "cnode_t \<Rightarrow> bound_t" where
"cnode_to_bound c = (
  let (c1,c2) = c in
  index_to_bound (c2|>cc_ks) (c2|>cc_i) |> 
  with_parent_bound (c1|>cc_l,c1|>cc_u))"




(* wellformed_context, ts ---------------------------------------- *)


definition ts_to_ms :: "tree_stack_t \<Rightarrow> ms_t" where
"ts_to_ms ts = (case ts of Nil \<Rightarrow> (Some Small_root_node_or_leaf) | _ \<Rightarrow> None)"

lemma ts_to_ms_def_2: "
  (ts_to_ms Nil = (Some Small_root_node_or_leaf)) &
  (! x xs. ts_to_ms (x#xs) = None)"
  apply(simp add:ts_to_ms_def)
  done


fun wellformed_ts :: "key \<Rightarrow> tree_stack_t => bool" where
"wellformed_ts k0 xs = (
  case xs of Nil \<Rightarrow> True
  | cn#cns \<Rightarrow> (wellformed_cnode k0 (ts_to_ms cns) cn & wellformed_ts k0 cns))"
(*end wfcontext definition*)

lemma wellformed_ts_def_2: "
  (wellformed_ts k0 Nil = True) &
  (wellformed_ts k0 (cn#cns) = (wellformed_cnode k0 (ts_to_ms cns) cn & wellformed_ts k0 cns))"
by simp

declare wellformed_ts.simps[simp del]



(* stack reassembly ----------------------------------- *)

fun reass :: "Tree \<Rightarrow> tree_stack_t \<Rightarrow> Tree" where
"reass t ts = (
  case ts of
  Nil \<Rightarrow> t
  | cn#cns \<Rightarrow> (
    let (c1,c2) = cn in
    let t2 = Node(c2|>cc_ks,(c2|>cc_rs)[(c2|>cc_i):=t]) in
    reass t2 cns)
)"


(* lemmas ------------------------------------------------ *)

(* FIXME needed? *)
definition reass_tree_to_leaves_b :: bool where
"reass_tree_to_leaves_b = (! ts t.
  ? xs zs. (reass t ts) |> tree_to_leaves = xs@(tree_to_leaves t)@zs)"



end
