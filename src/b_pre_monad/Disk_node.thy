theory Disk_node  
imports A_start_here
begin

(* blocks on disk correspond to nodes, which are like tree nodes, but
with pointers rather than children *)

(* type variable naming conventions:

'k - keys
'v - values
'r - references to disk blocks

*)

datatype ('node,'leaf) dnode = 
  Disk_node "'node" 
  | Disk_leaf "'leaf"

definition dest_Disk_node :: "('node,'leaf) dnode \<Rightarrow> 'node" where
"dest_Disk_node f = (case f of Disk_node x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_node''))"

definition dest_Disk_leaf :: "('node,'leaf) dnode \<Rightarrow> 'leaf" where
"dest_Disk_leaf f = (case f of Disk_leaf x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_leaf''))"

(* FIXME probably want to abstract even further *)
datatype_record ('k,'v,'leaf) leaf_ops = 
  leaf_lookup :: "'k \<Rightarrow> 'leaf \<Rightarrow> 'v option"
  leaf_insert :: "'k \<Rightarrow> 'v \<Rightarrow> 'leaf \<Rightarrow> 'leaf"
  leaf_insert_v2 :: "'k \<Rightarrow> 'v \<Rightarrow> 'leaf \<Rightarrow> 'leaf * 'v option"
  leaf_remove :: "'k \<Rightarrow> 'leaf \<Rightarrow> 'leaf"
  leaf_length :: "'leaf \<Rightarrow> nat"
  xdbg_leaf_kvs :: "'leaf \<Rightarrow> ('k*'v) s"  (* avoid for non-dbg code *)
  leaf_steal_right :: "'leaf*'leaf \<Rightarrow> 'leaf*'k*'leaf"
  leaf_steal_left :: "'leaf*'leaf \<Rightarrow> 'leaf*'k*'leaf"
  leaf_merge :: "'leaf*'leaf \<Rightarrow> 'leaf"
  split_large_leaf :: "'leaf \<Rightarrow> 'leaf*'k*'leaf"
  mk_leaf :: "('k*'v) s \<Rightarrow> 'leaf"  (* FIXME avoid? *)

datatype_record ('k,'r,'node) node_ops =
  split_large_node :: "'node \<Rightarrow> 'node*'k*'node"
  node_merge :: "'node * 'k * 'node \<Rightarrow> 'node"
  node_steal_right :: "'node * 'k * 'node \<Rightarrow> 'node * 'k * 'node"
  node_steal_left :: "'node * 'k * 'node \<Rightarrow> 'node * 'k * 'node"
  node_keys_length :: "'node \<Rightarrow> nat"
  node_make_small_root :: "'r*'k*'r \<Rightarrow> 'node"
  node_get_single_r :: "'node \<Rightarrow> 'r"  (* when we decrease the size of the tree in delete *)
  

type_synonym ('k,'r) simple_node_ops = "('k,'r,'k s * 'r s) node_ops"

definition mk_simple_node_ops :: "(('k s * 'r s) \<Rightarrow> ('k s * 'r s) * 'k * ('k s * 'r s)) \<Rightarrow> 
('k,'r) simple_node_ops" where
"mk_simple_node_ops sln = (
  \<lparr> split_large_node=sln,
    node_merge=(% ((ks1,rs1), k, (ks2,rs2)). (ks1@[k]@ks2,rs1@rs2)),
    node_steal_right=(% x. case x of 
      ((ks1,rs1),k1,(k2#ks2,r2#rs2)) \<Rightarrow> ( (ks1@[k1],rs1@[r2]),k2,(ks2,rs2))),
    node_steal_left=(% x. case x of
      ((ks1,rs1),k2,(ks2,rs2)) \<Rightarrow> 
      case (List.rev ks1, List.rev rs1) of
      (k1#ks1,r1#rs1) \<Rightarrow>
      ((List.rev ks1,List.rev rs1), k1, (k2#ks2,r1#rs2))),
    node_keys_length=(% (ks,_). List.length ks),
    node_make_small_root=(% (r1,k,r2). ([k],[r1,r2])),
    node_get_single_r=(% (ks,rs). List.hd rs)

  \<rparr>
)"

end







(*
(* FIXME do we also want to check wrt size constraints? probably yes *)

definition check_length_ks_rs :: "'k list * 'r list \<Rightarrow> bool" where
"check_length_ks_rs ks_rs = (
  let (ks,rs) = ks_rs in
  1+List.length ks = List.length rs)"
  

definition mk_Disk_node :: "'k list * 'r list \<Rightarrow> ('k,'v','r) dnode" where
"mk_Disk_node ks_rs = (
  (* enforce a wellformedness property *)
  let _ = check_true (% _. check_length_ks_rs ks_rs) in
  (Disk_node (ks_rs)))"

(* type_synonym pfr = "(key,value_t) t" *)

definition dest_Disk_node :: "('k,'v,'r) dnode \<Rightarrow> ('k list * 'r list)" where
"dest_Disk_node f = (case f of Disk_node x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_node''))"

definition dest_Disk_leaf :: "('k,'v,'r) dnode \<Rightarrow> ('k*'v) list" where
"dest_Disk_leaf f = (case f of Disk_leaf x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_leaf''))"


*)



(* old ================================== *)

(* there are local wf constraints relative to some particular
constants; but prefer to convert to tree and check wf *)

(*
definition wf_node_frame :: "constants \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"wf_node_frame c kn rn = ((kn + 1 = rn) & (c|>min_node_keys \<le> kn) & (kn \<le> c|>max_node_keys))"

definition wf_leaf_frame :: "constants \<Rightarrow> nat \<Rightarrow> bool" where
"wf_leaf_frame c n = ( c|>min_leaf_size \<le> n & n \<le> c|>max_leaf_size )"
*)

