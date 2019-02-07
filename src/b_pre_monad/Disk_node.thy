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

datatype ('k,'r,'leaf,'unit) dnode = 
  Disk_node "'k list * 'r list" 
  | Disk_leaf "'leaf"

definition dest_Disk_node :: "('k,'r,'leaf,unit) dnode \<Rightarrow> ('k list * 'r list)" where
"dest_Disk_node f = (case f of Disk_node x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_node''))"

definition dest_Disk_leaf :: "('k,'r,'leaf,unit) dnode \<Rightarrow> 'leaf" where
"dest_Disk_leaf f = (case f of Disk_leaf x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_leaf''))"

datatype_record ('k,'v,'leaf) leaf_ops = 
  leaf_insert :: "'k \<Rightarrow> 'v \<Rightarrow> 'leaf \<Rightarrow> 'leaf"
  leaf_length :: "'leaf \<Rightarrow> nat"
  leaf_kvs :: "'leaf \<Rightarrow> ('k*'v) s"
  mk_leaf :: "('k*'v) s \<Rightarrow> 'leaf"
  
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

