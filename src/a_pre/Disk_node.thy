theory Disk_node  
imports Prelude
begin

(* blocks on disk correspond to nodes, which are like tree nodes, but
with pointers rather than children *)

(* type variable naming conventions:

'k - keys
'v - values
'r - references to disk blocks

*)

datatype ('k,'v,'r) dnode = 
  Disk_node "'k list * 'r list" 
  | Disk_leaf "('k*'v) list"


(* type_synonym pfr = "(key,value_t) t" *)

definition dest_Disk_node :: "('k,'v,'r) dnode \<Rightarrow> ('k list * 'r list)" where
"dest_Disk_node f = (case f of Disk_node x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_node''))"

definition dest_Disk_leaf :: "('k,'v,'r) dnode \<Rightarrow> ('k*'v) list" where
"dest_Disk_leaf f = (case f of Disk_leaf x \<Rightarrow> x  | _ \<Rightarrow> failwith (STR ''dest_Disk_leaf''))"







(* old ================================== *)

(* there are local wf constraints relative to some particular
constants; but prefer to convert to tree and check wf *)

(*
definition wf_node_frame :: "constants \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"wf_node_frame c kn rn = ((kn + 1 = rn) & (c|>min_node_keys \<le> kn) & (kn \<le> c|>max_node_keys))"

definition wf_leaf_frame :: "constants \<Rightarrow> nat \<Rightarrow> bool" where
"wf_leaf_frame c n = ( c|>min_leaf_size \<le> n & n \<le> c|>max_leaf_size )"
*)

end