theory Disk_node_to_tree  
  imports Disk_node Tree
begin

(* NOTE nothing requires dnode to be finite currently; FIXME perhaps add a hight to dnode *)
definition disk_node_to_tree' where
"disk_node_to_tree' leaf_ops node_ops self = (% dn.
  case dn of 
  Disk_node n \<Rightarrow> (
    n |> (node_ops|>dbg_node_krs) |> (% (ks,rs). 
    Node(ks,List.map self rs)))
  | Disk_leaf l \<Rightarrow> (
    l |> (leaf_ops|>dbg_leaf_kvs) |> Leaf))"

(* NOTE we require the 'r type var to be a dnode *)
function disk_node_to_tree :: 
"('k, 'v, 'leaf) leaf_ops \<Rightarrow> ('k, ('node, 'leaf) dnode, 'node) node_ops \<Rightarrow> ('node, 'leaf) dnode \<Rightarrow> ('k, 'v) tree" 
where
"disk_node_to_tree leaf_ops node_ops dn = (
  let self = % dn. disk_node_to_tree leaf_ops node_ops dn in
  disk_node_to_tree' leaf_ops node_ops self dn)"
apply (force)+ done
termination disk_node_to_tree
 by (force intro:FIXME)

(* find_consts "('k,'v)tree" *)

definition dummy :: unit where "dummy = ()"

end


