(* We redeclare tree type, specialized to int,int. This makes yojson
   serialization easier. *)

open Isa_btree

(* let dest_Some = Isa_export_wrapper.dest_Some *)


type tree' = 
    Node' of int list * tree' list | Leaf' of (int*int) list
[@@deriving yojson]

(* Map to Isabelle.Tree.tree, so we can perform wf checks easily *)
let rec tree'_to_tree t = match t with
  | Node' (ks,ts) -> Isa_export.Tree.Node(ks,List.map tree'_to_tree ts)
  | Leaf' kvs -> Leaf kvs


(* leaf and node test impls ----------------------------------------- *)


type test_leaf' = unit

type test_leaf = (int,int,test_leaf') Tjr_map.map

let _leaf_map_ops : (int, int, test_leaf) Tjr_map.map_ops = 
  Tjr_map.make_map_ops Int_.compare


include struct
  open Isa_export.Disk_node

  type test_node' = unit

  type test_node = (int option, test_r, test_node') Tjr_map.map

  (* test_r is the type of r for the test_store *)
  and test_r = Test_r of (test_node,test_leaf)dnode
end

let _node_map_ops : (int option, test_r, test_node) Tjr_map.map_ops = 
  Tjr_map.make_map_ops 
    (Isa_btree.Isa_export_wrapper.Internal_node_impl.key_compare Int_.compare)


(* convert to yojson *)

let rec test_node_to_Node' n = 
    n 
    |> _node_map_ops.bindings
    |> List.split |> fun (ks,rs) -> 
    (List.tl ks |> List.map dest_Some,List.map test_r_to_tree' rs) |> fun (ks,rs) ->
    Node' (ks,rs)

and test_leaf_to_Leaf' l = 
    l 
    |> _leaf_map_ops.bindings
    |> fun xs -> Leaf' xs

and test_r_to_tree' (Test_r r) = match r with
  | Disk_node n -> n |> test_node_to_Node'
  | Disk_leaf l -> l |> test_leaf_to_Leaf'

let test_r_to_yojson r = r |> test_r_to_tree' |> tree'_to_yojson

let _ = test_r_to_yojson

let test_r_to_tree r = test_r_to_tree' r |> tree'_to_tree


(* frame test impl -------------------------------------------------- *)

open Isa_export_wrapper

let test_node_to_yojson n = n |> test_node_to_Node' |> tree'_to_yojson

type test_frame = (int,test_r,test_node) Internal_frame_impl.frame [@@deriving to_yojson]
