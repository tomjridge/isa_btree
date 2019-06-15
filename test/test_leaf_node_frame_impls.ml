(* We redeclare tree type, specialized to int,int. This makes yojson
   serialization easier. 

  tree(Node,Leaf)

  tree'(Node',Leaf')

  tree' --tree'_to_tree--> tree

  test_node=(int option,test_r,_) map
  test_leaf=(int,int,_)map
  test_r=Test_r of (test_node,test_leaf)dnode
  
  test_r --test_r_to_tree'--> tree'
  tree' --tree'_to_test_r--> test_r

  test_r --test_r_to_tree--> tree


*)

open Isa_btree

module Internal = struct
  module T1 = struct
    type tree' = 
        Node' of int list * tree' list | Leaf' of (int*int) list
    [@@deriving yojson]
  end
  include T1

  (* Map to Isabelle.Tree.tree, so we can perform wf checks easily *)
  let rec tree'_to_tree t = match t with
    | Node' (ks,ts) -> Isa_export.Tree.Node(ks,List.map tree'_to_tree ts)
    | Leaf' kvs -> Leaf kvs

  (* leaf and node test impls ----------------------------------------- *)


  module Map_ops = Isa_btree_util.Internal_make_map_ops(struct
      type k=int
      let k_cmp = Pervasives.compare
    end)
  include Map_ops
       
  module T2 = struct
    type test_leaf = (int,int,k_comparator) Base.Map.t
  end
  include T2

  let leaf_map_ops : (int, int, _) Tjr_map.With_base_as_record.map_ops = k_map()

  open Isa_export.Disk_node

  module T3 = struct
    type test_node = (int option, test_r, kopt_comparator) Base.Map.t

    (* test_r is the type of r for the test_store *)
    and test_r = Test_r of (test_node,test_leaf)dnode
  end
  include T3

  let node_map_ops : (int option, test_r, _) Tjr_map.With_base_as_record.map_ops 
    = kopt_map()

  let _ = node_map_ops



  (* tree' test_r conversions --------------------------------------- *)

  (* open Tjr_map.With_base *)
      
  let rec tree'_to_test_r = function
    | Leaf' kvs -> Test_r(Disk_leaf(leaf_map_ops.of_bindings kvs))
    | Node' (ks,rs) -> 
      let ks = None::(List.map (fun x -> Some x) ks) in
      let rs = List.map tree'_to_test_r rs in
      let krs = List.combine ks rs in
      Test_r(Disk_node(node_map_ops.of_bindings krs))

  (* convert to yojson *)

  module Test_r_to_tree = struct
    let rec test_node_to_Node' n = 
      n 
      |> node_map_ops.bindings
      |> List.split |> fun (ks,rs) -> 
      List.(tl ks |> map dest_Some,map test_r_to_tree' rs) |> fun (ks,rs) ->
      Node' (ks,rs)

    and test_leaf_to_Leaf' l = 
      l 
      |> leaf_map_ops.bindings
      |> fun xs -> Leaf' xs

    and test_r_to_tree' (Test_r r) = match r with
      | Disk_node n -> n |> test_node_to_Node'
      | Disk_leaf l -> l |> test_leaf_to_Leaf'

    let test_r_to_yojson r = r |> test_r_to_tree' |> tree'_to_yojson

    let _ = test_r_to_yojson

    let test_r_to_tree r = test_r_to_tree' r |> tree'_to_tree

    let test_r_to_string r = test_r_to_yojson r |> Yojson.Safe.pretty_to_string
  end
  include Test_r_to_tree


  (* frame test impl -------------------------------------------------- *)
  (* open Isa_export_wrapper *)

  let test_node_to_yojson n = n |> test_node_to_Node' |> tree'_to_yojson

  type test_frame = (int,test_r,test_node) Isa_btree_intf.Frame_type.frame
  [@@deriving to_yojson] 
end
open Internal

module Export = struct
  include T1
  include T2 
  include T3
  let tree'_to_tree = tree'_to_tree
  let test_r_to_tree' = test_r_to_tree'
  let tree'_to_test_r = tree'_to_test_r
  let test_r_to_tree = test_r_to_tree
  let test_r_to_yojson = test_r_to_yojson
  let test_r_to_string = test_r_to_string
  let test_frame_to_yojson = test_frame_to_yojson
  (* let k_args = Isa_export_wrapper.{  *)
      (* k_cmp=Pervasives.compare; k_map=leaf_map_ops; kopt_map=node_map_ops } *)
  let make_btree_ops ~monad_ops ~cs ~store_ops = 
    Isa_btree.make_with_comparators ~monad_ops ~cs 
      ~k_cmp:Internal.k_comparator 
      ~kopt_cmp:Internal.kopt_comparator
      ~store_ops

end

include Export


