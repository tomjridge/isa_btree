(** Unit tests for specific delete cases. *)

open Isa_export
open Isa_export_wrapper
open Test_leaf_node_frame_impls
open Test_monad

let store_ops = Test_store.store_ops

let init_tree' = 
  let l = Leaf' [(1,1)] in
  let r = Leaf' [(2,2);(3,3)] in
  Node' ([2],[l;r])
                       
let t'2r = Test_leaf_node_frame_impls.tree'_to_test_r

let cs = Constants.{
    min_leaf_size=1;
    max_leaf_size=2;
    min_node_keys=1;
    max_node_keys=1
  }

let k_cmp = Int_.compare

let wf_tree = wf_tree ~cs ~ms:(Some Tree.Small_root_node_or_leaf) ~k_cmp 

let test_1 () = assert(wf_tree (tree'_to_tree init_tree'))

let pre_btree_ops = 
  Test_leaf_node_frame_impls.make_btree_ops
    ~monad_ops ~cs ~store_ops

let { delete; _ } = pre_btree_ops

(* leaf steal right case *)
let test_2 () =
  let r = init_tree'|>t'2r in
  delete ~r ~k:1 |> fun op ->
  sp_to_fun op r |> fun (r',_) ->
  r' |> test_r_to_yojson |> fun j -> 
  Printf.printf "Leaf_steal_right: %s\n" (Yojson.Safe.pretty_to_string j);
  r' |> test_r_to_tree' |> fun t' -> 
  assert(t' = Node'([3],[ Leaf'[(2,2)];Leaf'[(3,3)]]))

(* leaf steal left case *)
let test_3 () = 
  Node'([3],[ Leaf'[(1,1);(2,2)];Leaf'[(3,3)]]) |> fun t' -> 
  t' |> t'2r |> fun r ->
  delete ~r ~k:3 |> fun op ->
  sp_to_fun op r |> fun (r',_) -> 
  r' |> test_r_to_yojson |> fun j -> 
  Printf.printf "Leaf_steal_left: %s\n" (Yojson.Safe.pretty_to_string j);
  r' |> test_r_to_tree' |> fun t'' -> 
  assert(t'' = Node'([2],[ Leaf'[(1,1)];Leaf'[(2,2)]]))
  
  

let test () =
  test_1();
  test_2();
  test_3()
