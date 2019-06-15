(** Some testing of insert_many and insert_all. *)

open Isa_btree
open Isa_export
open Isa_export_wrapper
open Tjr_monad
open Test_monad
open Test_leaf_node_frame_impls
open Test_util
open Test_store
open Test_spec

let test_insert_many cs =
  let bt = 
    Test_leaf_node_frame_impls.make_btree_ops ~monad_ops ~cs ~store_ops
  in
  Logger.log_lazy (fun () -> Printf.sprintf "Constants: %s\n" (cs|>Constants.cs2s));
  let { insert_all; insert_many; leaf_ops; _ } = bt in
  let Isa_btree_intf.Insert_all_type.{ insert_all } = insert_all in
  let Isa_btree_intf.Insert_many_type.{ insert_many } = insert_many in
  (* s is the spec... a map *)
  let r = Test_r(Disk_leaf (leaf_ops.kvs_to_leaf [])) in
  let open Tjr_seq in
  let high = int_of_string "10" in
  let {take_and_drop},kvs = (1 -- high) in
  let {take_and_drop} = {take_and_drop} |> Tjr_seq.map (fun x -> (x,x)) in
  let ((k,v)::kvs),_ = take_and_drop high kvs in
  Logger.log_lazy (fun () -> Printf.sprintf "kvs: %d\n" (1+List.length kvs));
  sp_to_fun (insert_many ~r ~k ~v ~kvs) r |> fun ((kvs',_),r') -> 
  let wf_tree = wf_tree ~cs ~ms:(Some Tree.Small_root_node_or_leaf) ~k_cmp in
  assert (wf_tree (test_r_to_tree r'));
  let kvs_in_store = r'
                     |> test_r_to_tree
                     |> Isa_export.Tree.tree_to_leaves |> List.concat
  in  
  let n_in_store, n_remaining = List.length kvs_in_store, List.length kvs' in
  Printf.printf "Initially %d; after insert, %d in store, %d remaining\n%!" high n_in_store n_remaining;
  assert(high = n_in_store+n_remaining);
  ()


let test_insert_all cs = 
  let store_ops = Test_store.store_ops in
  let bt = 
    Test_leaf_node_frame_impls.make_btree_ops ~monad_ops ~cs ~store_ops
  in
  let insert_all = bt.insert_all.insert_all in
  (* s is the spec... a map *)
  let r = Test_r(Disk_leaf (bt.leaf_ops.kvs_to_leaf [])) in
  let open Tjr_seq in
  let high = int_of_string "2" in
  let {take_and_drop},kvs = (1 -- high) in
  let {take_and_drop} = {take_and_drop} |> Tjr_seq.map (fun x -> (x,x)) in
  let rec loop r kvs = 
    match take_and_drop 100 kvs with
    | [],_ -> r
    | kvs,rest -> 
      List.iter (fun (x,_) -> Printf.printf "x %d\n" x) kvs;
      sp_to_fun (insert_all ~r ~kvs) r |> fun (r',_) -> 
      loop r' rest
  in
  loop r kvs |> fun r -> 
  let wf_tree = wf_tree ~cs ~ms:(Some Tree.Small_root_node_or_leaf) ~k_cmp in
  assert (wf_tree (test_r_to_tree r));
  let kvs' = r
             |> test_r_to_tree
             |> Isa_export.Tree.tree_to_leaves |> List.concat
  in
  Printf.printf "After insert, %d entries\n%!" (List.length kvs');
  let _ = List.iter (fun (x,_) -> Printf.printf "%d\n" x) kvs' in
  assert(high = List.length kvs');
  assert (
    kvs'
    = (take_and_drop high kvs |> fun (kvs,_) -> kvs)); 
  ()

