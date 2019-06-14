(* open Isa_export_wrapper *)
open Test_monad
(* open Test_util *)

let test_seq_insert () = 
  let cs = Constants.mk_constants 
      ~min_leaf_size:500
      ~max_leaf_size:1000
      ~min_node_keys:500
      ~max_node_keys:1000
  in
  let store_ops = Test_store.store_ops in
  let bt = Test_leaf_node_frame_impls.make_btree_ops
      ~monad_ops ~cs ~store_ops
  in
  let { leaf_ops; find; insert; delete; _ } = bt in
  (* disable_isa_checks(); *)
  (* disable_tests(); *)
  let rec loop n r = 
    n <= 0 |> function
    | true -> () 
    | false -> 
      sp_to_fun (insert ~r ~k:n ~v:n) r |> function (Some r,_) -> 
        loop (n-1) r  (* guaranteed to return new r *)
  in
  loop (int_of_float 1e6) (Test_r (Disk_leaf (leaf_ops.kvs_to_leaf [])))
