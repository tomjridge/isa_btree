open Isa_export_wrapper
open Test_monad
open Test_util

let test_seq_insert () = 
  let cs = Constants.mk_constants 
      ~min_leaf_size:500
      ~max_leaf_size:1000
      ~min_node_keys:500
      ~max_node_keys:1000
  in
  let store_ops = Test_store.store_ops in
  Internal_make_pre_map_ops_etc.make ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
  fun ~pre_map_ops
    ~insert_many
    ~insert_all
    ~leaf_stream_ops
    ~leaf_ops:leaf_ops0
    ~node_ops:node_ops0
    ~frame_ops:frame_ops0
  ->
  let { leaf_lookup; find; insert; delete } = pre_map_ops in
  (* disable_isa_checks(); *)
  (* disable_tests(); *)
  let rec loop n r = 
    n <= 0 |> function
    | true -> () 
    | false -> 
      sp_to_fun (insert ~r ~k:n ~v:n) r |> function (Some r,_) -> 
        loop (n-1) r  (* guaranteed to return new r *)
  in
  loop (int_of_float 1e6) (Test_r (Disk_leaf map_ops.empty))
