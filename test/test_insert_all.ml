open Isa_btree
open Isa_export
open Isa_export_wrapper
open Tjr_monad
open Test_monad
open Test_leaf_node_frame_impls
open Test_util

let test_insert_all cs = 
  let dbg_frame f = 
    Logger.log_lazy (fun _ -> 
        Printf.sprintf "dbg_frame: %s\n" 
          (f |> test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
  in
  let store_ops = Test_store.store_ops in
  Internal_make_pre_map_ops_etc.make ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
  fun ~pre_map_ops
    ~insert_all
    ~leaf_stream_ops
    ~leaf_ops:leaf_ops0
    ~node_ops:node_ops0
    ~frame_ops:frame_ops0
    -> 
  let { insert_all } = insert_all in
  (* s is the spec... a map *)
  let r = Test_r(Disk_leaf map_ops.empty) in
  let open Tjr_seq in
  let high = int_of_string "1E4" in
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
    = (take_and_drop 10000 kvs |> fun (kvs,_) -> kvs)); 
  ()

