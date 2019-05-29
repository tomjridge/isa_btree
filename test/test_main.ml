(** Exhaustively test the B-tree functionality, using a "correct"
   in-memory store. In this case, we use a "Tree store".

At the moment this takes constants from a config file, but perhaps we
   should test over a set of configs as well (just use the test code,
   parameterized by a config).

A previous version of the tests was fine-grained (each little step was
   tested). This just tests the big step.


We take 'r = tree. Then insert has type r -> k -> v -> (r option,'t)m

Here, we know that insert will always mutate, so we always get a Some.

We can also take ('a,t) m = 'a

*)

open Isa_btree
open Isa_export
open Tjr_monad
(* open Test_flag *)
open Test_monad
(* open Test_store  *)
open Test_util
open Tjr_fs_shared.Kv_op

open Test_leaf_node_frame_impls
(* module Test_impls = Test_leaf_node_frame_impls *)




(* test config ------------------------------------------------------ *)

module C = struct
  type pre_config = {
    range_min:int;
    range_max:int;
    min_leaf_size:int;
    max_leaf_size:int;
    min_node_keys:int;
    max_node_keys:int
  } [@@deriving yojson]
  type config = pre_config list [@@deriving yojson]
  let filename="test_config.json"
end

(* declares val config *)
include Tjr_config.Make(C)

let default_fuel = 6  (* 5 is not enough *)

open Isa_export_wrapper

type ii_op = (int,int) op [@@deriving yojson]

let k_cmp : int -> int -> int = Int_.compare

let map_ops = Tjr_map.make_map_ops k_cmp

let dbg_tree_at_r = fun r -> return ()

(*
let _make_pre_map_ops_etc = 
  Internal_make_pre_map_ops.make_pre_map_ops_etc
*)

type test_r = Test_leaf_node_frame_impls.test_r
type spec = (int,int,unit)Tjr_map.map

let execute_tests ~cs ~range ~fuel = 
  let dbg_frame f = 
    Logger.log_lazy (fun _ -> 
        Printf.sprintf "dbg_frame: %s\n" 
          (f |> test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
  in
  let store_ops = Test_store.store_ops in
  Internal_make_pre_map_ops.make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
  fun ~pre_map_ops
    ~insert_all
    ~leaf_stream_ops
    ~leaf_ops:leaf_ops0
    ~node_ops:node_ops0
    ~frame_ops:frame_ops0
    ->
  let { leaf_lookup; find; insert; delete } = pre_map_ops in
  let ops = 
    range|>List.map (fun x -> Insert (x,x)) |> fun xs ->
    range|>List.map (fun x -> Delete x) |> fun ys -> 
    xs@ys
  in
  (* FIXME here and later we are a little unsure about
     Small_root_node_or_leaf; FIXME the following is very inefficient
     *)
  let wf_tree = wf_tree ~cs ~ms:(Some Tree.Small_root_node_or_leaf) ~k_cmp in
  (* s is the spec... a map *)
  let test (r:test_r) (s:spec) = 
    Logger.log(__LOC__);
    Logger.log(test_r_to_string r);
    (* tree is wellformed (internal check) *)
    assert(r |> test_r_to_tree |> wf_tree);
    (* bindings match (check against spec) *)
    assert(map_ops.bindings s = (
        r 
        |> test_r_to_tree
        |> Isa_export.Tree.tree_to_leaves |> List.concat));
    ()
  in
  let rec depth n ((r:test_r), (s: spec)) =
    n = 0 |> function
    | true -> () 
    | false -> 
      ops |> List.iter (fun op ->
          Logger.log(test_r_to_string r);
          Logger.jlog (ii_op_to_yojson op);
          match op with
          | Insert (k,v) -> (
              sp_to_fun (insert ~r ~k ~v) r |> function (Some r,_) ->
                let s = map_ops.add k v s in
                let _ = test r s in
                depth (n-1) (r,s))
          | Delete k -> (
              sp_to_fun (delete ~r ~k) r |> fun (r,_) -> 
              let s = map_ops.remove k s in
              let _ = test r s in
              depth (n-1) (r,s)))
  in
  depth fuel (Test_r (Disk_leaf map_ops.empty),map_ops.empty)

;;

let main' ~range_min ~range_max ~constants = 
  let range = List_.mk_range ~min:range_min ~max:range_max ~step:1 in
  execute_tests ~cs:constants ~range ~fuel:default_fuel

let _ = main'

let main ~pre_config:c = 
  let constants = Constants.{
      min_leaf_size=c.C.min_leaf_size; max_leaf_size=c.max_leaf_size;
      min_node_keys=c.min_node_keys; max_node_keys=c.max_node_keys }
  in
  Printf.printf "range_min, range_max, constants: %d, %d, (%d,%d,%d,%d)\n%!" 
    c.range_min c.range_max c.min_leaf_size c.max_leaf_size c.min_node_keys c.max_node_keys;
  main' ~range_min:c.range_min ~range_max:c.range_max ~constants

let _ = monad_ops

(* test insert all -------------------------------------------------- *)

let test_insert_all cs = 
  let dbg_frame f = 
    Logger.log_lazy (fun _ -> 
        Printf.sprintf "dbg_frame: %s\n" 
          (f |> test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
  in
  let store_ops = Test_store.store_ops in
  Internal_make_pre_map_ops.make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
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

(* setup profiler ----------------------------------------------- *)

open Tjr_profile

(*
let profiler = 
  Tjr_profile.make_int_profiler 
    ~now:Core.Time_stamp_counter.(fun () ->
        now () |> to_int63 |> Core.Int63.to_int |> fun (Some x) -> x)
*)

let profiler = 
  Tjr_profile.make_string_profiler 
    ~now:Core.Time_stamp_counter.(fun () ->
        now () |> to_int63 |> Core.Int63.to_int |> fun (Some x) -> x)

let _ = 
  enable_isa_checks();
  (* enable_tests(); *)
  ()

let with_logger f = 
    Logger.logger := Some (Log.mk_log_ops());
    Logger.at_exit ~print:true;
    Logger.log_lazy (fun _ -> "Logger initialized");
    f();
    Logger.at_exit ~print:false
    
let _ = 
  let run_tests () = 
    with_logger (fun () -> 
    Printf.printf "%s: tests begin\n%!" __MODULE__;
    List.iter (fun pre_config -> main ~pre_config) config;
    Printf.printf "%s: tests OK\n%!" __MODULE__)
  in
  match List.tl (Array.to_list (Sys.argv)) with
  | [] | ["exhaustive"] -> begin
      Isa_export_wrapper.Internal_leaf_impl.leaf_profiler := profiler;
      enable_isa_checks();
      (* enable_tests(); *)
      run_tests();
      profiler.print_summary()
    end
  | ["test_leaf_impl"] -> 
    Isa_export_wrapper.Internal_leaf_impl.test_leaf_impl()
  | ["test_node_impl"] -> 
    with_logger (fun () -> Isa_export_wrapper.Internal_node_impl.test_node_impl())
  | ["test_delete"] -> 
    Test_delete.test()
  | ["insert_all"] -> 
    List.iter test_insert_all Constants.all_constants
(*  | ["no_asserts"] -> begin
      disable_isa_checks();
      disable_tests();  (* disable test flag *)
      run_tests()
    end*)
  | ["seq_insert"] -> begin
      let cs = Constants.mk_constants 
          ~min_leaf_size:500
          ~max_leaf_size:1000
          ~min_node_keys:500
          ~max_node_keys:1000
      in
      let store_ops = Test_store.store_ops in
      Internal_make_pre_map_ops.make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
      fun ~pre_map_ops
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
      loop (int_of_float 1e6) (Test_r (Disk_leaf map_ops.empty));
      profiler.print_summary()
    end
  | ["test_polymap"] -> begin
      let rec loop n m = 
        n <= 0 |> function
        | true -> ()
        | false -> 
          map_ops.add n n m |> fun m -> 
          loop (n-1) m
      in
      loop (int_of_float 1e7) map_ops.empty
    end
