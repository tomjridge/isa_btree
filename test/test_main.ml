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
open Test_flag
open Test_store  (* also includes monad_ops *)
open Tjr_fs_shared.Kv_op

module Test_impls = Test_leaf_node_frame_impls




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
  let filename="config.json"
end

(* declares val config *)
include Tjr_config.Make(C)

open Isa_export_wrapper

type ii_op = (int,int) op [@@deriving yojson]

let k_cmp : int -> int -> int = Int_.compare

let map_ops = Poly_map.make_map_ops k_cmp

let dbg_tree_at_r = fun r -> return ()

let _make_pre_map_ops_etc = 
  Internal_make_pre_map_ops.make_pre_map_ops_etc

type test_r = Test_leaf_node_frame_impls.test_r
type spec = (int,int,unit)Poly_map.map

let execute_tests ~cs ~range ~fuel = 
  let dbg_frame f = 
    Logger.log_lazy (fun _ -> 
        Printf.sprintf "dbg_frame: %s\n" 
          (f |> Test_impls.test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
  in
  let store_ops = Test_store.store_ops in
  _make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
  fun ~pre_map_ops
    ~pre_insert_many_op
    ~leaf_stream_ops
    ~leaf_ops:leaf_ops0
    ~node_ops:node_ops0
    ~frame_ops:frame_ops0
    ~kvs_to_leaf
    ~leaf_to_kvs
    ~krs_to_node
    ~node_to_krs ->
  let { leaf_lookup; find; insert; delete } = pre_map_ops in
  let ops = 
    range|>List.map (fun x -> Insert (x,x)) |> fun xs ->
    range|>List.map (fun x -> Delete x) |> fun ys -> 
    xs@ys
  in
  (* s is the spec... a map *)
  let test (r:test_r) (s:spec) = 
    (* FIXME here and later we are a little unsure about
       Samll_root_node_or_leaf; FIXME the following is very
       inefficient *)
    let wf_tree = wf_tree ~cs ~ms:(Some Tree.Small_root_node_or_leaf) ~k_cmp in
    let _ = if test_flag() then begin
        (* tree is wellformed (internal check) *)
        assert(r |> Test_impls.test_r_to_tree |> wf_tree);
        (* bindings match (check against spec) *)
        assert(map_ops.bindings s = (
            r 
            |> Test_impls.test_r_to_tree
            |> Isa_export.Tree.tree_to_leaves |> List.concat));
      end
    in
    ()
  in
  let rec depth n ((r:test_r), (s: spec)) =
    n = 0 |> function
    | true -> () 
    | false -> 
      ops |> List.iter (fun op ->
          (* Logger.log(Test_store.t2s r); *)
          (* Logger.jlog (ii_op_to_yojson op); *)
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
  execute_tests ~cs:constants ~range ~fuel:5 

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


(* setup profiler ----------------------------------------------- *)

open Tjr_profile

let profiler = 
  Tjr_profile.make_int_profiler 
    ~now:Core.Time_stamp_counter.(fun () ->
        now () |> to_int63 |> Core.Int63.to_int |> fun (Some x) -> x)

let _ = 
  let run_tests () = 
    Logger.logger := Some (Log.mk_log_ops());
    Logger.at_exit ~print:true;
    Logger.log_lazy (fun _ -> "Logger initialized");
    Printf.printf "%s: tests begin\n%!" __MODULE__;
    List.iter (fun pre_config -> main ~pre_config) config;
    Printf.printf "%s: tests OK\n%!" __MODULE__;
    Logger.at_exit ~print:false
  in
  match List.tl (Array.to_list (Sys.argv)) with
  | [] -> begin
      enable_isa_checks();
      enable_tests();
      run_tests() 
    end
  | ["no_asserts"] -> begin
      disable_isa_checks();
      disable_tests();
      run_tests()
    end
  | ["seq_insert"] -> begin
      let cs = Constants.mk_constants 
          ~min_leaf_size:500
          ~max_leaf_size:1000
          ~min_node_keys:500
          ~max_node_keys:1000
      in
      let store_ops = Test_store.store_ops in
      _make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r @@
      fun ~pre_map_ops
        ~pre_insert_many_op
        ~leaf_stream_ops
        ~leaf_ops:leaf_ops0
        ~node_ops:node_ops0
        ~frame_ops:frame_ops0
        ~kvs_to_leaf
        ~leaf_to_kvs
        ~krs_to_node
        ~node_to_krs ->
      let { leaf_lookup; find; insert; delete } = pre_map_ops in
      disable_isa_checks();
      disable_tests();
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
