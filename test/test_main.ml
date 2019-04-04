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
open Tjr_monad
open Test_store  (* also includes monad_ops *)
open Tjr_fs_shared.Kv_op

module Logger = Tjr_fs_shared.Logger



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

(* val config *)
include Tjr_config.Make(C)

open Isa_export_wrapper

type ii_op = (int,int) op [@@deriving yojson]

  

let execute_tests ~cs ~range ~fuel = 
  let store_ops = Test_store.store_ops in
  let { find; insert; delete } = 
    let k_cmp = Tjr_int.compare in
    make_find_insert_delete ~monad_ops ~cs ~k_cmp ~store_ops ~check_tree_at_r'
  in
  let ops = 
    range|>List.map (fun x -> Insert (x,x)) |> fun xs ->
    range|>List.map (fun x -> Delete x) |> fun ys -> 
    xs@ys
  in
  (* s is the spec... a map *)
  let rec depth n (r, (s:(int,int)Tjr_polymap.t) ) =
    if n = 0 then () else
    ops |> List.iter (fun op ->
        Logger.log(Test_store.t2s r);
        Logger.jlog (ii_op_to_yojson op);
        match op with
        | Insert (k,v) -> (
            insert ~r ~k ~v |> Imperative.from_m |> function (Some r) ->
              let s = Tjr_polymap.add k v s in
              (* assert(Tjr_polymap.bindings s = (Isa_export.Tree.tree_to_leaves r |> List.concat)); *)
              depth (n-1) (r,s))
        | Delete k -> (
            delete ~r ~k |> Imperative.from_m |> fun r -> 
            let s = Tjr_polymap.remove k s in
            (* assert(Tjr_polymap.bindings s = (Isa_export.Tree.tree_to_leaves r |> List.concat)); *)
            depth (n-1) (r,s)))
  in
  depth fuel (Leaf (empty_poly_map()),empty_poly_map())
  
;;

let main' ~range_min ~range_max ~constants = 
  let range = Tjr_list.mk_range ~min:range_min ~max:range_max ~step:1 in
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

let _ =
  Profile_manager.now := 
    Core.Time_stamp_counter.(fun () ->
        now () |> to_int63 |> Core.Int63.to_int |> fun (Some x) -> x)
[@@ocaml.warning "-8"]

let profiler = Profile_manager.create_profiler ~name:"my_profiler"


let _ = 
  match List.tl (Array.to_list (Sys.argv)) with
  | [] -> (
      Logger.logger := Some (Tjr_log.mk_log_ops());
      Logger.at_exit ~print:true;
      Printf.printf "%s: tests begin\n%!" __MODULE__;
      List.iter (fun pre_config -> main ~pre_config) config;
      Printf.printf "%s: tests OK\n%!" __MODULE__;
      Logger.at_exit ~print:false)
  | ["seq_insert"] -> (
      let cs = Constants.mk_constants 
                 ~min_leaf_size:500
                 ~max_leaf_size:1000
                 ~min_node_keys:500
                 ~max_node_keys:1000
      in
      let store_ops = Test_store.store_ops in
      let { find; insert; delete } = 
        let k_cmp = Tjr_int.compare in
        make_find_insert_delete ~monad_ops ~cs ~k_cmp ~leaf_ops ~store_ops 
      in
      Isa_test.disable_isa_checks();
      let rec loop n r = 
        if n <= 0 then () else
          insert ~r ~k:n ~v:n |> Imperative.from_m |> function (Some r) ->
          loop (n-1) r
      in
      loop (int_of_float 1e6) (Leaf (empty_poly_map()));
      print_profile_summary (profiler.get_marks())
    )
    | ["test_polymap"] -> (
        let rec loop n m = 
          if n <= 0 then () else
          Tjr_polymap.add n n m |> fun m -> 
          loop (n-1) m
      in
      loop (int_of_float 1e7) (Tjr_polymap.empty (fun (x:int) (y:int) -> Pervasives.compare x y))
    )
    
