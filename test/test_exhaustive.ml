(** DEPRECATED!!! Exhaustively test the B-tree functionality, using a "correct"
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

(* test config ------------------------------------------------------ *)

open Isa_export_wrapper
open Test_monad
open Test_leaf_node_frame_impls
open Test_util
open Test_spec

module C = struct
  type pre_config = {
    range_min:int;
    range_max:int;
    fuel:int;
    min_leaf_size:int;
    max_leaf_size:int;
    min_node_keys:int;
    max_node_keys:int
  } [@@deriving yojson]
  type config = pre_config list [@@deriving yojson]
  let default_config = None
  let filename="test_config.json"
end

(* declares val config *)
include Tjr_config.Make(C)

module Internal = struct
  type test_r = Test_leaf_node_frame_impls.test_r
  type spec = (int,int,unit)Tjr_map.map

  let execute_tests ~cs ~range ~fuel = 
    let map_ops = spec_map_ops in     
    let dbg_frame f = 
      Logger.log_lazy (fun _ -> 
          Printf.sprintf "dbg_frame: %s\n" 
            (f |> test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
    in
    let store_ops = Test_store.store_ops in
    let bt = 
      Test_leaf_node_frame_impls.make_btree_ops ~monad_ops ~cs ~store_ops
    in
    let { leaf_ops; find; insert; delete; _ } = bt in
    let ops = 
      range|>List.map (fun x -> Insert (x,x)) |> fun xs ->
      range|>List.map (fun x -> Delete x) |> fun ys -> 
      xs@ys
    in
    (* FIXME here and later we are a little unsure about
       Small_root_node_or_leaf; FIXME the following is very inefficient
    *)
    let wf_tree = wf_tree ~cs ~ms:(Some Isa_export.Tree.Small_root_node_or_leaf) ~k_cmp in
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
    depth fuel (Test_r (Disk_leaf (leaf_ops.kvs_to_leaf [])),map_ops.empty)


  let main' ~range_min ~range_max ~fuel ~constants = 
    let range = List_.mk_range ~min:range_min ~max:range_max ~step:1 in
    execute_tests ~cs:constants ~range ~fuel

  let _ = main'

  let main ~pre_config:c = 
    let constants = Constants.{
        min_leaf_size=c.C.min_leaf_size; max_leaf_size=c.max_leaf_size;
        min_node_keys=c.min_node_keys; max_node_keys=c.max_node_keys }
    in
    Printf.printf "range_min, range_max, fuel, constants: %d, %d, %d, (%d,%d,%d,%d)\n%!" 
      c.range_min c.range_max c.fuel c.min_leaf_size c.max_leaf_size c.min_node_keys c.max_node_keys;
    main' ~range_min:c.range_min ~range_max:c.range_max ~fuel:c.fuel ~constants

end

let test_exhaustive = Internal.main
