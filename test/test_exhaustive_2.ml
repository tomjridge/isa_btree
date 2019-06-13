(** Exhaustively test the B-tree functionality, using a "correct"
   in-memory store. In this case, we use a "Tree store".

This version uses sets of states rather than depth-first search.
*)

(* test config ------------------------------------------------------ *)

open Isa_export_wrapper
open Test_monad
open Test_leaf_node_frame_impls
open Test_util

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
  let default_config = None
  let filename="test_exhaustive_2.json"
end

(* declares val config *)
include Tjr_config.Make(C)

module Internal = struct
  type test_r = Test_leaf_node_frame_impls.test_r
  type spec = (int,int,unit)Tjr_map.map

  let execute_tests ~cs ~range = 
    let dbg_frame f = 
      Logger.log_lazy (fun _ -> 
          Printf.sprintf "dbg_frame: %s\n" 
            (f |> test_frame_to_yojson |> Yojson.Safe.pretty_to_string))
    in
    let store_ops = Test_store.store_ops in
    let bt = Test_leaf_node_frame_impls.make_btree_ops
                      ~monad_ops ~cs ~dbg_tree_at_r:(fun _ -> return ()) ~store_ops
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
    let tbl = Hashtbl.create 100 in
    let test_r_to_spec r =
        Hashtbl.find_opt tbl r |> function
        | None -> failwith __LOC__
        | Some s -> s
    in
    let add_spec_for_r r s = 
      (* assert(Hashtbl.mem tbl r = false); *)
      Hashtbl.add tbl r s
    in
    let init_state = Test_r (Disk_leaf (leaf_ops.kvs_to_leaf [])) in
    add_spec_for_r init_state map_ops.empty;
    (* use the functionality from Tjr_lib.Exhaustive_testing *)
    Exhaustive_testing.test 
      ~cmp:Pervasives.compare
      ~step:(fun r op -> 
          let s = test_r_to_spec r in
          match op with
          | Insert (k,v) -> (
              sp_to_fun (insert ~r ~k ~v) r |> function (Some r,_) ->                
                let s = map_ops.add k v s in
                test r s;
                add_spec_for_r r s;
                [r])
          | Delete k -> (
                sp_to_fun (delete ~r ~k) r |> fun (r,_) -> 
                let s = map_ops.remove k s in
                test r s;
                add_spec_for_r r s;
                [r]))
      ~check_state:(fun _ -> ())  (* already checked in step *)
      ~check_step:(fun t op t' -> ())  (* ditto *)
      ~ops
      ~init_states:[init_state]

  let execute_tests ~range_min ~range_max ~constants = 
    let range = List_.mk_range ~min:range_min ~max:range_max ~step:1 in
    execute_tests ~cs:constants ~range

  let execute_tests ~pre_config:c = 
    let constants = Constants.{
        min_leaf_size=c.C.min_leaf_size; max_leaf_size=c.max_leaf_size;
        min_node_keys=c.min_node_keys; max_node_keys=c.max_node_keys }
    in
    Printf.printf "range_min, range_max, constants: %d, %d, (%d,%d,%d,%d)\n%!" 
      c.range_min c.range_max c.min_leaf_size c.max_leaf_size c.min_node_keys c.max_node_keys;
    execute_tests ~range_min:c.range_min ~range_max:c.range_max ~constants

end

let test_exhaustive = Internal.execute_tests
