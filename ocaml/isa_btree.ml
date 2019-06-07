(** Isabelle B-tree definitions, as an OCaml lib *)
open Isa_btree_intf

(** {2 Public interfaces} *)

(** {2 Assertion checking etc} *)
include Isa_export_wrapper.Isa_export_assert_flag


(** {2 Constants} *)

type constants = Constants.constants =
  {
    min_leaf_size: int;
    max_leaf_size: int;
    min_node_keys: int;
    max_node_keys: int
  }

module Constants = Constants


(** {2 Disk-backed nodes} *)

include Isa_btree_intf.Dnode_type


(*
(** {2 Node/leaf conversions to/from lists} *)

include Isa_export_wrapper.Node_leaf_conversions_type

(*
include Isa_export_wrapper.Leaf_ops_type
include Isa_export_wrapper.Node_ops_type
*)
*)

(** {2 Pre-map ops} *)

include Pre_map_ops_type


(** {2 Insert all and insert many} *)

include Insert_all_type

include Insert_many_type

(** {2 Store ops} *)

include Store_ops_type


(** {2 Leaf stream ops} *)

include Leaf_stream_ops_type


(** {2 Main functionality: make_isa_btree} *)

(* include Isa_export_wrapper.Internal_export *)

include Btree_ops_type

include Isa_export_wrapper.Export

(** This functor takes a [k_cmp] and generates extra types
   [k_comparator...] for the map implementations. Then there is a
   function [make_btree_ops] which takes a [store_ops] and returns the
   B-tree operations *)
module Make(S:sig 
    type t
    type k
    type v
    type r
    val monad_ops: t monad_ops
    val cs: Constants.constants
    val k_cmp: k -> k -> int
end) = struct
  open S


  (* TODO convert k_cmp to k_comparator *)
  type k_comparator
  let k_comparator : (k,k_comparator)Base.Map.comparator = failwith "FIXME"
  let k_map :(k,v,_)Tjr_map.With_base.map_ops = Tjr_map.With_base.make_map_ops k_comparator

  type kopt_comparator
  let kopt_comparator : (k option,kopt_comparator)Base.Map.comparator = failwith "FIXME"
  let kopt_map : (k option,r,_)Tjr_map.With_base.map_ops = Tjr_map.With_base.make_map_ops kopt_comparator

  let dbg_tree_at_r r = monad_ops.return ()

  let make_btree_ops ~store_ops = 
    make ~monad_ops ~cs ~k_cmp ~k_map ~kopt_map ~dbg_tree_at_r ~store_ops
end

(** {2 Internal interfaces} *)

module Isa_export = Isa_export
module Isa_export_wrapper = Isa_export_wrapper
