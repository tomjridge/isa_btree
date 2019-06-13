(** Isabelle B-tree definitions, as an OCaml lib *)
open Isa_btree_intf

(** {2 Public interfaces} *)

(** {2 Assertion checking etc} *)
include Isa_export_wrapper.Isa_export_assert_flag


(** {2 Collection of all the interfaces in a separate module (we pull
   some of these out in the following).} *)
module Isa_btree_intf = Isa_btree_intf

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


(** {2 Main functionality: make a B-tree} *)

(* include Isa_export_wrapper.Internal_export *)

include Pre_btree_ops_type

(** This functor takes various types and constants (including, in
   particular, the type of keys and the value for the comparison on
   keys) and generates extra types [k_comparator...] for the map
   implementations. Then there is a function [make_btree_ops] which
   takes a [store_ops] and returns the B-tree operations.

    Note that these are "pre_btree_ops" because they expose internal
   types that we may want to hide: leaf, node, frame, leaf_stream(?).
   See tjr_btree for the simpler versions.

 *)
module Make(S:sig 
    type t
    type k
    type v
    type r
    val monad_ops: t monad_ops
    val cs: Constants.constants
    val k_cmp: k -> k -> int
  end) : (sig
  open S
  type node
  type leaf 
  type frame
  type leaf_stream
  val make_btree_ops: store_ops:(r, (node, leaf) dnode, t) store_ops ->
    (k, v, r, t, leaf, node, leaf_stream) pre_btree_ops
end)
= struct
  open Isa_export_wrapper
  open S

  module Map_ops = Isa_export_wrapper.Internal_make_map_ops(
    struct 
      type nonrec k = k 
      let k_cmp = k_cmp 
    end)
  open Map_ops

  let dbg_tree_at_r r = monad_ops.return ()

  type node = (k option, r, kopt_comparator) Base.Map.t
  type leaf = (k, v, k_comparator) Base.Map.t
  type frame = (k, r, node) Frame_type.frame
  type leaf_stream = (r, leaf, frame) Internal_leaf_stream_impl._t


  let make_btree_ops ~(store_ops:(r,(node,leaf)dnode,t)store_ops) 
    : (k,v,r,t,leaf,node,leaf_stream) pre_btree_ops
    = 
    Internal_make_with_kargs.(
      let k_args = { k_cmp; k_map=k_map(); kopt_map=kopt_map() } in
      make_with_kargs ~monad_ops ~cs ~k_args ~dbg_tree_at_r ~store_ops)

  let _ = make_btree_ops
end


(** {2 Internal interfaces} *)

module Isa_export = Isa_export
module Isa_export_wrapper = Isa_export_wrapper
