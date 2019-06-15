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


(*
(** {2 Insert all and insert many} *)

include Insert_all_type

include Insert_many_type
*)


(** {2 Store ops} *)

include Store_ops_type


(*
(** {2 Leaf stream ops} *)

include Leaf_stream_ops_type
*)


(** {2 Main functionality: make a B-tree} *)

(* include Isa_export_wrapper.Internal_export *)

(** A record of operations provided by the B-tree *)

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

module Make(S:S) : (sig
  open S
  type leaf 
  type node
  type leaf_stream

  val leaf_ops: (k,v,leaf)leaf_ops
  val node_ops: (k,r,node)node_ops

  val make_btree_ops: 
    store_ops:(r, (node, leaf) dnode, t) store_ops ->
    (k, v, r, t, leaf, node, leaf_stream) pre_btree_ops
end)
= struct
  open Isa_export_wrapper
  open S

  module Map_ops = Isa_btree_util.Internal_make_map_ops(
    struct 
      type nonrec k = k 
      let k_cmp = k_cmp 
    end)
  include Map_ops

  type node = (k option, r, kopt_comparator) Base.Map.t
  type leaf = (k, v, k_comparator) Base.Map.t
  type frame = (k, r, node) Frame_type.frame
  type leaf_stream = (r, leaf, frame) Internal_leaf_stream_impl._t

  let leaf_node_frame_ops = Leaf_node_frame_impls.make_leaf_node_frame_ops_from_comparators ~k_cmp:k_comparator ~kopt_cmp:kopt_comparator
  let leaf_ops = leaf_node_frame_ops.leaf_ops
  let node_ops = leaf_node_frame_ops.node_ops

  let make_btree_ops ~(store_ops:(r,(node,leaf)dnode,t)store_ops)
    : (k,v,r,t,leaf,node,leaf_stream)pre_btree_ops
    = 
    Internal_make_with_comparators.(
      make_with_comparators ~monad_ops ~cs ~k_cmp:k_comparator ~kopt_cmp:kopt_comparator ~store_ops)

  let _ = make_btree_ops
end


(** {2 Internal interfaces} *)

module Comparator_to_map_ops = Isa_btree_util.Comparator_to_map_ops

let make_with_comparators = Isa_export_wrapper.make_with_comparators

module Make_with_first_class_module = struct

  module type T = sig
    type k 
    type v 
    type r
    type t
    type node
    type leaf
    type leaf_stream

    (** These leaf and node ops allow store_ops to convert internal
       types to lists that can be stored on disk. *)
    val leaf_ops: (k,v,leaf)leaf_ops
    val node_ops: (k,r,node)node_ops

    val make_btree_ops :
      store_ops:(r, (node, leaf) dnode, t) store_ops ->
      (k, v, r, t, leaf, node, leaf_stream) pre_btree_ops
  end

  let make_with_first_class_module (type k v r t) ~monad_ops ~cs ~k_cmp = 
    let module A = struct 
      type nonrec k=k
      type nonrec v=v
      type nonrec r=r
      type nonrec t=t
      let k_cmp=k_cmp
      let monad_ops = monad_ops
      let cs = cs
    end
    in
    let module B = Make(A) in
    let module C = struct include A include B end in
    (module C : T with type k=k and type v=v and type r=r and type t=t)

  let _ = make_with_first_class_module
end

module Leaf_node_frame_impls = Leaf_node_frame_impls
module Isa_export = Isa_export
module Isa_export_wrapper = Isa_export_wrapper
module Isa_btree_util = Isa_btree_util
module Notes = Notes
