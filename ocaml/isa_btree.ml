(** Isabelle B-tree definitions, as an OCaml lib *)

include Summary


(** {2 Assertion checking etc} *)
include Isa_export_wrapper.Isa_export_assert_flag


(** {2 Code exported from Isabelle, and a wrapper} *)

module Isa_export = Isa_export

module Isa_export_wrapper = Isa_export_wrapper


(** {2 Constants} *)

type constants = Constants.constants =
  {
    min_leaf_size: int;
    max_leaf_size: int;
    min_node_keys: int;
    max_node_keys: int
  }

module Constants = Constants


(** {2 Main types and interfaces} *)

module Isa_btree_intf = Isa_btree_intf

open Isa_btree_intf

type ('node,'leaf) dnode = ('node,'leaf) Dnode_type.dnode

type ('r,'dnode,'t) store_ops = ('r,'dnode,'t) Store_ops_type.store_ops

type ('k,'v,'leaf) leaf_ops = ('k,'v,'leaf) Isa_btree_intf.leaf_ops

type ('k,'r,'node) node_ops = ('k,'r,'node) Isa_btree_intf.node_ops

type ('k, 'v, 'r, 'ls, 't) leaf_stream_ops =
  ('k, 'v, 'r, 'ls, 't) Isa_btree_intf.leaf_stream_ops

type ('k, 'v, 'r, 'leaf, 'frame, 't) pre_map_ops =
  ('k, 'v, 'r, 'leaf, 'frame, 't) Isa_btree_intf.pre_map_ops

type ('k,'v,'r,'t,'leaf,'node,'ls) pre_btree_ops = 
  ('k,'v,'r,'t,'leaf,'node,'ls) Isa_btree_intf.pre_btree_ops


(** {2 Main functionality: make a B-tree} *)

module Make = Make


(** {2 Internal interfaces} *)

module Comparator_to_map_ops = Isa_btree_util.Comparator_to_map_ops

(** This is the "most general" interface *)
let make_with_k_maps = Isa_export_wrapper.make_with_k_maps

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
    let module B = Make.Make_v2(A) in
    let module C = struct include A include B end in
    (module C : T with type k=k and type v=v and type r=r and type t=t)

  let _ = make_with_first_class_module
end

module Leaf_node_frame_impls = Leaf_node_frame_impls

module Isa_btree_util = Isa_btree_util

module Profilers = Profilers
