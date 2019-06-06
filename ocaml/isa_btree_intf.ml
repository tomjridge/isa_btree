(** Jane Street-style interface file *)

(* NOTE defn. in Isabelle *)
(* type ('k,'r,'node) node_ops' = ('k,'r,'node) Disk_node.node_ops *)

module Dnode_type = struct
  (** Recall [dnode] type *)
  type ('node,'leaf) dnode = ('node,'leaf) Isa_export.Disk_node.dnode = 
      Disk_node of 'node | Disk_leaf of 'leaf
end
include Dnode_type

module Leaf_ops_type = struct
  (** As Isabelle def. See \doc(doc:leaf_ops). *)
  type ('k,'v,'leaf) leaf_ops = {
    leaf_lookup: 'k -> 'leaf -> 'v option;
    leaf_insert: 'k -> 'v -> 'leaf -> 'leaf * 'v option;
    leaf_remove: 'k -> 'leaf -> 'leaf;
    leaf_length: 'leaf -> int;
    leaf_steal_right: 'leaf * 'leaf -> 'leaf * 'k * 'leaf;
    leaf_steal_left: 'leaf*'leaf -> 'leaf*'k*'leaf;
    leaf_merge: 'leaf * 'leaf -> 'leaf;
    split_large_leaf: int -> 'leaf -> 'leaf*'k*'leaf;
    leaf_to_kvs: 'leaf -> ('k*'v) list;
    kvs_to_leaf: ('k*'v) list -> 'leaf;
    (* dbg_leaf_kvs: 'leaf -> ('k*'v) list; *)
    (* dbg_leaf: 'leaf -> unit; *)
  }
end
include Leaf_ops_type

module Node_ops_type = struct
  (* As Isabelle defn. See \doc(doc:node_ops) *)
  type ('k,'r,'node) node_ops = {
    split_node_at_k_index: int -> 'node -> ('node*'k*'node);
    node_merge: 'node*'k*'node -> 'node;
    node_steal_right: 'node*'k*'node -> 'node*'k*'node;
    node_steal_left: 'node*'k*'node -> 'node*'k*'node;
    node_keys_length: 'node -> int;
    node_make_small_root: 'r*'k*'r -> 'node;
    node_get_single_r: 'node -> 'r;
    node_to_krs: 'node -> ('k list * 'r list);
    krs_to_node: ('k list * 'r list) -> 'node;
    (* dbg_node_krs: 'node -> ('k list * 'r list); *)
    (* dbg_node: 'node -> unit *)
  }
end
include Node_ops_type


module Frame_ops_type = struct
  module Internal_bottom_or_top = struct
    type 'k or_top = 'k option

    type 'k or_bottom = 'k option
  end
  open Internal_bottom_or_top

  type ('k,'r) segment = 'k or_bottom * 'r * ('k*'r) list * 'k or_top

  (** See Isabelle defn. See \doc(doc:frame_ops) *)
  type ('k,'r,'frame,'node) frame_ops = {
    split_node_on_key: 'r -> 'k -> 'node -> 'frame;
    midpoint: 'frame -> 'r;

    get_focus: 'frame -> ('k or_bottom * 'r * 'k or_top);
    get_focus_and_right_sibling: 'frame -> ('k or_bottom * 'r * 'k * 'r * 'k or_top) option;
    get_left_sibling_and_focus: 'frame -> ('k or_bottom * 'r * 'k * 'r * 'k or_top) option;
    replace: ('k,'r) segment -> ('k,'r) segment -> 'frame -> 'frame;
    frame_to_node: 'frame -> 'node;

    get_midpoint_bounds: 'frame -> ('k option * 'k option);
    backing_node_blk_ref: 'frame -> 'r;

    split_node_for_leaf_stream: 'r -> 'node -> 'frame;
    step_frame_for_leaf_stream: 'frame -> 'frame option;

    dbg_frame: 'frame -> unit;
  }
end
include Frame_ops_type

(** {2 Store operations} *)

module Store_ops_type = struct
  type ('r,'dnode,'t) store_ops = {
    read: 'r -> ('dnode,'t) m;
    wrte: 'dnode -> ('r,'t) m;
    rewrite: 'r -> 'dnode -> ('r option, 't) m;
    free: 'r list -> (unit,'t) m
  }
end
include Store_ops_type


(** {2 Pre-map operations} *)

module Pre_map_ops_type = struct
  (** Pre-map ops, with an explicit root pointer *)
  type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
    leaf_lookup: 'k -> 'leaf -> 'v option;
    find: r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
    insert: r:'r -> k:'k -> v:'v -> ('r option,'t) m;
    delete: r:'r -> k:'k -> ('r,'t) m;
  }
end
include Pre_map_ops_type



(** {2 Leaf stream operations} *)

module Leaf_stream_ops_type = struct
  (** The type of operations on leaf streams. Note that [ls_leaf]
      always returns a leaf. So each step transitions from one leaf to
      the next. *)
  type ('k,'v,'r,'leaf_stream_state,'t) leaf_stream_ops = {
    make_leaf_stream: 'r -> ('leaf_stream_state,'t) m;
    ls_step: 'leaf_stream_state -> ('leaf_stream_state option,'t) m;
    ls_kvs: 'leaf_stream_state -> ('k*'v)list;
  }
end
include Leaf_stream_ops_type
    (* ls_leaf: 'leaf_stream_state -> 'leaf; *)




module type Ctxt0 = sig

  type t
  val monad_ops: t monad_ops
      
  (* val cs: Constants.constants *)

  type k
  type v
  type r
  val k_cmp: k -> k -> int
end


module type Ctxt_with_node_leaf_frame_impls = sig

  include Ctxt0

  type node_impl
  type leaf_impl
  type frame_impl
  type dnode_impl = (node_impl,leaf_impl)dnode

  val node_ops: (k,r,node_impl) node_ops
  val leaf_ops: (k,v,leaf_impl) leaf_ops
  val frame_ops: (k,r,frame_impl,node_impl) frame_ops
end
