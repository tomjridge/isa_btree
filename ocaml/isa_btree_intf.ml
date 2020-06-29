(** Jane Street-style interface file *)

(* NOTE defn. in Isabelle *)
(* type ('k,'r,'node) node_ops' = ('k,'r,'node) Disk_node.node_ops *)

type ('a,'b) ty_eq = ('a,'b) Base.Type_equal.t

module Dnode_type = struct
  (** Recall [dnode] type *)
  type ('node,'leaf) dnode = ('node,'leaf) Isa_export.Disk_node.dnode = 
      Disk_node of 'node | Disk_leaf of 'leaf
end
include Dnode_type


(** {2 Node, leaf and frame types} *)

(** It is useful to be able to talk about these types outside the functor application. *)


(** {2 Frames} *)

(* this is really an implementation type *)
module Frame_type = struct
  type ('k,'r,'node) frame = {
    midkey: 'k option;  (* really or_bottom; may be None *)
    midpoint: 'r;
    node: 'node;
    backing_node_blk_ref: 'r
  } [@@deriving to_yojson]
end
(* open Frame_type  (\* lots of other frames lying around, so just open here *\) *)
type ('k,'r,'node) frame = ('k,'r,'node) Frame_type.frame

module Internal_leaf_node : sig
  type ('k,'r,'cmp) node
  val node_ty_eq: (('k,'r,'cmp) node,('k option, 'r, 'cmp) Base.Map.t) ty_eq

  type ('k,'v,'cmp) leaf
  val leaf_ty_eq: (('k,'v,'cmp) leaf,('k, 'v, 'cmp) Base.Map.t) ty_eq
                    
  (* type ('k,'r,'cmp) frame  *)
  (* val frame_ty_eq : (('k,'r,'cmp) frame,('k, 'r, ('k,'r,'cmp) node) Frame_type.frame) ty_eq *)
end
= struct
  type ('k,'r,'cmp) node = ('k option, 'r, 'cmp) Base.Map.t
  let node_ty_eq = Base.Type_equal.refl
  
  type ('k,'v,'cmp) leaf = ('k, 'v, 'cmp) Base.Map.t
  let leaf_ty_eq = Base.Type_equal.refl

  (* type ('k,'r,'cmp) frame = ('k, 'r, ('k,'r,'cmp) node) Frame_type.frame *)
  (* let frame_ty_eq = Base.Type_equal.refl *)
end

module Abstract_leaf_node_frame_types = struct
  open Internal_leaf_node
  type nonrec ('k,'r,'cmp) node = ('k,'r,'cmp) node
  type nonrec ('k,'v,'cmp) leaf = ('k,'v,'cmp) leaf
  (* type nonrec ('k,'r,'cmp) frame = ('k,'r,'cmp) frame  *)
end
include Abstract_leaf_node_frame_types

module Internal_leaf_stream_impl_t = struct
  (** We augment the basic Isabelle type with some extra information:
     the current leaf. This type is for debugging - you shouldn't need
     to access components. *)
  type ('r,'leaf,'frame) _t = { 
    leaf: 'leaf;
    isa_ls_state: ('r,'leaf,'frame)Isa_export.Leaf_stream_state.leaf_stream_state 
  }
end

module Abstract_leaf_stream : sig
  type ('k,'v,'r,'cmp) leaf_stream
end = struct
  type ('k,'v,'r,'cmp) leaf_stream = 
    ('r, ('k,'v,'cmp)leaf, ('k,'r,'cmp) Frame_type.frame) Internal_leaf_stream_impl_t._t 
end


module Leaf_ops_type = struct

  (** As Isabelle def. See \doc(doc:leaf_ops). Note: the empty leaf
     can be obtained by calling kvs_to_leaf on the empty list. *)
  type ('k,'v,'leaf) leaf_ops = {
    leaf_lookup      : 'k -> 'leaf -> 'v option;
    leaf_insert      : 'k -> 'v -> 'leaf -> 'leaf * 'v option;
    leaf_remove      : 'k -> 'leaf -> 'leaf;
    leaf_length      : 'leaf -> int;
    leaf_steal_right : 'leaf * 'leaf -> 'leaf * 'k * 'leaf;
    leaf_steal_left  : 'leaf*'leaf -> 'leaf*'k*'leaf;
    leaf_merge       : 'leaf * 'leaf -> 'leaf;
    split_large_leaf : int -> 'leaf -> 'leaf*'k*'leaf;
    leaf_to_kvs      : 'leaf -> ('k*'v) list;
    kvs_to_leaf      : ('k*'v) list -> 'leaf;
    (* empty_leaf: 'leaf;  *)
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

(** For packaging *)
type ('a,'b,'c) leaf_node_frame_ops = {
  leaf_ops:'a;
  node_ops:'b;
  frame_ops:'c;
}

(** {2 Store operations} *)

module Store_ops = struct

  (* $(PIPE2SH("""sed -n '/store_ops[ ]are like/,/}/p' >GEN.store_ops.ml_""")) *)
  (** store_ops are like a blk device, but allowing read/writes of
     leafs and nodes rather than blks (so, marshalling is done in a
     lower layer)

      NOTE rewrite attempts to rewrite a block; this may not be
     allowed (CoW) and instead a new block is allocated and written

      NOTE also that 'dnode is either leaf or node *)
  type ('r,'dnode,'t) store_ops = {
    read    : 'r -> ('dnode,'t) m;
    wrte    : 'dnode -> ('r,'t) m;
    rewrite : 'r -> 'dnode -> ('r option, 't) m;
    free    : 'r list -> (unit,'t) m
  }

  type ('r,'dnode,'t) t = ('r,'dnode,'t) store_ops
  (* $(FIXME("free store_ops.free needs thinking about")) *)
end
include Store_ops


(** {2 Pre-map operations} *)

module Pre_map_ops_type = struct

  (* $(PIPE2SH("""sed -n '/Pre-map[ ]ops/,/}/p' >GEN.pre_map_ops.ml_""")) *)
  (** Pre-map ops, with root passing, exposing leaf and frame *)
  type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
    leaf_lookup : 'k -> 'leaf -> 'v option;
    find        : r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
    insert      : r:'r -> k:'k -> v:'v -> ('r option,'t) m;
    delete      : r:'r -> k:'k -> ('r,'t) m;
  }
end
include Pre_map_ops_type



(** {2 Leaf stream operations} *)

module Leaf_stream_ops_type = struct

  (* $(PIPE2SH("""sed -n '/Leaf-stream[ ]ops/,/}/p' >GEN.leaf_stream_ops.ml_""")) *)
  (** Leaf-stream ops. Note that [ls_leaf] always returns a leaf i.e.
     each step transitions from one leaf to the next. FIXME not
     concurrent safe- may need CoW or detailed analysis of concurrent
     mutations on B-tree or at worst blocking of conc mutation or ls
     failure *)
  type ('k,'v,'r,'ls_state,'t) leaf_stream_ops = {
    make_leaf_stream : 'r -> ('ls_state,'t) m;
    ls_step          : 'ls_state -> ('ls_state option,'t) m;
    ls_kvs           : 'ls_state -> ('k*'v)list;
  }
end
include Leaf_stream_ops_type
    (* ls_leaf: 'ls_state -> 'leaf; *)


(** {2 Insert many} 

The semantics of this operation is: for a list of (k,v), the operation
inserts some kvs, and returns the rest.

*) 

module Insert_many_type = struct
  (* separate type to make somewhat readable *)
  type ('k,'v,'r,'t) insert_many_type = {
    insert_many: r:'r -> k:'k -> v:'v -> kvs:('k*'v)list -> (('k*'v)list*'r option, 't)m
  }
end
include Insert_many_type


(** {2 Insert all}

The semantics of this operation is: for a list of (k,v), the operation
   inserts all kvs, and returns the updated root (or the original root
   if tree was updated in place).  *)

module Insert_all_type = struct
  type ('k,'v,'r,'t) insert_all_type = {
    insert_all: r:'r -> kvs:('k*'v)list -> ('r,'t) m
  }
end
include Insert_all_type



(** {2 B-tree (pre-) ops} *)

(** A record of operations provided by the B-tree *)
module Pre_btree_ops_type = struct

  (* $(ABBREV("ls = leaf_stream")) *)
  (* $(PIPE2SH("""sed -n '/type[ ].*pre_btree_ops/,/}/p' >GEN.pre_btree_ops.ml_""")) *)
  type ('k,'v,'r,'t,'leaf,'node,'ls) pre_btree_ops = {
    find   : r:'r -> k:'k -> ('r * 'leaf * ('k, 'r, 'node) frame list, 't) m;
    insert : r:'r -> k:'k -> v:'v -> ('r option, 't) m;
    delete : r:'r -> k:'k -> ('r, 't) m;

    leaf_stream_ops : ('k, 'v, 'r, 'ls, 't) leaf_stream_ops;
    leaf_ops        : ('k,'v,'leaf) leaf_ops;
    node_ops        : ('k,'r,'node) node_ops;

    (* FIXME pre_map_ops seems to reproduce find, ... *)
    pre_map_ops     : ('k, 'v, 'r, 'leaf, ('k, 'r, 'node) frame, 't) pre_map_ops;

    insert_many     : ('k, 'v, 'r, 't) insert_many_type;
    insert_all      : ('k, 'v, 'r, 't) insert_all_type
  }


  (* leaf_lookup : 'k -> 'leaf -> 'v option; *)
end
include Pre_btree_ops_type


module Leaf_node_frame_map_ops_type = struct
  (** To avoid dependency on any particular map implementation, we
      define the exact interface we require here. *)
  type ('k,'v,'t) map_ops = ('k,'v,'t) Tjr_map.With_base_as_record.map_ops
end
(* don't include to avoid too many map types in scope *)


type ('s,'t) type_conversions = {
  s_to_t: 's -> 't;
  t_to_s: 't -> 's;
}



