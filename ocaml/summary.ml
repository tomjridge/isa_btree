(** Summary of the main interfaces *)

(**

{[
(** Argument to Make functor *)
module type S = sig 
  type k
  type v
  type r
  type t
  val k_cmp     : k -> k -> int
  val monad_ops : t monad_ops
  val cs        : constants
end


(** Result of Make functor *)
module type T = sig
  module S : S
  open S

  type leaf 
  type node
  type leaf_stream

  (** NOTE leaf_ops and node_ops are used externally to convert
     to/from lists *)
  val leaf_ops: (k,v,leaf)leaf_ops
  val node_ops: (k,r,node)node_ops

  val make_btree_ops: 
    store_ops:(r, (node, leaf) dnode, t) store_ops ->
    (k, v, r, t, leaf, node, leaf_stream) pre_btree_ops
end


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


  (** Pre-map ops, with root passing, exposing leaf and frame *)
  type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
    leaf_lookup : 'k -> 'leaf -> 'v option;
    find        : r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
    insert      : r:'r -> k:'k -> v:'v -> ('r option,'t) m;
    delete      : r:'r -> k:'k -> ('r,'t) m;
  }


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

]}

*)
