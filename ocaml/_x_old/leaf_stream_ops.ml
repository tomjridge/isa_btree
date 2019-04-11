(** A leaf stream is a linear sequence of the leaves in a B-tree, used
    for iterating over all the bindings in the tree. Leaf stream
    operations: make a leaf stream; get the list of (key,value) pairs
    associated to "current" leaf; step to the next leaf. *)

open Tjr_monad.Types

(* leaf stream ------------------------------------------------------ *)

(* we only reveal lss when it points to a leaf *)

module Leaf_stream_types = struct
  (** Leaf stream representation. This type is for debugging - you
      shouldn't need to access components. *)
  type ('r,'leaf,'frame) _leaf_stream_state = { 
    leaf: 'leaf;
    ls: ('r,'leaf,'frame)Isa_export.Leaf_stream_state.leaf_stream_state 
  }


  (* FIXME mk_leaf_stream should surely start with a page ref? *)
  (* type ('k,'v,'r) lss = ('k,'v,'r) leaf_stream_state *)

  type (v,'r,'leaf_stream,'t) leaf_stream_ops = {
    mk_leaf_stream: 'r -> ('leaf_stream,'t) m;
    ls_step: 'leaf_stream -> ('leaf_stream option,'t) m;
    ls_leaf: 'leaf_stream -> 'leaf;
  }
    
end
include Leaf_stream_types


let wf_ls_ops 
    ~(mk_leaf_stream: 'r -> (('k,'v,'r) lss,'t) m)
    ~(ls_step: ('k,'v,'r) lss -> (('k,'v,'r) lss option,'t) m)
    ~(ls_kvs: ('k,'v,'r) lss -> ('k*'v) list)
  =
  true[@@ocaml.warning "-27"]

let mk_ls_ops ~mk_leaf_stream ~ls_step ~ls_kvs =
  assert(wf_ls_ops ~mk_leaf_stream ~ls_step ~ls_kvs);
  { mk_leaf_stream; ls_step; ls_kvs }

let _ = mk_ls_ops

let dest_ls_ops { mk_leaf_stream;ls_step; ls_kvs} = 
  assert(wf_ls_ops ~mk_leaf_stream ~ls_step ~ls_kvs);
  fun k -> k ~mk_leaf_stream ~ls_step ~ls_kvs

