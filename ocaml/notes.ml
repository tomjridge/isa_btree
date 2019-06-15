(** Some notes on constructing the B-tree *)

(** In order to construct B-trees dynamically, without first-order
   modules, we have used an approach based on parametric records of
   operations. However, this gets unwieldy (too many type
   parameters!). Here we look at an approach based on first-order
   modules. The downside is that we need quite a few type sharing
   annotations to get things to work. *)

open Isa_btree_intf

(** The basic types, and background monad_ops and cs and k_cmp. *)
module type Sa = sig
  type k
  type v
  type r
  type t
end

module type Sb = sig
  include Sa

  (** NOTE this gives rise to types for the (k,_,_) map and (k
     option,_,_) map *)
  val k_cmp     : k -> k -> int
  val monad_ops : t monad_ops
  val cs        : Constants.constants
end

(* using comparators; this allows the implementation types in Sz to be
   non-generative *)
module type Sc = sig
  include Sa

  type k_comparator
  type kopt_comparator
  val k_cmp     : (k,k_comparator)Base.Map.comparator
  val kopt_cmp  : (k option,kopt_comparator)Base.Map.comparator

  val monad_ops : t monad_ops
  val cs        : Constants.constants
end



module type Ta = sig
  include Sa

  (* We can expose the implementation of these types, but that depends
     on the generated comparator types (hence modtype Sc) *)
  type leaf
  type node

  val leaf_ops: (k,v,leaf)leaf_ops
  val node_ops: (k,r,node)node_ops

  type leaf_stream

  (** NOTE that there is really a type dependency on constants, since
     we can't just mix two implementations with different
     constants.

      NOTE also that we unfortunately expose the existence of leaf and node
 *)
  val pre_btree_ops: 
    (r,(node,leaf)dnode,t) store_ops -> 
    (k,v,r,t,leaf,node,leaf_stream)pre_btree_ops
end



(** The advantage of this impl is that we avoid type generativity; of
   course, that means we are free to mess up different map types. *)
module type Tb = sig
  include Sa
  include Ta with 
    type leaf=(k,v,unit)Tjr_map.map and 
  type node=(k option,r,unit)Tjr_map.map and 
  type k:=k and type v:=v and type r:=r and type t:=t
end

(** This fixes the implementation of leaf and node as Base.Map.t. Fine
   for testing, but we probably prefer Ta for development since we
   don't want to assume impls of leaf and node. Alternatively, take a
   pre_btree_ops and work with that. *)
module type Tc = sig 
  include Sc

  include Ta with 
    type leaf=(k,v,k_comparator)Base.Map.t and 
  type node=(k option,r,kopt_comparator)Base.Map.t and 
  type k:=k and type v:=v and type r:=r and type t:=t
end

module type Tc' = sig include Tc end
