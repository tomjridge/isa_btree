open Tjr_monad.Types
open Constants_type
open Isa_export

type ('node,'leaf) dnode = ('node,'leaf) Disk_node.dnode

type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
 find: r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
 insert: r:'r -> k:'k -> v:'v -> ('r option,'t) m;
 delete: r:'r -> k:'k -> ('r,'t) m;
}


(* node ops --------------------------------------------------------- *)

(* NOTE *)
type ('k,'r,'node) node_ops' = ('k,'r,'node) Disk_node.node_ops

(* record version to parallel isabelle's datatype version *)
type ('k,'r,'node) node_ops = {
  split_node_at_k_index: int -> 'node -> ('node*'k*'node);
  node_merge: 'node*'k*'node -> 'node;
  node_steal_right: 'node*'k*'node -> 'node*'k*'node;
  node_steal_left: 'node*'k*'node -> 'node*'k*'node;
  node_keys_length: 'node -> int;
  node_make_small_root: 'r*'k*'r -> 'node;
  node_get_single_r: 'node -> 'r;
}

open Tjr_fs_shared

type ('k,'r,'t) keyspace_ops = ('k,'r,'t) Tjr_lin_partition.keyspace_ops

(* FIXME is keyspace just a node? no, node is more restricted, and frame is something else *)

let make_node_ops ~k_cmp =
  let kspace = Tjr_lin_partition.make_keyspace_ops ~k_cmp in
  let split_node_at_k_index : int -> 'node -> 'node*'k*'node = fun i n -> 
    kspace.split_keyspace_at_index i n
  in
  let node_merge : 'node*'k*'node -> 'node = fun (n1,k,n2) ->
    kspace.merge_keyspaces (n1,k,n2)
  in
  let node_steal_right : 'node*'k*'node -> 'node*'k*'node = fun (n1,k1,n2) ->
    let (r,k2,n2) = kspace.ks_dest_cons n2 in
    let n1 = kspace.ks_internal_add (Some k1) r n1 in
    (n1,k2,n2) 
  in
  let node_steal_left : 'node*'k*'node -> 'node*'k*'node = fun (n1,k1,n2) ->
    let (n1,k2,r1) = kspace.ks_dest_snoc n1 in
    let n2 = 
      let (_,r2) = kspace.find_intv_and_binding_for_key None n2 in
      n2 
      |> kspace.ks_internal_add (Some k1) r2 
      |> kspace.ks_internal_add None r1
    in
    (n1,k2,n2)
  in
  let node_keys_length n = kspace.k_size n in
  let node_make_small_root (r1,k,r2) = 
    kspace.ks_internal_empty 
    |> kspace.ks_internal_add None r1
    |> kspace.ks_internal_add (Some k) r2
  in
  let node_get_single_r n =
    n |> kspace.ks2krs |> fun (ks,rs) ->
    assert(List.length rs = 1);
    List.hd rs
  in
  {split_node_at_k_index; node_merge; node_steal_right; node_steal_left; node_keys_length; node_make_small_root; node_get_single_r}
;;

(*
FIXME got here; need to implement node_ops and frame_ops 

node_ops is just tjr_fs_shared/tjr_lin_partition
frame_ops builds on this

then make_find_insert_delete should take a k_cmp and construct all the leaf and node and ops

also need to add batch operations
*)

let make_find_insert_delete (type t) ~(monad_ops:t monad_ops) = 
  let module Monad = struct
    type nonrec t = t
    type ('a,'t) mm = ('a,t) Tjr_monad.Types.m 
    let bind ab a = monad_ops.bind a ab
    let return a = monad_ops.return a
    let fmap f a = a |> bind (fun a -> return (f a))
  end
  in
  let module M = Isa_export.Make(Monad) in
  let int2nat n = Arith.nat_of_integer (Big_int.big_int_of_int n) in
  let nat2int (n:Arith.nat) = Arith.int_of_nat n in
  let int2isa i = Arith.Int_of_integer(Big_int.big_int_of_int i) in
  let cs2isa (cs:constants) = 
    Constants_and_size_types.make_constants 
      (int2nat cs.min_leaf_size) 
      (int2nat cs.max_leaf_size)
      (int2nat cs.min_node_keys)
      (int2nat cs.max_node_keys)
  in
  let cmp2isa (f: 'k -> 'k -> int) = fun k1 k2 -> f k1 k2 |> int2isa in
  let leaf_ops2isa (leaf_lookup,leaf_insert,leaf_remove,leaf_length,dbg_leaf_kvs,leaf_steal_right,leaf_steal_left,leaf_merge,split_large_leaf) = 
    let leaf_length l = leaf_length l |> int2nat in
    Isa_export.Disk_node.Make_leaf_ops(leaf_lookup,leaf_insert,leaf_remove,leaf_length,dbg_leaf_kvs,leaf_steal_right,leaf_steal_left,leaf_merge,split_large_leaf)
  in
  let node_ops2isa node_ops = 
    let split_large_node i n = node_ops.split_large_node (
    Isa_export.Disk_node.Make_node_ops (split_large_node,node_merge,node_steal_right,node_steal_left,node_keys_length,node_make_small_root,node_get_single_r)
  in
  let frame_ops2isa (left_half,right_half,midpoint,rh_dest_cons,lh_dest_snoc,unsplit,get_midpoint_bounds,split_node_on_key,original_node_r,split_node_on_first_key,step_frame_for_ls) = 
    Isa_export.Stacks_and_frames.Make_frame_ops(left_half,right_half,midpoint,rh_dest_cons,lh_dest_snoc,unsplit,get_midpoint_bounds,split_node_on_key,original_node_r,split_node_on_first_key,step_frame_for_ls)
  in
  let store_ops2isa store_ops = 
    let (a,b,c,d) = store_ops in
    M.Post_monad.make_store_ops a b c d
  in
  fun ~cs ~k_cmp
    ~leaf_ops
    ~node_ops
    ~frame_ops
    ~store_ops
    ~check_tree_at_r'
    -> 
    let _ = leaf_ops in
    let find  = 
      let find = M.Find.find (frame_ops2isa frame_ops) (store_ops2isa store_ops) in
      fun ~(r:'r) ~(k:'k) -> find r k |> Monad.fmap (fun (a,(b,c)) -> (a,b,c))
    in
    let insert = 
      let insert = M.Insert.insert (cs2isa cs) (leaf_ops2isa leaf_ops) (node_ops2isa node_ops) (frame_ops2isa frame_ops) (store_ops2isa store_ops) check_tree_at_r' in
      fun  ~(r:'r) ~(k:'k) ~(v:'v) -> insert r k v
    in
    let delete  =
      let delete = M.Delete.delete (cs2isa cs) (leaf_ops2isa leaf_ops)  (node_ops2isa node_ops) (frame_ops2isa frame_ops) (store_ops2isa store_ops) check_tree_at_r' in
      fun ~(r:'r) ~(k:'k) -> delete r k
    in
    {find;insert;delete}

let _ = make_find_insert_delete
