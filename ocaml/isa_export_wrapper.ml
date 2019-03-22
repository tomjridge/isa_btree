open Tjr_monad.Types
open Constants_type
open Isa_export

type ('node,'leaf) dnode = ('node,'leaf) Disk_node.dnode

type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
 find: r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
 insert: r:'r -> k:'k -> v:'v -> ('r option,'t) m;
 delete: r:'r -> k:'k -> ('r,'t) m;
}

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
  let n2isa n = Arith.nat_of_integer (Big_int.big_int_of_int n) in
  let i2isa i = Arith.Int_of_integer(Big_int.big_int_of_int i) in
  let cs2isa (cs:constants) = 
    Constants_and_size_types.make_constants 
      (n2isa cs.min_leaf_size) 
      (n2isa cs.max_leaf_size)
      (n2isa cs.min_node_keys)
      (n2isa cs.max_node_keys)
  in
  let cmp2isa (f: 'k -> 'k -> int) = fun k1 k2 -> f k1 k2 |> i2isa in
  let leaf_ops2isa (leaf_lookup,leaf_insert,leaf_remove,leaf_length,dbg_leaf_kvs,leaf_steal_right,leaf_steal_left,leaf_merge,split_large_leaf) = 
    let leaf_length l = leaf_length l |> n2isa in
    Isa_export.Disk_node.Make_leaf_ops(leaf_lookup,leaf_insert,leaf_remove,leaf_length,dbg_leaf_kvs,leaf_steal_right,leaf_steal_left,leaf_merge,split_large_leaf)
  in
  let node_ops2isa (split_large_node,node_merge,node_steal_right,node_steal_left,node_keys_length,node_make_small_root,node_get_single_r) = 
    Isa_export.Disk_node.Make_node_ops (split_large_node,node_merge,node_steal_right,node_steal_left,node_keys_length,node_make_small_root,node_get_single_r)
  in
  let frame_ops2isa (leaf_half,right_half,midpoint,rh_dest_cons,lh_dest_snoc,unsplit,get_midpoint_bounds,split_node_on_key,original_node_r,split_node_on_first_key,step_frame_for_ls) = 
    Isa_export.Stacks_and_frames.Make_frame_ops(leaf_half,right_half,midpoint,rh_dest_cons,lh_dest_snoc,unsplit,get_midpoint_bounds,split_node_on_key,original_node_r,split_node_on_first_key,step_frame_for_ls)
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
