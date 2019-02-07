open Tjr_monad.Types
open Constants_type
open Isa_export

type ('k,'v,'r) dnode = ('k,'v,'r,unit) Disk_node.dnode

type ('k,'r) stk = ('r list * 'k list, 'r, 'k list * 'r list, 'r) Stacks_and_frames.stk_frame list

type ('k,'v,'r,'leaf,'t) pre_map_ops = {
 find: r:'r -> k:'k -> ('r * 'leaf * ('k,'r)stk,'t) m;
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
  let leaf_ops2isa (leaf_insert,leaf_length,leaf_kvs,mk_leaf) =
    let leaf_length l = leaf_length l |> n2isa in
    Isa_export.Disk_node.Make_leaf_ops(leaf_insert,leaf_length,leaf_kvs,mk_leaf)
  in
  let store_ops2isa store_ops = 
    let (a,b,c,d) = store_ops in
    M.Post_monad.make_store_ops a b c d
  in
  fun ~cs ~k_cmp
    ~leaf_ops
    ~store_ops -> 
    let _ = leaf_ops in
    let find  = 
      let find = M.Find.find (cs2isa cs) (cmp2isa k_cmp) (leaf_ops2isa leaf_ops) (store_ops2isa store_ops) in
      fun ~(r:'r) ~(k:'k) -> find r k |> Monad.fmap (fun (a,(b,c)) -> (a,b,c))
    in
    let insert = 
      let insert = M.Insert.insert (cs2isa cs) (cmp2isa k_cmp) (leaf_ops2isa leaf_ops) (store_ops2isa store_ops) in
      fun  ~(r:'r) ~(k:'k) ~(v:'v) -> insert r k v
    in
    let delete  =
      let delete = M.Delete.delete (cs2isa cs) (cmp2isa k_cmp) (leaf_ops2isa leaf_ops) (store_ops2isa store_ops) in
      fun ~(r:'r) ~(k:'k) -> delete r k
    in
    {find;insert;delete}

let _ = make_find_insert_delete
