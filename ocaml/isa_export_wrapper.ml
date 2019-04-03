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

(* NOTE defn. in Isabelle *)
type ('k,'r,'node) node_ops' = ('k,'r,'node) Disk_node.node_ops

(* As Isabelle defn. See \doc(doc:node_ops) *)
type ('k,'r,'node) node_ops = {
  split_node_at_k_index: int -> 'node -> ('node*'k*'node);
  node_merge: 'node*'k*'node -> 'node;
  node_steal_right: 'node*'k*'node -> 'node*'k*'node;
  node_steal_left: 'node*'k*'node -> 'node*'k*'node;
  node_keys_length: 'node -> int;
  node_make_small_root: 'r*'k*'r -> 'node;
  node_get_single_r: 'node -> 'r;
}

(*  node_dest_cons: 'node -> 'r * 'k * 'node;  (* NOTE only for a node *)
  node_dest_snoc: 'node -> 'node * 'k * 'r;  (* NOTE only for a node *) *)

open Tjr_fs_shared

(* implement node ops using a map from option; see impl notes in \doc(doc:node_ops) *)

(* None is less than any other lower bound; this corresponds to the
   "lowest" interval below k0 *)
let rec key_compare k_cmp k1 k2 =
  match k1,k2 with 
  | None,None -> 0
  | None,_ -> -1
  | _,None -> 1
  | Some k1, Some k2 -> k_cmp k1 k2

let dest_Some x = match x with Some x -> x | _ -> failwith "dest_Some"

let make_node_ops (type k r) ~k_cmp = 
  let map_ops = Tjr_poly_map.make_map_ops (key_compare k_cmp) in
  let make_node ks rs = 
    assert(List.length rs = 1 + List.length ks);
    let ks = None::(List.map (fun x -> Some x) ks) in
    let krs = List.combine ks rs in
    map_ops.of_bindings krs
  in
  let _ = make_node in
  let split_node_at_k_index i n =   (* i counts from 0 *)
    map_ops.bindings n |> fun krs -> 
    let ks,rs = List.split krs in
    let ks = List.tl ks |> List.map dest_Some in  (* drop None *)
    let k = List.nth ks i in
    let r = map_ops.find_opt (Some k) n |> dest_Some in
    let (n1,_,n2) = map_ops.split (Some k) n in
    n2 |> map_ops.add None r |> fun n2 ->
    (n1,k,n2)
  in
  let node_merge (n1,k,n2) = 
    n2 |> map_ops.find_opt None |> dest_Some |> fun r2 -> 
    n2 |> map_ops.remove None |> map_ops.add (Some k) r2 |> fun n2 ->
    map_ops.disjoint_union n1 n2
  in
  let node_steal_right (n1,k,n2) =
    n2 |> map_ops.find_opt None |> dest_Some |> fun r2 ->
    n2 |> map_ops.remove None |> fun n2 ->
    n1 |> map_ops.add (Some k) r2 |> fun n1 ->
    n2 |> map_ops.min_binding_opt |> dest_Some |> fun (k,_) ->
    k |> dest_Some |> fun k ->
    (n1,k,n2)
  in
  let node_steal_left (n1,k,n2) = 
    n1 |> map_ops.max_binding_opt |> dest_Some |> fun (k,r) ->
    k |> dest_Some |> fun k ->
    n1 |> map_ops.remove (Some k) |> fun n1 ->
    n2 |> map_ops.add (Some k) r |> fun n2 ->
    (n1,k,n2)
  in
  let node_keys_length n = 
    (map_ops.cardinal n) -1
  in
  let node_make_small_root (r1,k,r2) =
    map_ops.empty |> map_ops.add None r1 |> map_ops.add (Some k) r2
  in
  let node_get_single_r n =
    assert(map_ops.cardinal n = 1);
    map_ops.bindings n |> fun [(_,r)] -> r
  in
  let _ = node_steal_right in
  { split_node_at_k_index; node_merge; node_steal_right; node_steal_left; node_keys_length;
    node_make_small_root; node_get_single_r }
    

(* frame_ops -------------------------------------------------------- *)

(* \doc(doc:frame_ops) *)
type ('k,'r,'frame,'left_half,'right_half,'node) frame_ops = {
  split_node_on_key: 'r -> 'node -> 'k -> 'frame;
  left_half: 'frame -> 'left_half;
  right_half: 'frame -> 'right_half;
  midpoint: 'frame -> 'r;
  rh_dest_cons: 'right_half -> ('k*'r*'right_half) option;
  lh_dest_snoc: 'left_half -> ('left_half*'r*'k) option;
  unsplit: 'left_half*('k,'r)Isa_export.Stacks_and_frames.rkr_or_r * 'right_half -> 'node;
  get_midpoint_bounds: 'frame -> ('k option * 'k option);
  backing_node_blk_ref: 'frame -> 'r
}

(* FIXME maybe move elsewhere *)


type ('k,'node) left_half = 'node * 'k option

type ('k,'r) frame = {
  lh: ('k,'r) node;  (* may be empty *)
  (* midkey: see Stacks_and_frames.thy *)
  midkey: 'k option;  (* may be None *)
  midpoint: 'r;
  rh: ('k,'r) node;  (* may be empty *)
  backing_node_blk_ref: 'r
}

let mu_opt = function
  | None -> None
  | Some None -> None
  | Some x -> Some x

(* ~ks_dest_cons ~ks_dest_snoc *)
let make_frame_ops (type k r ) 
    ~map_ops
    ~keyspace_ops
    ~(node_ops:(k,r,(k,r)node)node_ops) 
  = 
  let open Tjr_lin_partition in
  let split_node_on_key n k : (k, r) node * k option * r * (k, r) node = 
    keyspace_ops.split_keyspace_on_key k n
  in  
  let split_node_on_key backing_node_blk_ref n k = 
    split_node_on_key n k |> fun (lh,k,r,rh) -> 
    { lh; rh; midkey=k; midpoint=r; backing_node_blk_ref}
  in
  (* left half is a pair of a total keyspace, and a bounding key *)
  let left_half f = (`Lh,f.lh,f.midkey) in
  let right_half f = (`Rh,f.rh) in
  let midpoint f = f.midpoint in
  let rh_dest_cons (_,rh) =     
    map_ops.Tjr_poly_map.min_binding_opt rh |> function
    | None -> None  (* rh is empty *)
    | Some(None,_) -> failwith ("impossible "^__LOC__)
    | Some(Some k,r) -> 
      rh |> map_ops.remove (Some k) |> fun rh ->
      Some(k,r,rh)
  in
  let lh_dest_snoc (_,lh,k) = 
    (* again, we may be in the situation that there is only a None
       binding in lh, so we can't dest_snoc; or lh may be empty *)
    match map_ops.max_binding_opt lh with
    | None -> None
    | Some(None,_) -> (
        assert false
        (* This case should not happen if we steal from a node which has at least 1 key *)
      )
    | Some (Some kn,rn) -> 
      (* remove kn binding from lh *)
      let lh = map_ops.remove (Some kn) lh in
      (* we must take care of the extra key *)
      let lh = (lh,kn) in
      Some(lh,rn,k)
  in
  let unsplit (lh,rkr,rh) = 
    (* \doc(doc:frame_ops) *)
    let (lh,k1) = lh in
    match rkr with 
    | Isa_export.Stacks_and_frames.R r -> (
        rh |> map_ops.add None r |> fun rh -> 
        keyspace_ops.merge_keyspaces (lh,k1,rh))
    | Rkr (r1,(k2,r2)) -> (
        rh 
        |> map_ops.add (Some k2) r2 
        |> map_ops.add None r1 
        |> fun rh -> 
        keyspace_ops.merge_keyspaces (lh,k1,rh))
  in
  let get_midpoint_bounds f = 
    let l = f.midkey in
    let u = 
      match map_ops.min_binding_opt f.rh with
      | None -> None
      | Some(None,_) -> assert false  (* possible? *)
      | Some(Some u,_) -> u
    in
    (l,u)
  in
  let backing_node_blk_ref f = f.backing_node_blk_ref in
  let _ = split_node_on_key, left_half, right_half, midpoint, rh_dest_cons, lh_dest_snoc, unsplit, get_midpoint_bounds in
  { split_node_on_key; left_half; right_half; midpoint; rh_dest_cons; lh_dest_snoc; unsplit; get_midpoint_bounds; backing_node_blk_ref }
    
  

(*
FIXME got here; need to implement frame_ops 

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
  (* isa numbers:
type nat = Nat of Big_int.big_int;;
type int = Int_of_integer of Big_int.big_int;;
  *)
  let int2nat n = Arith.nat_of_integer (Big_int.big_int_of_int n) in
  let nat2bigint (Arith.Nat n) = n in
  let bigint2int = Big_int.int_of_big_int in
  let nat2int (n:Arith.nat) = n |> nat2bigint |> bigint2int in
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
    let {split_node_at_k_index; node_merge; node_steal_right; node_steal_left; node_keys_length; node_make_small_root; node_get_single_r} = node_ops in
    Isa_export.Disk_node.Make_node_ops (
      (fun nat n -> split_node_at_k_index (nat2int nat) n |> fun (x,y,z) -> (x,(y,z))), 
      (fun (a,(b,c)) -> node_merge (a,b,c)), 
      (fun (a,(b,c)) -> node_steal_right (a,b,c) |> fun (a,b,c) -> (a,(b,c))), 
      (fun (a,(b,c)) -> node_steal_left (a,b,c) |> fun (a,b,c) -> (a,(b,c))), 
      (fun x -> x |> node_keys_length |> int2nat), 
      (fun (a,(b,c)) -> node_make_small_root (a,b,c)), 
      node_get_single_r)
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
