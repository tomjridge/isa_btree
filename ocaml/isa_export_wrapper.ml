open Tjr_monad.Types
open Constants_type
open Isa_export

let dest_Some x = match x with Some x -> x | _ -> failwith "dest_Some"


type ('node,'leaf) dnode = ('node,'leaf) Disk_node.dnode

type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
 find: r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
 insert: r:'r -> k:'k -> v:'v -> ('r option,'t) m;
 delete: r:'r -> k:'k -> ('r,'t) m;
}

(* leaf ops --------------------------------------------------------- *)


(* As Isabelle def. See \doc(doc:leaf_ops). *)

type ('k,'v,'leaf) leaf_ops = {
  leaf_lookup: 'k -> 'leaf -> 'v option;
  leaf_insert: 'k -> 'v -> 'leaf -> 'leaf * 'v option;
  leaf_remove: 'k -> 'leaf -> 'leaf;
  leaf_length: 'leaf -> int;
  dbg_leaf_kvs: 'leaf -> ('k*'v) list;
  leaf_steal_right: 'leaf * 'leaf -> 'leaf * 'k * 'leaf;
  leaf_steal_left: 'leaf*'leaf -> 'leaf*'k*'leaf;
  leaf_merge: 'leaf * 'leaf -> 'leaf;
  split_large_leaf: int -> 'leaf -> 'leaf*'k*'leaf
}


let make_leaf_ops ~k_cmp = 
  let map_ops = Tjr_poly_map.make_map_ops k_cmp in
  let leaf_lookup k l = map_ops.find_opt k l in
  let leaf_insert k v l = 
    map_ops.find_opt k l |> fun v' ->
    map_ops.add k v l |> fun l -> (l,v')
  in
  let leaf_remove k l = map_ops.remove k l in
  let leaf_length l = map_ops.cardinal l in
  let dbg_leaf_kvs l = map_ops.bindings l in
  let leaf_steal_right (l1,l2) =
    map_ops.min_binding_opt l2 |> dest_Some |> fun (k,v) ->
    l2 |> map_ops.remove k |> map_ops.min_binding_opt |> dest_Some |> fun (k',_) ->
    l1 |> map_ops.add k v |> fun l1 ->
    (l1,k',l2)
  in
  let leaf_steal_left (l1,l2) =
    map_ops.max_binding_opt l1 |> dest_Some |> fun (k,v) ->
    l1 |> map_ops.remove k |> fun l1 ->
    l2 |> map_ops.add k v |> fun l2 ->
    (l1,k,l2)
  in
  let leaf_merge (l1,l2) = map_ops.disjoint_union l1 l2 in
  let split_large_leaf i l1 = 
    l1 |> map_ops.bindings |> Tjr_list.drop i |> fun binds -> 
    match binds with
    | [] -> failwith __LOC__
    | (k,v)::rest -> 
      l1 |> map_ops.split k |> fun (l1,_,l2) -> 
      l2 |> map_ops.add k v |> fun l2 ->
      (l1,k,l2)
  in
  ({ leaf_lookup; leaf_insert; leaf_remove; leaf_length; 
    dbg_leaf_kvs; leaf_steal_right; leaf_steal_left; 
    leaf_merge;
    split_large_leaf } : ('k,'v,('k,'v,unit)Tjr_poly_map.map) leaf_ops)
  
let _ = make_leaf_ops


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

(* open Tjr_fs_shared *)

(* implement node ops using a map from option; see impl notes in \doc(doc:node_ops) *)

(* None is less than any other lower bound; this corresponds to the
   "lowest" interval below k0 *)
let rec key_compare k_cmp k1 k2 =
  match k1,k2 with 
  | None,None -> 0
  | None,_ -> -1
  | _,None -> 1
  | Some k1, Some k2 -> k_cmp k1 k2

let make_node_ops (type k) ~(k_cmp:k -> k -> int) = 
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
  ({ split_node_at_k_index; node_merge; node_steal_right; node_steal_left; node_keys_length;
     node_make_small_root; node_get_single_r } : (k,'v,(k option,'v,unit)Tjr_poly_map.map) node_ops)

let _ :
k_cmp:('a -> 'a -> int) ->
('a, 'b, ('a option, 'b, 'c) Tjr_poly_map.map) node_ops
= make_node_ops


(* frame_ops -------------------------------------------------------- *)

(* See Isabelle defn. See \doc(doc:frame_ops) *)

type 'k or_top = 'k option

type 'k or_bottom = 'k option

type ('k,'r) segment = 'k or_bottom * 'r * ('k*'r) list * 'k or_top

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
}

(* FIXME maybe move elsewhere *)

type ('k,'r,'node) frame = {
  midkey: 'k option;  (* may be None *)
  midpoint: 'r;
  node: 'node;
  backing_node_blk_ref: 'r
}

let make_frame_ops (type k r) ~(k_cmp:k->k->int) = 
  let map_ops = Tjr_poly_map.make_map_ops (key_compare k_cmp) in
  Tjr_fs_shared.Map_with_key_traversal.make_ops ~map_ops @@ fun ~get_next_binding ~get_prev_binding ->
  (* map_ops is a map from 'k option *)
  let split_node_on_key backing_node_blk_ref k n = 
    (* get the relevant key *)
    let midkey,midpoint = 
      map_ops.find_opt (Some k) n |> function
      | None -> get_prev_binding (Some k) n |> dest_Some |> fun (k,r) ->
                (k,r)
      | Some r -> (Some k,(r:r))
    in
    { midkey; midpoint; backing_node_blk_ref; node=n }
  in
  let _ = split_node_on_key in
  let midpoint f = f.midpoint in
  let get_focus f = 
    let k1 = f.midkey in
    let k2 = f.node |> get_next_binding f.midkey |> function 
      | None -> None 
      | Some (k,r) -> k
    in
    (k1,f.midpoint,k2)
  in
  let get_focus_and_right_sibling f =
    let k1,r1 = f.midkey,f.midpoint in
    f.node |> get_next_binding f.midkey |> function
    | None -> None
    | Some (k2,r2) -> 
      let k2 = k2 |> dest_Some in
      (* NOTE as a hack, we just return None for k3, since it is never used... *)
      Some(k1,r1,k2,r2,None)
  in
  let get_left_sibling_and_focus f = 
    f.node |> get_prev_binding f.midkey |> function
    | None -> None 
    | Some(k1,r1) ->
      let k2,r2 = f.midkey,f.midpoint in
      let k2 = k2 |> dest_Some in
      (* NOTE hack *)
      Some(k1,r1,k2,r2,None)
  in
  let replace (k,r,krs,_) (k',r',krs',_) f =
    assert(key_compare k_cmp k k' = 0);
    f.node |> map_ops.add k' r' |> fun n ->
    (* remove old ks *)
    (krs,n) 
    |> Tjr_list.iter_opt (fun (krs,n) ->
      match krs with 
      | [] -> None
      | (k,r)::krs ->
        n |> map_ops.remove (Some k) |> fun n -> Some(krs,n))
    |> snd
    (* add new krs *)
    |> fun n ->
    (krs',n) 
    |> Tjr_list.iter_opt (fun (krs,n) -> 
      match krs with
      | [] -> None
      | (k,r)::krs ->
        n |> map_ops.add (Some k) r |> fun n -> Some(krs,n))
    |> snd
    |> fun node ->
    { f with node }
  in
  let frame_to_node f = f.node in
  let get_midpoint_bounds f = 
    let l : k option = f.midkey in
    let u = f.node |> get_next_binding f.midkey |> function
      | None -> None
      | Some (k,r) -> (k:k option)
    in
    (l,u)
  in
  let backing_node_blk_ref f = f.backing_node_blk_ref in
  { split_node_on_key; midpoint; get_focus; get_focus_and_right_sibling; 
    get_left_sibling_and_focus; replace; frame_to_node; get_midpoint_bounds;
    backing_node_blk_ref }
  
;;
      

let _ :
k_cmp:('a -> 'a -> int) ->
('a, 'b, ('a, 'b, ('a or_bottom, 'b, 'c) Tjr_poly_map.map) frame,
 ('a or_bottom, 'b, 'c) Tjr_poly_map.map)
frame_ops
 = make_frame_ops

;;


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
  let leaf_ops2isa leaf_ops  = 
    let  { leaf_lookup; leaf_insert; leaf_remove; leaf_length; 
           dbg_leaf_kvs; leaf_steal_right; leaf_steal_left; 
           leaf_merge;
           split_large_leaf }
      = leaf_ops 
    in
    Isa_export.Disk_node.Make_leaf_ops(
      leaf_lookup,leaf_insert,leaf_remove,
      (fun l -> leaf_length l |> int2nat),dbg_leaf_kvs,
      (fun (l1,l2) -> leaf_steal_right (l1,l2) |> fun (a,b,c) -> (a,(b,c))),
      (fun (l1,l2) -> leaf_steal_left (l1,l2) |> fun (a,b,c) -> (a,(b,c))),
      leaf_merge,
      (fun n l -> split_large_leaf (nat2int n) l |> fun (a,b,c) -> (a,(b,c))))
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
  let frame_ops2isa frame_ops = 
    let   { split_node_on_key; midpoint; get_focus; get_focus_and_right_sibling; 
    get_left_sibling_and_focus; replace; frame_to_node; get_midpoint_bounds;
            backing_node_blk_ref } = frame_ops 
    in
    let seg2isa (a,b,c,d) = (a,(b,(c,d))) in
    let isa2seg (a,(b,(c,d))) = (a,b,c,d) in
    Isa_export.Stacks_and_frames.Make_frame_ops(
      split_node_on_key, midpoint, 
      (fun f -> get_focus f |> fun (a,b,c) -> (a,(b,c))), 
      (fun f -> get_focus_and_right_sibling f |> function None -> None | Some(a,b,c,d,e) -> Some(a,(b,(c,(d,e))))), 
      (fun f -> get_left_sibling_and_focus f |> function None -> None | Some(a,b,c,d,e) -> Some(a,(b,(c,(d,e))))),
      (fun seg1 seg2 -> replace (isa2seg seg1) (isa2seg seg2)), 
      frame_to_node, 
      get_midpoint_bounds, 
      backing_node_blk_ref, 
      (fun x -> failwith "FIXME_not_implemented"), 
      (fun x -> failwith "FIXME not implemented"))
  in
  let store_ops2isa store_ops = 
    let (a,b,c,d) = store_ops in
    M.Post_monad.make_store_ops a b c d
  in
  fun ~cs ~k_cmp ~store_ops ~check_tree_at_r' -> 
    let leaf_ops = make_leaf_ops ~k_cmp in
    let node_ops = make_node_ops ~k_cmp in
    let frame_ops = make_frame_ops ~k_cmp in
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
