(** A store that works directly with trees, not refs to blks. For
   testing. *)

open Isa_btree

(* a store that works with trees not refs --------------------------- *)

let k_cmp : int -> int -> int = Pervasives.compare


let leaf_ops : (int,int,(int,int,unit)Tjr_poly_map.map) Isa_export_wrapper.leaf_ops = 
  Isa_export_wrapper.make_leaf_ops ~k_cmp

let _ = leaf_ops

type leaf = (int,int,unit) Tjr_poly_map.map

type key = int  [@@deriving yojson]
type value = int  [@@deriving yojson]

type tree = 
  | Node of (int option,tree,unit) Tjr_poly_map.map
  | Leaf of leaf

type r = tree


module State = struct
  type t = tree
  let compare (x:t) (y:t) = Pervasives.compare x y
end

include struct
  open Tjr_monad.Types
  open Tjr_monad.Imperative
  let monad_ops : imperative monad_ops = 
    Tjr_monad.Imperative.monad_ops
end

let return = monad_ops.return

include struct

  open Isa_export.Disk_node

  let store_ops =
    let ( >>= ) = monad_ops.bind in
    let return = monad_ops.return in
    let read r =
      (* r is a tree, but we need to return a frame *)
      let frm =
        match r with
        | Node n -> Disk_node n
        | Leaf l -> Disk_leaf l
      in
      return frm
    in
    let write frm = 
      let node = 
        match frm with
        | Disk_node n -> Node n
        | Disk_leaf l -> Leaf l
      in
      return node
    in
    let rewrite r frm = write frm >>= fun r -> return (Some r) in
    let free _rs = return () in
    (read,write,rewrite,free)

  let _ = store_ops

end

