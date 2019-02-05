(** A store that works directly with trees, not refs to blks. For
   testing. *)

open Isa_btree.Isa_export
open Disk_node

(* a store that works with trees not refs --------------------------- *)


type key = int  [@@deriving yojson]
type value = int  [@@deriving yojson]


type tree = (key,value)Tree.tree [@@deriving yojson]
type r = tree

let t2s t = t |> tree_to_yojson |> Yojson.Safe.pretty_to_string


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
  open Tree

  let store_ops =
    let ( >>= ) = monad_ops.bind in
    let return = monad_ops.return in
    let read r =
      (* r is a tree, but we need to return a frame *)
      let frm =
        match r with
        | Node(ks,ts) -> Disk_node(ks,ts)
        | Leaf(kvs) -> Disk_leaf(kvs)
      in
      return frm
    in
    let write frm = 
      let node = 
        match frm with
        | Disk_node(ks,ts) -> Node(ks,ts)
        | Disk_leaf(kvs) -> Leaf(kvs)
      in
      return node
    in
    let rewrite r frm = write frm >>= fun r -> return (Some r) in
    let free _rs = return () in
    (read,write,rewrite,free)
end

