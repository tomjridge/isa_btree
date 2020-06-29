(** A store that works directly with trees, not refs to blks. For
   testing. Pointers r are trees themselves. *)

open Test_leaf_node_frame_impls
open Test_monad


(* a store that works with trees not refs --------------------------- *)

(* FIXME perhaps r should just be unit, and the store passes the tree
   around; at the moment we have r as the tree, and the tree is
   duplicated in the store *)


open Isa_export.Disk_node

let store_ops =
  let read r =
    (* r is a test_r, but we need to return a frame *)
    let frm =
      match r with
      | Test_r n -> n
    in
    return frm
  in
  let wrte frm = 
    let node = Test_r frm in
    State_passing.of_fun (fun _ -> (node,node))
  in
  let rewrite r frm = wrte frm >>= fun r -> return (Some r) in
  let free _rs = return () in
  Store_ops_type.{read;wrte;rewrite;free}

let _ : (test_r, (test_node, test_leaf) dnode, test_r state_passing)
    Isa_btree.store_ops
  = store_ops

