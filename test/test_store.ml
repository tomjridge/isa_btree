(** A store that works directly with trees, not refs to blks. For
   testing. Pointers r are trees themselves. *)

open Isa_btree
open Test_leaf_node_frame_impls
open Test_monad
(* a store that works with trees not refs --------------------------- *)


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
    return node
  in
  let rewrite r frm = wrte frm >>= fun r -> return (Some r) in
  let free _rs = return () in
  Isa_export_wrapper.{read;wrte;rewrite;free}

let _ : (test_r, (test_node, test_leaf) dnode, test_r state_passing)
    Isa_export_wrapper.store_ops
  = store_ops

