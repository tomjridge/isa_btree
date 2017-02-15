(* store arbitrary byte buffers on top of a block store -------------------- *)

(* each buffer is stored using an initial "metadata" block (eg
   recording the length of the file); the other blocks store the actual data


   parameters: buff (in-mem buffer); disk (with function to write buff
   at offset to a block, and monad); btree implementation (sharing
   with disk)


   provides: write_buff : buff -> btree.ref; read_buff: btree.ref -> buff

*)

open Our.Util

type blk_index = int
type offset = int

module type Buff_t = sig  
  type t
  val length: t -> int
  val create: int -> t
end

module type Disk_t = sig
  module Buff: Buff_t
  type store
  (* type store_error *)
  module M : (sig
    type 'a m 
    val bind: ('a -> 'b m) -> 'a m -> 'b m
    val return: 'a -> 'a m
  end)
  type block
  type blk_id = int
  val block_size: int 
  (* write block_size bytes from buff, unless at end of buff, in
     which case write the remainder *)
  val write_buff: Buff.t -> offset -> blk_id M.m
  val read_buff: Buff.t -> offset -> blk_id -> unit M.m
end

module type Btree_t = sig
  module Disk : Disk_t
  type ref_t = int (* typically a blk_id; FIXME exposed to make debugging easier *)
  open Disk
  val empty_btree: unit -> ref_t M.m
  val insert: blk_index (* k *) -> blk_id (* v *) -> ref_t -> ref_t M.m
  val find: ref_t -> blk_index -> blk_id M.m
end


module type S = sig 
  (* in-memory buffer *)
  module Buff: Buff_t
  module Disk: Disk_t with module Buff = Buff

  (* copy from in-mem buffer to block; expect start to be block
     aligned? expect end to be start+block_size unless last part of
     buf? FIXME this is actually expected to mutate the block, but
     isn't in the monad (which is really concerned with the store);
     dont' use "original" block after this op! *)
  (*
  val copy: Buff.t -> int (* start *) -> int (* end *) 
    -> Disk.block -> Disk.block
     *)
  module Btree: Btree_t with module Disk = Disk
end



module Make = functor (S:S) -> struct
  
  module S = S

  open S
  open Buff
  open Disk
  open Btree

  open M

  (* use this to store the length of the buffer *)
  let meta_key = -1

  let write_buff : Buff.t -> Btree.ref_t M.m = (
    fun buf -> 
      (* create an empty btree *)
      Btree.empty_btree () |> bind (
        fun r -> 
          (* let _ = Printf.printf "bytestore: write_buff: %d \n" r in *)
          (* allocate first block, and write length *)
          let len = Buff.length buf in
          (* insert len to metablock *)
          insert meta_key len r |> bind (
            fun r ->
              (* let _ = print_endline "bytestore 132" in *)
              (* now write out other blocks *)
              let rec f: blk_index -> ref_t -> ref_t m = (
                fun n r -> (
                    (* if len=4096, we write 1 block; if 4097, 2; if 0, 0 *)
                    let off = n * block_size in
                    match off < len with
                    | true -> (
                        (* alloc, write out, update btree, and recurse *)
                        Disk.write_buff buf off |> bind (
                          fun blk_id ->
                            insert n blk_id r |> bind (
                              fun r -> f (n+1) r)))
                    | false -> (return r)
                  ))
              in
              f 0 r
          )))


  let read_buff : Btree.ref_t -> Buff.t M.m = (
    fun r -> 
      (* get blk_id corresponding to meta block and determine length *)
      find r meta_key |> bind (
        fun len -> 
          (* allocate buffer *)
          let buf = Buff.create len in
          (* now read the blocks and update the buf *)
          let rec f: blk_index -> unit m = (
            fun n ->
              let off = n*block_size in
              match off < len with
              | true -> (find r n |> bind (
                  fun blk_id ->
                    Disk.read_buff buf off blk_id |> bind (
                      fun () ->
                        f (n+1))))
              | false -> (return ()))
          in
          f 0 |> bind (
            fun () -> return buf
          )))

end
