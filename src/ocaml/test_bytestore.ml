(* implement and test bytestore ---------------------------------------- *)


open Bytestore
open Btree_util



module Page = struct

  type t = bytes (* 4096 *)

  let pagesize = 4096

end



module Buff = struct

  type t = bytes

  let length = Bytes.length

  let create = Bytes.create

end



(* FIXME here we want to have an in-mem store to page *)

module Disk = struct

  type store = {free:int; map: Page.t Map_int.t}

  type store_error  (* no constructors *)


  module M = struct

    type 'a m = store -> store * 'a 

    let bind: ('a -> 'b m) -> 'a m -> 'b m = (
      fun f fa -> fun s -> 
        fa s |> (fun (s,a) -> f a s))

    let return: 'a -> 'a m = fun a -> fun s -> (s,a)

  end      
  

  type block = Page.t (* 4096 *)

  type blk_id = int

  let blocksize = Page.pagesize


  let write_buff: Buff.t -> offset -> blk_id M.m = (
    fun buf off s -> 
      let page = Bytes.create blocksize in
      let len = 
        let x = Bytes.length buf - off in
        if x < blocksize then x else blocksize
      in
      let _ = Bytes.blit buf off page off len in
      let free = s.free in
      ({free=free+1; map=Map_int.add free page s.map},free)
  )

  let read_buff: Buff.t -> offset -> blk_id -> unit M.m = (
    fun buf off i s ->
        let len = 
          let x = Bytes.length buf - off in
          if x>blocksize then blocksize else x
        in
        let page = Map_int.find i s.map in
        let _ = Bytes.blit page 0 buf off len in
        (s,())
  )

  (* write a single int (buff length) into a block *)
  let write_int: int -> blk_id M.m = (
    fun i s -> 
      let buf = Bytes.create blocksize in
      let bs = ints_to_bytes [Int32.of_int i] buf in
      let free = s.free in
      ({free=free+1; map=Map_int.add free buf s.map},free)
  )


  let read_int: blk_id -> int M.m = (
    fun i s ->
      let blk = Map_int.find i s.map in
      let j::_ = bytes_to_ints blk in
      let j' = Int32.to_int j in
      (s,j') )


  (* additional Btree.STORE interface -------------------------------------- *)
  type page = bytes

  type page_ref = int[@@deriving yojson]

  let alloc : page -> store -> store * (page_ref, store_error) rresult = (
    fun p s -> 
      let free = s.free in
      let s' = {s with free=free+1} in
      (s,Ok free))

  let dest_Store : store -> page_ref -> page (* FIXME remove *) = (
    fun s r -> Map_int.find r s.map )

  let page_ref_to_page :
    page_ref -> store -> store * (page, store_error) rresult = (
    fun r s -> (s,Ok(Map_int.find r s.map)))

  let free : page_ref list -> store -> store * (unit, store_error) rresult = (
    fun rs s -> (s,Ok ()))

end


(* btree backed by Disk ---------------------------------------- *)

module Btree' = struct 

  include Int_int_store.Make(Disk)

  type ref_t = int

  open Disk

  FIXME following

  let empty: unit -> ref_t M.m = failwith ""

  let insert: blk_index (* k *) -> blk_id (* v *) -> ref_t -> ref_t M.m = failwith ""
        
  let find: ref_t -> blk_index -> blk_id M.m = failwith ""

end


(* instantiate Bytestore ---------------------------------------- *)

module Bytestore' = Bytestore.Make(struct
    module Buff=Buff
    module Disk=Disk
    module Btree=Btree'
end)

