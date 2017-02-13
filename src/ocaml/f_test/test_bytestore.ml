(* implement and test bytestore ---------------------------------------- *)


open Ext_bytestore
open Btree_util

module Params = struct
  type page = string (* 4096 *)
  let page_size = 4096

  type block = string
  type blk_id = int
end

module Buff = struct
  type t = bytes (* we want to read into a buf; different from block/page *)
  let length = Bytes.length
  let create = (fun n -> Bytes.make n (Char.chr 0))
end

let _ = (module Buff : Buff_t)

(* FIXME here we want to have an in-mem store to page *)

module Disk = struct
  module Buff = Buff
  type store = {free:int; map: Params.page Map_int.t}
  type store_error  (* no constructors *)
  let empty_disk = {free=0; map=Map_int.empty}

  module M = Btree_util.State_error_monad.Make(struct type state = store end)

  type block = Params.block (* 4096 *)
  type blk_id = Params.blk_id
  let block_size = Params.page_size

  let write_buff: Buff.t -> offset -> blk_id M.m = (
    fun buf off s -> 
      let page = Bytes.create block_size in
      let len = 
        let x = Buff.length buf - off in
        if x < block_size then x else block_size
      in
      let _ = Bytes.blit buf off (Bytes.of_string page) 0 len in
      let page_id = s.free in
      ({free=s.free+1; map=Map_int.add page_id page s.map},Ok page_id)
  )

  let read_buff: Buff.t -> offset -> blk_id -> unit M.m = (
    fun buf off i s -> try (
        let len = 
          let x = Bytes.length buf - off in
          if x>block_size then block_size else x
        in
        let page = Map_int.find i s.map in
        let _ = Bytes.blit page 0 buf off len in
        (s,Ok ())
    ) with _ -> failwith "read_buff"
  )

  (* additional Btree.STORE interface -------------------------------------- *)
  type page = string
  type page_ref = int[@@deriving yojson]

  let alloc : page -> page_ref M.m = (
    fun p s -> 
      ({free=s.free+1; map=Map_int.add s.free p s.map},Ok s.free))

  let dest_Store : store -> page_ref -> page = (
    fun s r -> 
      (* print_endline (string_of_int r);  *)
      try (Map_int.find r s.map) with _ -> failwith "dest_Store" )

  let page_ref_to_page: page_ref -> page M.m = (
    fun r s -> 
      try (s,Ok(Map_int.find r s.map)) with _ -> failwith "page_ref_to_page")

  let free : page_ref list -> unit M.m = (
    fun rs s -> (s,Ok ()))

  let page_size = Params.page_size

end

let _ = (module Disk: Disk_t)

let _ = (module Disk: Btree_api.STORE)


(* btree backed by Disk ---------------------------------------- *)

module Btree' = struct 

  module Int_int_store = Ext_int_int_store.Make(Disk)

  type ref_t = int

  open Disk
  open Int_int_store.Btree_simple.

  let empty_btree: unit -> ref_t M.m = (
    fun _ s -> 
      Find.Find.empty_btree () s |> (fun (s,r) -> (s,Btree_util.dest_Ok r))
  )

  let insert: blk_index (* k *) -> blk_id (* v *) -> ref_t -> ref_t M.m = (
    fun k v r -> (
        fun s ->
          Insert.insert k v r s
      )
  )
        
  let find: ref_t -> blk_index -> blk_id M.m = (
    fun r k -> (
        fun s ->
          Find.find s k r |> (
            fun x -> match x with
              | Some y -> (s,y)
              | _ -> failwith "find")))

end


(* instantiate Bytestore ---------------------------------------- *)

module Bytestore' = Ext_bytestore.Make(struct
    module Buff=Buff
    module Disk=Disk
    module Btree=Btree'
end)


(* do some tests ---------------------------------------- *)


open Disk.M


let test len = (
  let buf = Bytes.make len 'a' in
  let r = (Bytestore'.write_buff buf)
          |> bind (fun r -> 
              (* Printf.printf "write_buff: ref1 %d\n" r; *)
          Bytestore'.read_buff r)
          |> bind (fun buf' ->
          assert (Bytes.to_string buf' = Bytes.to_string buf);
          return ())    
  in
  r Disk.empty_disk
  )


let _ = test 1

let _ = List.map test [0;1;4095;4096;4097;8191;8192;8193;40000]
