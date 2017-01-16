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

  let empty_disk = {free=0; map=Map_int.empty}

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
      let _ = Bytes.blit buf off page 0 len in
      let page_id = s.free in
      ({free=s.free+1; map=Map_int.add page_id page s.map},page_id)
  )

  let read_buff: Buff.t -> offset -> blk_id -> unit M.m = (
    fun buf off i s -> try (
        let len = 
          let x = Bytes.length buf - off in
          if x>blocksize then blocksize else x
        in
        let page = Map_int.find i s.map in
        let _ = Bytes.blit page 0 buf off len in
        (s,())
    ) with _ -> failwith "read_buff"
  )

(*
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
*)

  (* additional Btree.STORE interface -------------------------------------- *)
  type page = bytes

  type page_ref = int[@@deriving yojson]

  let alloc : page -> store -> store * (page_ref, store_error) rresult = (
    fun p s -> 
      ({free=s.free+1; map=Map_int.add s.free p s.map},Ok s.free))

  let dest_Store : store -> page_ref -> page (* FIXME remove *) = (
    fun s r -> 
      (* print_endline (string_of_int r);  *)
      try (Map_int.find r s.map) with _ -> failwith "dest_Store" )

  let page_ref_to_page :
    page_ref -> store -> store * (page, store_error) rresult = (
    fun r s -> 
      try (s,Ok(Map_int.find r s.map)) with _ -> failwith "page_ref_to_page")

  let free : page_ref list -> store -> store * (unit, store_error) rresult = (
    fun rs s -> (s,Ok ()))

end


(* btree backed by Disk ---------------------------------------- *)

module Btree' = struct 

  include Int_int_store.Make(Disk)

  type ref_t = int

  open Disk

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

module Bytestore' = Bytestore.Make(struct
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
