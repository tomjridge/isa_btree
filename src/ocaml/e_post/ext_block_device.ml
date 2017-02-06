(* Things related to block devices *)

(* FIXME put everything in monads, so that we can easily compose things *)

let failwith x = failwith ("block_device: "^x)

open Sexplib.Std (* for ppx_assert *)


(* basic type for in-mem block, and on-disk block ref -------------------- *)
module Block = struct

  type t = bytes (* 4096 *)

  let size = 4096 (* bytes *)

  (* block ref *)
  type r = int[@@deriving yojson]

  (* to make an empty block before writing to disk *)
  let empty () = Bytes.make size (Char.chr 0) 

end



(* a block device backed by a file ---------------------------------------- *)

module Blk_fd = struct

  type r = Block.r

  type block = Block.t

  type fd = Unix.file_descr

  type t = fd

  let block_size = Block.size

  let mk_block : bytes -> block = (
    fun x -> 
      assert(Bytes.length x = block_size);
      x
  )

  let get_fd : t -> fd = fun x -> x

  let r_to_off r = block_size * r

  let read : fd -> r -> block = (
    fun s r -> 
      try Unix.(
          let _ = lseek s (r_to_off r) SEEK_SET in
          let buf = Block.empty() in (* bytes are mutable *)
          let n = read s buf 0 block_size in
(*
          let _ = print_endline (
              X_string.replace_list {| $n $r $bs |} 
                [("$n",n|>string_of_int);
                 ("$r",r|>string_of_int);
                 ("$bs",block_size|>string_of_int);
                ]
            )
          in
*)
          let _ = [%test_eq: int] n block_size in
          let _ = assert (n=block_size) in
          buf)
      with Unix.Unix_error _ -> failwith "read"  (* FIXME *)
  )

  let write: fd -> r -> block -> unit = (
    fun s r buf -> 
      try Unix.(
          let _ = lseek s (r_to_off r) SEEK_SET in        
          let n = single_write s buf 0 block_size in
          let _ = assert (n=block_size) in
          ())
      with _ -> failwith "write"  (* FIXME *)
  )


  (* FIXME was existing_file_to_fd *)
  let open_file: string -> fd = Unix.(
      fun s ->
        openfile s [O_RDWR] 0o640 
    )


end




(*
module Cached_blockstore = struct 

  type r = Blockstore.r (* ref to a block *)

  type block = Block.t

  module Lru = struct
    module Key = struct
      type t = int
      let compare : t -> t -> int = Pervasives.compare
      let witness : t = 0
    end

    include Lru_cache.Make(Key)
    end

  (* ref to the store itself *)
  type t = { fd:Blockstore.fd; cache: block Lru.t }

  let mk : Blockstore.fd -> t = (fun fd -> {fd;cache=Lru.init 100})

  let read : t -> r -> block = (
    fun s r -> 
      (* try to read from cache *)
      Lru.get s.cache r 
        (fun r -> Blockstore.read s.fd r)
        
  )

  let write : t -> r -> block -> unit = (
    fun s r buf -> 
      (* we just write out for the time being *)
      Blk_fd.write s.fd r buf      
  )

end
*)


(* a store backed by a file ---------------------------------------- *)

module Filestore (* : Our.Store_t *) = struct

  open Our

  type page_ref = int [@@deriving yojson]
  type page = Block.t


  type store = { 
    fd: Blk_fd.fd; 
    free_ref: int;
  }

  type store_error = string

  open Blk_fd

  (* alloc without write; free block can then be used to write data
     out of the btree *)
  let alloc_block : store -> store * (page_ref, store_error) Util.rresult = (
    fun s -> 
      let r = s.free_ref in
      ({s with free_ref=r+1},Our.Util.Ok(r))  
  )

  let alloc : page -> store -> store * (page_ref, store_error) Util.rresult = (
    fun p s -> 
      try (
        (* go to end, identify corresponding ref, and write *)
        (*
        let n = Unix.(lseek (s|>get_fd) 0 SEEK_END) in
        let _ = assert (n mod Block.size = 0) in
        let r = n / Block.size in
           *)
        let r = s.free_ref in
        let _ = write s.fd r p in
        ({s with free_ref=r+1},Our.Util.Ok(r))  
      )
      with _ -> (s,Our.Util.Error "Filestore.alloc")
  )


  let free: 
    page_ref list -> store -> store * (unit, store_error) Util.rresult = (
    fun ps -> fun s -> (s,Util.Ok()))

  let page_ref_to_page: 
    page_ref -> store -> store * (page, store_error) Util.rresult = (
    fun r s ->
      try (
        (s,Util.Ok(read s.fd r))
      )
      with _ -> (s,Util.Error "Filestore.page_ref_to_page")
  )

  let dest_Store : store -> page_ref -> page = (
    fun s r -> read s.fd r)

end




(* a filestore which caches page writes and recycles page refs -------------- *)

module Recycling_filestore = struct

  open Our

  type page_ref = Filestore.page_ref [@@deriving yojson]
  type page = Filestore.page
  type store_error = Filestore.store_error

  
  module Cache = Map.Make(
    struct 
      type t = page_ref
      let compare: t -> t -> int = Pervasives.compare
    end)

  module Set_r = Btree_util.Set_int

  (* we maintain a set of blocks that have been allocated and not
     freed since last sync (ie which need to be written), and a set of
     page refs that have been allocated since last sync and freed
     without being synced (ie which don't need to go to store at
     all) *)

  (* FIXME worth checking no alloc/free misuse? *)

  type store = { 
    fs: Filestore.store; 
    cache: page Cache.t;  (* a cache of pages which need to be written *)
    freed_not_synced: Set_r.t   (* could be a list - we don't free something that has already been freed *)
  }

  let alloc : page -> store -> store * (page_ref, store_error) Util.rresult = (
    fun p s -> 
      match (Set_r.is_empty s.freed_not_synced) with
      | true -> Filestore.(
          (* want to delay filestore write, but allocate a ref upfront *)
          let free_r = s.fs.free_ref in
          let fs' = { s.fs with free_ref = free_r+1 } in
          let cache' = Cache.add free_r p s.cache in
          ({s with fs=fs';cache=cache'},Util.Ok free_r))
      | false -> (
          (* just return a ref we allocated previously *)
          s.freed_not_synced 
          |> Set_r.min_elt 
          |> (fun r -> 
              let s' = 
                {s with 
                 freed_not_synced=(Set_r.remove r s.freed_not_synced);
                 cache=(Cache.add r p s.cache)
                } 
              in
              (s',Util.Ok(r))
            )
        )
    )


  let free : page_ref list -> store -> store * (unit, store_error) Util.rresult
    = (fun ps s -> (
        {s with freed_not_synced=(
             Set_r.union s.freed_not_synced (Set_r.of_list ps)) },
        Util.Ok()))


  let page_ref_to_page : 
    page_ref -> store -> store * (page, store_error) Util.rresult = (
    fun r s -> 
      (* consult cache first *)
      let p = try Some(Cache.find r s.cache) with Not_found -> None in
      match p with
      | Some p -> (s,Util.Ok p)
      | None -> (Filestore.page_ref_to_page r s.fs 
                 |> (fun (fs',p) -> ({s with fs=fs'},p))))


  let dest_Store : store -> page_ref -> page = (
    fun s r -> 
      try (Cache.find r s.cache) with Not_found -> Filestore.dest_Store s.fs r)

  (* FIXME at the moment this doesn't write anything to store - that
     happens on a sync, when the cache is written out *)


  (* FIXME this should also flush the cache of course *)
  let sync : store -> unit = (
    fun s ->
      let () = 
        Cache.iter 
          Filestore.(fun r p -> 
              match (Set_r.mem r s.freed_not_synced) with 
              | true -> () 
              | false -> Blk_fd.write s.fs.fd r p)
          s.cache 
      in
      ())

end

