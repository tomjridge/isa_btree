(* Things related to block devices *)

(* FIXME put everything in monads, so that we can easily compose things *)

(* FIXME make a config modules, which contains basic config params - default blocksize; how many bytes to store an int etc *)

let failwith x = failwith ("block_device: "^x)

open Sexplib.Std (* for ppx_assert *)


(* basic type for in-mem block, and on-disk block ref -------------------- *)

(* FIXME move to config? *)
module Defaults = struct

  (* page of block? at this level we prefer block; in mem we use page *)
  type block = Btree_api.Simple.page 

  let page_size = 4096 (* bytes *)

  (* block ref *)
  type block_ref = Btree_api.Simple.page_ref[@@deriving yojson]

  (* to make an empty block before writing to disk *)
  let empty () = String.make page_size (Char.chr 0) 

end



(* a block device backed by a file ---------------------------------------- *)

module Blkdev_on_fd = struct
  type fd = Unix.file_descr
  type t = fd
  type r = Defaults.block_ref
  type blk = Defaults.block
               
  module M = Btree_util.State_error_monad.Make(struct type state = fd end)

  let block_size = Defaults.page_size

  let mk_block : string -> blk = (
    fun x -> 
      assert(Bytes.length x = block_size);
      x
  )

  let get_fd : t -> fd = fun x -> x

  let r_to_off r = block_size * r

  let read : r -> blk M.m = (
    fun r -> (
        fun s ->
          try Unix.(
              let _ = lseek s (r_to_off r) SEEK_SET in
              let buf = Bytes.make block_size (Char.chr 0) in 
              let n = read s buf 0 block_size in
              (* let _ = [%test_eq: int] n block_size in *)
              let _ = assert (n=block_size) in
              (s,Ok buf))
          with Unix.Unix_error _ -> failwith "read"  (* FIXME *)
      )
  )

  let write: r -> blk -> unit M.m = (
    fun r buf -> (fun s ->
        try Unix.(
            let _ = lseek s (r_to_off r) SEEK_SET in        
            let n = single_write s buf 0 block_size in
            let _ = assert (n=block_size) in
            (s,Ok ()))
        with _ -> failwith "write"  (* FIXME *)
      )
  )


  let sync : unit M.m = (fun s -> 
      try ExtUnixSpecific.fsync s; (s,Ok())
      with _ -> failwith "sync")

  let open_file: string -> fd = Unix.(
      fun s -> openfile s [O_RDWR] 0o640 )


end

let _ = (module Blkdev_on_fd : Btree_api.BLOCK_DEVICE)


(*
module Cached_blockstore = struct 

  type r = Blockstore.r (* ref to a block *)

  type block = Default_block.t

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

(* we target Btree_api.Simple.STORE *)

module Filestore (* : Our.Store_t *) = struct

  type page_ref = Btree_api.Simple.page_ref [@@deriving yojson]
  type page = Btree_api.Simple.page
  let page_size = Defaults.page_size

  type store = { 
    fd: Blkdev_on_fd.fd; 
    free_ref: page_ref;
  }


  open Blkdev_on_fd

  module M = Btree_util.State_error_monad.Make(
    struct type state = store end)

      
  (* alloc without write; free block can then be used to write data
     outside the btree *)
  let alloc_block : page_ref M.m = (
    fun s -> 
      let r = s.free_ref in
      ({s with free_ref=r+1},Ok(r))
  )

  let alloc : page -> page_ref M.m = (
    fun p -> (fun s -> 
        try (
          let r = s.free_ref in
          let x = Blkdev_on_fd.M.(write r p |> run s.fd) in
          ({s with free_ref=r+1},Ok(r))
        )
        with _ -> (s,Error "Filestore.alloc")
      ))


  let free: page_ref list -> unit M.m = (fun ps -> fun s -> (s,Ok()))

  let page_ref_to_page: page_ref -> page M.m = (
    fun r -> (fun s ->
        try (
          let x = Blkdev_on_fd.M.(read r|>run s.fd) in
          match x with
          | (_,Ok(p)) -> (s,Ok(p))
          | (_,Error e) -> (s,Error e)
        ) 
        with _ -> (s,Error "Filestore.page_ref_to_page")
  ))

  
  let dest_Store : store -> page_ref -> page = (
    fun s r -> M.(
        page_ref_to_page r |> run s |> (fun x -> 
            match x with
              (_,Ok(p)) -> p
            | _ -> failwith __LOC__)))

end

let _ = (module Filestore : Btree_api.STORE)

let _ = (module Filestore : Btree_api.Simple.STORE)



(* a filestore which caches page writes and recycles page refs -------------- *)

module Recycling_filestore = struct

  type page_ref = Filestore.page_ref [@@deriving yojson]
  type page = Filestore.page
  let page_size = Defaults.page_size
  
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
    freed_not_synced: Set_r.t   
    (* could be a list - we don't free something that has already been freed *)
  }

  module M = Btree_util.State_error_monad.Make(
      struct type state = store end)

  (* FIXME following should use the monad from filestore *)
  let alloc : page -> page_ref M.m = (
    fun p -> (fun s -> 
        match (Set_r.is_empty s.freed_not_synced) with
        | true -> Filestore.(
            (* want to delay filestore write, but allocate a ref upfront *)
            let free_r = s.fs.free_ref in
            let fs' = { s.fs with free_ref = free_r+1 } in
            let cache' = Cache.add free_r p s.cache in
            ({s with fs=fs';cache=cache'},Ok free_r))
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
                (s',Ok(r))
              )
          )
      )
  )


  let free : page_ref list -> unit M.m = (
    fun ps -> (fun s -> 
        {s with freed_not_synced=(
             Set_r.union s.freed_not_synced (Set_r.of_list ps)) },
        Ok()))


  let page_ref_to_page: page_ref -> page M.m = (
    fun r -> (fun s -> 
        (* consult cache first *)
        let p = try Some(Cache.find r s.cache) with Not_found -> None in
        match p with
        | Some p -> (s,Ok p)
        | None -> (Filestore.page_ref_to_page r s.fs 
                   |> (fun (fs',p) -> ({s with fs=fs'},p)))))


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
              | false -> (
                  match Blkdev_on_fd.(write r p|>M.run s.fs.fd) with
                  | (_,Error e) -> failwith (__LOC__ ^ e)
                  | (_,Ok _) -> ()))
          s.cache 
      in
      ())

end


let _ = (module Recycling_filestore : Btree_api.STORE)

let _ = (module Recycling_filestore : Btree_api.Simple.STORE)
