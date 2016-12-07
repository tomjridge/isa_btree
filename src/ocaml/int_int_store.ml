(* A simple block store backed by a file. *)

(* FIXME error handlign *)

module Set_int = Set.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)

open Sexplib.Std

let failwith x = failwith ("b1_filestore: "^x)

module Block = struct

  type t = bytes (* 4096 *)

  let size = 4096 (* bytes *)

  (* block ref *)
  type r = int

  let empty () = Bytes.make size (Char.chr 0)

end

(* a thin layer over Unix. *)
module Blockstore = struct

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

  
  let existing_file_to_fd: string -> fd = Unix.(
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
      Blockstore.write s.fd r buf      
  )

end
*)


module Filestore (* : Our.Store_t *) = struct

  open Our

  type page_ref = int [@@deriving yojson]
  type page = Block.t


  type store = { 
    fd: Blockstore.fd; 
    free_ref: int;
  }

  type store_error = string

  open Blockstore

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


  let free : page_ref list -> store -> store * (unit, store_error) Util.rresult = (
    fun ps -> fun s -> (s,Util.Ok()))

  let page_ref_to_page : page_ref -> store -> store * (page, store_error) Util.rresult = (
    fun r s ->
      try (
        (s,Util.Ok(read s.fd r))
      )
      with _ -> (s,Util.Error "Filestore.page_ref_to_page")
  )

  let dest_Store : store -> page_ref -> page = (
    fun s r -> read s.fd r
  )


end


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

  module Set_r = Set_int

  (* we maintain a set of blocks that have been allocated and not
     freed, and a maximum ref *)
  type store = { 
    fs: Filestore.store; 
    cache: page Cache.t;  (* a cache of pages which need to be written *)
    freed_not_synced: Set_r.t 
  }

  let alloc : page -> store -> store * (page_ref, store_error) Util.rresult = Unix.(
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
          |> Set_r.max_elt 
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

  let free : page_ref list -> store -> store * (unit, store_error) Util.rresult = (
    fun ps -> fun s -> (
        {s with freed_not_synced=(Set_r.union s.freed_not_synced (Set_r.of_list ps)) }, Util.Ok()))

  let page_ref_to_page : page_ref -> store -> store * (page, store_error) Util.rresult = (
    fun r s -> 
      (* consult cache first *)
      let p = try Some(Cache.find r s.cache) with Not_found -> None in
      match p with
      | Some p -> (s,Util.Ok p)
      | None -> (Filestore.page_ref_to_page r s.fs |> (fun (fs',p) -> ({s with fs=fs'},p))))


  let dest_Store : store -> page_ref -> page = (
    fun s r -> 
      try (Cache.find r s.cache) with Not_found -> Filestore.dest_Store s.fs r
  )

  (* FIXME at the moment this doesn't write anything to store - that
     happens on a sync, when the cache is written out *)

  let sync : store -> unit = (
    fun s ->
      let () = Cache.iter Filestore.(fun r p -> Blockstore.write s.fs.fd r p) s.cache in
      ()
  )

end




(* frame mapping for int int kv *)
module S_int_int (* : Btree.S *) = struct

  module C = struct
    let block_size = Block.size

    let int_size = 4

    (* if n keys, we need 2+n+(n+1) ints to store; n = block_size/4 -2 - 1 / 2 *)
    let max_node_keys = (block_size / int_size - 2 - 1)/2
    let max_leaf_size = (block_size / int_size - 2)/2
    let min_node_keys = 2
    let min_leaf_size = 2
  end

  module KV = struct
    type key = int[@@deriving yojson]
    type value_t = int[@@deriving yojson]
    let key_ord (x:int) y = Pervasives.compare x y
    let equal_value x y = (x=y)
  end

  module ST = Recycling_filestore (* Filestore (* Recycling_filestore *) *)

  module FT = struct

    open KV
    open ST
    (* format: int node_or_leaf; int number of entries; entries *)

    type pframe =  
        Node_frame of (key list * page_ref list) |
        Leaf_frame of (key * value_t) list[@@deriving yojson]



    (* buf is Bytes *)
    let ints_to_bytes (is:int32 list) buf = Int32.(
        let is = Array.of_list is in
        let l = Array.length is in
        let _ = assert (Bytes.length buf >= 4*l) in
        for i = 0 to l-1 do
          let the_int = is.(i) in
          for j = 0 to 3 do 
            let off = 4*i+j in
            let c = (shift_right the_int (8*j)) |> logand (of_int 255) in
            Bytes.set buf off (Char.chr (to_int c))
          done
        done;
        ()
      )

    let bytes_to_ints buf = Int32.(
        let _ = assert (Bytes.length buf mod 4 = 0) in
        let l = Bytes.length buf / 4 in
        let is = Array.make l (Int32.of_int 0) in
        for i = 0 to l-1 do
          for j = 0 to 3 do
            Int32.(
              let off = 4*i+j in
              let c = (Bytes.get buf off) in
              let d = c|>Char.code|>of_int|>(fun x -> shift_left x(8*j)) in
              is.(i) <- add is.(i) d)
          done
        done;
        Array.to_list is
      )


    let frame_to_page' : pframe -> page = (
      fun p ->
        let is = (
          match p with
            Node_frame(ks,rs) -> ([0;List.length ks]@ks@rs)
          | Leaf_frame(kvs) -> (
              [1;List.length kvs]@(List.map fst kvs)@(List.map snd kvs))
        ) |> List.map Int32.of_int
        in
        let buf = Block.empty () in
        ints_to_bytes is buf;
        buf
    )

    let page_to_frame' : page -> pframe = (
      fun buf -> 
        let is = bytes_to_ints buf|>List.map Int32.to_int in
        match is with
        | 0::l::rest -> (
            let (ks,rs) = rest|>BatList.take (l+l+1)|>BatList.split_at l in
            Node_frame(ks,rs))
        | 1::l::rest -> (
            let (ks,vs) = rest|>BatList.take (2*l) |> BatList.split_at l in
            let kvs = List.combine ks vs in
            Leaf_frame(kvs)
          )
    )

    (* FIXME can remove these once code is trusted *)
    let frame_to_page = fun f -> 
      let p = frame_to_page' f in
      let f' = page_to_frame' p in
      let _ = assert (f' = f) in
      p

    let page_to_frame = fun p -> 
      let f = page_to_frame' p in
      let p' = frame_to_page' f in
      let _ = Bytes.([%test_eq: string] (to_string p) (to_string p')) in
      let _ = assert Bytes.(to_string p = to_string p') in
      f

  end (* FT *)


  let existing_file_to_new_store = (
    let open ST in
    let open FT in
    let f : string -> store * page_ref = (
      fun s ->
        let fd = Blockstore.existing_file_to_fd s in
        (* now need to write the initial frame *)
        let frm = Leaf_frame [] in
        let p = frm|>frame_to_page in
        let r = 0 in
        let () = Blockstore.write fd r p in

        Recycling_filestore.(
          {fs = Filestore.{fd=fd;free_ref=r+1} ;
           cache=Cache.empty;
           freed_not_synced=Set_int.empty;
          },r)

(*        
        Filestore.({ fd=fd; free_ref = r+1},r)
*)
)
    in
    f)




end


module T = Btree.Make(S_int_int)
