(* A simple block store backed by a file. *)

(* FIXME error handlign *)

module Block = struct

  type t = bytes (* 4096 *)

  let size = 4096 (* bytes *)

  (* block ref *)
  type r = int

end

(* a thin layer over Unix. *)
module Simple = struct

  type r = Block.r

  type block = Block.t

  type state = Unix.file_descr

  let failwith x = failwith ("obt_file_store: "^x)

  let block_size = Block.size

  let mk_block : bytes -> block = (
    fun x -> 
      assert(Bytes.length x = block_size);
      x
  )

  let r_to_off r = block_size * r

  let read : state -> r -> block = (
    fun s r -> 
      try Unix.(
          let _ = lseek s (r_to_off r) SEEK_CUR in
          let buf = Bytes.create block_size in (* bytes are mutable *)
          let n = read s buf 0 block_size in
          let _ = assert (n=block_size) in
          buf)
      with _ -> failwith "read"  (* FIXME *)
  )

  let write: state -> r -> block -> unit = (
    fun s r buf -> 
      try Unix.(
          let _ = lseek s (r_to_off r) SEEK_CUR in        
          let n = single_write s buf 0 block_size in
          let _ = assert (n=block_size) in
          ())
      with _ -> failwith "write"  (* FIXME *)
  )

  let create: string -> state = Unix.(
      fun s ->
        openfile s [O_RDWR] 0o640 
    )


end


module File_store (* : Our.Store_t *) = struct

  open Our
  open Simple

  type page_ref = int [@@deriving yojson]
  type page = block
  type store = state
  type store_error = string

  let alloc p s = Unix.(
      try (
        (* go to end, identify corresponding ref, and write *)
        let n = lseek s 0 SEEK_END in
        let _ = assert (n mod block_size = 0) in
        let r = n / block_size in
        let _ = Simple.write s r p in
        (s,Our.Util.Ok(r))    
      )
      with _ -> (s,Our.Util.Error "File_store.alloc")
  )


  let page_ref_to_page : page_ref -> store -> store * (page, store_error) Util.rresult = (
    fun r s ->
      try (
        (s,Util.Ok(read s r))
      )
      with _ -> (s,Util.Error "File_store.page_ref_to_page")
  )

  let dest_Store : store -> page_ref -> page = (
    fun s r -> 
      failwith "dest_Store"
  )

  
  let empty_store : unit -> store * page_ref = (fun _ -> failwith "empty_store")

end


(* frame mapping for int int kv *)
module Int_int = struct

  module Store = File_store

  module Key_value_types = struct
    type key = int[@@deriving yojson]
    type value_t = int[@@deriving yojson]
    let key_ord (x:int) y = Pervasives.compare x y
    let equal_value x y = (x=y)
  end

  let block_size = Block.size

  let int_size = 4


  (* format: int node_or_leaf; int number of entries; entries *)

  type pframe =  
      Node_frame of (Key_value_types.key list * Store.page_ref list) |
      Leaf_frame of (Key_value_types.key * Key_value_types.value_t) list[@@deriving yojson]


  (* convert an int to 4 bytes/chars; msb is first *)
  let int_to_cs n = (
    let r = ref [] in
    let n = ref n in
    let _ = 
      for i = 0 to 3 do
        let c = Char.chr (!n land 255) in
        let _ = n := !n lsr 8 in
        let _ = r:=c::!r in
        ()
      done
    in
    !r
  )

  let cs_to_int cs = (
    let _ = assert (List.length cs = 4) in
    let n = ref 0 in
    let cs = ref cs in
    let _ =
      for i = 3 to 0 do 
        let c = List.hd !cs in
        let j = (Char.code c) lsl (i*8) in
        n:=!n+j;
        cs:=List.tl !cs
      done
    in
    !n
  )


  let frame_to_page : pframe -> Store.page = (
    fun p ->
      let is = (
        match p with
          Node_frame(ks,rs) -> ([0;List.length ks]@ks@rs)
        | Leaf_frame(kvs) -> (
            [1;List.length kvs]@(List.map fst kvs)@(List.map snd kvs))
      ) |> List.map int_to_cs |> List.concat 
      in
      let buf = Bytes.create block_size in
      let is = ref is in
      let _ = 
        for i = 0 to List.length !is - 1 do
          Bytes.set buf i (List.hd !is);
          is:=List.tl !is
        done
      in
      buf
    )

  let page_to_frame : Store.page -> pframe = (
    fun p -> 
      let is = ref [] in
      let _ = 
        for i = 0 to Block.size / 4 do
          let off = i * 4 in
          let cs = 
            [0;1;2;3]
            |>List.map (fun x -> x+off)|>List.map (fun y -> Bytes.get p y)
          in
          let j = cs_to_int cs in
          is := j::!is 
        done;
        is:=List.rev !is
      in
      match !is with
      | 0::l::rest -> (
          let (ks,rs) = rest|>BatList.take (l+l+1)|>BatList.split_at l in
          Node_frame(ks,rs))
      | 1::l::rest -> (
          let (ks,vs) = rest|>BatList.take (2*l) |> BatList.split_at l in
          let kvs = List.combine ks vs in
          Leaf_frame(kvs)
        )
  )


end
