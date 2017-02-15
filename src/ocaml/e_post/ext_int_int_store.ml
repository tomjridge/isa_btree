(* a map from int to int; Store.page=bytes --------------------------------- *)

(* parameters are just ST; block.size is fixed *)

(* FIXME error handlign *)

open Sexplib.Std  (* for ppx_assert *)

let failwith x = failwith ("int_int_store: "^x)

open Ext_block_device

open Btree_util

(* assumptions ---------------------------------------- *)

let int_size = 4  (* bytes *)


(* KV, C, STORE, FT --------------------------------------- *)

(* for ints *)
module KV = struct
  type key = int[@@deriving yojson]
  type value = int[@@deriving yojson]
  let key_ord (x:int) y = Pervasives.compare x y
  let equal_value : value -> value -> bool = (=)
end

let _ = (module KV : Btree_api.KEY_VALUE)


(* NB page=string *)
module type STORE = Btree_api.Simple.STORE


module Make = functor (ST:STORE) -> struct
  module ST = ST
  module Btree_simple = Btree_simple.Make(struct
    module KV=KV
    module ST=ST
    open KV
    open Btree_api.Pickle_params
    let pp = Pickle.Examples.{
        p_k = p_int;
        u_k = u_int;
        k_len = 4;
        p_v = p_int;
        u_v = u_int;
        v_len = 4;
      }
  end)
end


(* int-int store on recycling filestore ------------------------------------- *)

(* from here we specialize to recycling_filestore *)

module ST = Recycling_filestore

module Int_int_filestore = struct

  module Int_int_store = Make(ST)

  let existing_file_to_new_store = (
    let open Int_int_store.Btree_simple.Btree.S.FT in
    let open ST in
    let f : string -> store * page_ref = (
      fun s ->
        let fd = Blkdev_on_fd.open_file s in
        (* now need to write the initial frame *)
        let frm = Leaf_frame [] in
        let p = frm|>frame_to_page in
        let r = 0 in
        let () = (
          match Blkdev_on_fd.(write r p |> M.run fd) with
          | (_,Error e) -> failwith (__LOC__ ^ e)
          | _ -> ())
        in
        ST.(
          {fs = Filestore.{fd=fd;free_ref=r+1} ;
           cache=ST.Cache.empty;
           freed_not_synced=Set_int.empty;
          },r))
    in
    f)

end

(* FIXME want this let _ = (module Int_int_filestore.Btree : Btree_api.MAP) *)


(* a high-level cache over Insert_many -------------------------------------- *)

(* we cache at the map level *)

module Int_int_cached (* : Btree.S *) = struct

  open Int_int_filestore

  type kvs = (KV.key * KV.value) list

  type pending_inserts = int Map_int.t  (* the high-level cache *)

  type t = ST.page_ref * ST.store * pending_inserts

  module Insert = struct

    (* just add to cache *)
    let insert : KV.key -> KV.value -> t -> t = (
      fun k v t -> 
        let (r,s,ps) = t in
        let ps' = Map_int.add k v ps in
        (r,s,ps'))

  end

  let sync : t -> t = (
    fun t -> 
      let (r,s,kvs) = t in
      (* insert all that are in the cache, using insert_many.cache *)
      let kvs = Map_int.bindings kvs in
      match kvs with 
      | [] -> (
          let () = ST.sync s in
          (r,s,Map_int.empty))
      | _ -> (  
          let f (s,r,kvs) = (
            match kvs with
              [] -> None
            | (k,v)::kvs -> (
                let (s,(r,kvs)) = 
                  Int_int_filestore.Int_int_store.Btree_simple.Btree.Insert_many.insert k v kvs r s in
                Some(s,r,kvs)))
          in
          let (s,r,kvs) = Btree.iter_step f (s,r,kvs) in
          let () = ST.sync s in
          (r,s,Map_int.empty)
        )
  )



end

