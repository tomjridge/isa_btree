(* marshalling (low-level), followed by pickling *)

(* various marshalling stuff ---------------------------------------- *)


module Basic_marshalling = struct

  (* convert int to bytes *)

  let int32_to_bytes = Int32.(
      fun i0 -> 
        let arr = Array.make 4 (Char.chr 0) in
        for j = 0 to 3 do 
          let off = j in
          let c = (shift_right i0 (8*j)) |> logand (of_int 255) in
          arr.(off) <- (c|>to_int|>Char.chr)
        done;
        [arr.(0);arr.(1);arr.(2);arr.(3)])

  (* assumes bs length 4 *)
  let bytes_to_int32 = Int32.(fun bs -> 
      assert (List.length bs = 4);
      let arr = Array.of_list bs in
      let i = ref (Int32.of_int 0) in
      for j = 0 to 3 do
        let off = j in
        let c = shift_left (arr.(off)|>Char.code|>Int32.of_int) off in
        i:=(logor !i c)
      done;
      !i)




end




(* various pickle/parsing routines ---------------------------------------- *)

(* FIXME move to tjr_lib *)

(* 

what is the contract? that if you pickle, it affects a range, and
unpickling starting at the beginning of the range consumes the range
(so that next pickler can work ok) and returns the same object you
pickled

*)

module type M = sig

  type 'a m

  val ret : 'a -> 'a m
  val bind : ('a -> 'b m) -> ('a m) -> ('b m)
end

(* for pickling, we take 'a m  = fun s -> 'a * s *)

module P = struct


  (* FIXME change this to buffer? yes; or even rev byte list? or
     bytes? what are we going to convert to eventually? probably bytes
     or string, so bytes is the obvious choice except that bytes is
     limited size; so use buffer; buffer append char is reasonably
     efficient; perhaps create with suitable 4096 byte size *)

  type t = string

  type 'a m = t -> 'a * t

  let ret x = (fun s -> (x,s))

  let bind f g = (
    fun s -> 
      g s |> (fun (x,s') -> f x s'))

  let write_bytes bs = (fun s -> ((),s^(BatString.implode bs)))

end

module P_ : M = P

module U = struct

  (* FIXME change this to bytes? no; string and offset? *)
  type t = string

  type 'a m = t -> 'a * t

  let ret x = (fun s -> (x,s))

  let bind f g = (
    fun s -> 
      g s |> (fun (x,s') -> f x s'))

  let map : ('a -> 'b) -> ('a m) -> ('b m) = (
    fun f -> fun x -> x |> bind (fun x -> ret (f x))
  )

  let read_bytes : int -> char list m = (fun n s -> 
      assert (String.length s >= n);
      Tjr_string.split_at s n |> (fun (bs,s') -> (bs|>BatString.explode,s')))

end


module Examples = struct

  (* open Btree_util *)

  let p_pair : 'a P.m -> 'b P.m -> ('a * 'b) P.m = P.(fun p q ->
      p |> bind (fun x -> q |> bind (fun y -> ret (x,y))))

  let p_pair : unit P.m -> unit P.m -> unit P.m = P.(fun p q ->
      p |> bind (fun x -> q |> bind (fun y -> ret ())))

  let u_pair : 'a U.m -> 'b U.m -> ('a * 'b) U.m = U.(fun p q ->
      p |> bind (fun x -> q |> bind (fun y -> ret (x,y)))
    )

  let p_int32 : int32 -> unit P.m = P.(
      fun i -> Basic_marshalling.int32_to_bytes i |> write_bytes
    )

  let u_int32 : int32 U.m = U.(
      read_bytes 4 |> bind (function s -> 
          let [a;b;c;d] = s in
          ret (Basic_marshalling.bytes_to_int32 [a;b;c;d]))
    )

  let p_int i = i |>Int32.of_int|>p_int32

  let u_int = U.(u_int32 |> map Int32.to_int)

  (* assume we know the length somehow *)
  let p_string : string -> unit P.m = P.(
      fun s ->
        BatString.explode s|>write_bytes
    )
  let u_string: int -> string U.m = U.(
      fun n -> read_bytes n |> map BatString.implode
    )

  let p_string_w_len : string -> unit P.m = P.(fun s ->
      p_int (String.length s) |> bind (
        fun _ -> p_string s)
    )

  let u_string_w_len : string U.m = U.(
      u_int |> bind (fun n -> 
          read_bytes n |> map (fun bs -> BatString.implode bs )))


  let p_list : ('a -> unit P.m) -> 'a list -> unit P.m = P.(
      fun p xs ->
        (* write length *)
        p_int (List.length xs) |> bind (
          (* write list *)
          fun _ ->
            let rec loop xs = (
              match xs with
              | [] -> ret ()
              | x::xs' -> (p x |> bind (fun _ -> loop xs')))
            in
            loop xs
        ))


  let u_list : ('a U.m) -> 'a list U.m = U.(
      fun u ->
        u_int |> bind (fun n ->
            let rec loop xs = (
              (* FIXME inefficient *)
              match List.length xs < n with
                true -> u |> bind (fun x -> loop (x::xs))
              | false -> ret (List.rev xs))
            in
            loop [])
    )

end


(* example for btree.simple ---------------------------------------- *)

module String_int = struct


  module KV = struct

    (* the key is actually a 16 byte hash of the full string *)
    type k = string [@@deriving yojson]
    type v = int [@@deriving yojson]

    let key_ord: k -> k -> int = Pervasives.compare
    let equal_value : v -> v -> bool = (=)

  end

  (* let _ = (module KV: Btree_api.KV) *)


  open KV
  open Examples

  (* we know the string has length 16 *)
  let key_size = 16

  let p_key : string -> unit P.m = (fun s -> 
      assert (String.length s = key_size);
      p_string s)


  let u_k : k U.m = (u_string key_size)

  let p_ks : k list -> unit P.m = p_list p_key

  let u_ks : k list U.m = u_list u_k


end

