(* general util stuff ---------------------------------------- *)

module Set_int = Set.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)

module Map_int = Map.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)




(* int array <-> bytes ---------------------------------------- *)


(* this have type unit, but updates mutable buf *)
let ints_to_bytes : int32 list -> bytes -> unit = Int32.(
    fun is buf -> 
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




(* import from Our ---------------------------------------- *)

include Our.Util
