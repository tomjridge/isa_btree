(* general util stuff ---------------------------------------- *)

module Int = struct
  type t = int 
  let compare: t -> t -> int = Pervasives.compare 
end

module Set_int = Set.Make(Int)
module Map_int = Map.Make(Int)


let dest_Ok x = Our.Util.(
  match x with
  | Ok y -> y
  | _ -> failwith "dest_Ok")

let rresult_to_result = Our.Util.(fun x ->
    match x with
    | Ok y -> Pervasives.Ok y
    | Error (String_error x) -> Pervasives.Error x)

