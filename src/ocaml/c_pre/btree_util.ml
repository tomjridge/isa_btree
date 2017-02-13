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




(* simple state monad ---------------------------------------- *)

module State_error_monad = struct
  module Make(S: sig type state end) = struct
    module S = S
    type store = S.state
    type 'a m = store -> (store * ('a,string) result)
    open Our.Monad
    let return: 'a -> 'a m = (fun x -> (fun s -> (s,Ok x)))
    let bind: ('a -> 'b m) -> 'a m -> 'b m = (
      fun f x -> (
          fun s -> match x s with
            | (s',Error e) -> (s',Error e)
            | (s',Ok y) -> (f y s')
        ))
    let run: store -> 'a m -> store * ('a,string) result = (fun s f ->
        f s)        
  end
end

let _ = Btree_api.(
    module State_error_monad.Make(struct type state end) : STORE_MONAD)



(* import from Our ---------------------------------------- *)

include Our.Util
