(** An implementation of functional sequences; for testing *)

type ('a,'t) tjr_seq_type = {
  take_and_drop: int -> 't -> 'a list * 't;  (* if the list is empty, the seq should be empty *)
}

(* implement a sequence from l to h by a pair (l,h) *)

(** int sequence from l to h *)
let ( -- ) = 
  let rec take n (l,h) =
    match n>0 && l <= h with
    | true -> l::take (n-1) (l+1,h)
    | false -> []
  in
  let rec take_and_drop n (l,h) =
    take n (l,h) |> fun xs ->
    xs,(l+List.length xs,h)
  in
  fun (l:int) (h:int) -> { take_and_drop },(l,h)

let _ = ( -- )

let rec map f {take_and_drop} = {
  (* take=(fun n t -> take n t |> List.map f); *)
  take_and_drop=(fun n t -> 
      take_and_drop n t |> fun (xs,t) -> 
      (List.map f xs),t)
}

let iter f {take_and_drop;_} t = 
  let rec g t = 
    take_and_drop 1 t |> function
    | [],_ -> ()
    | [x],t -> f x; g t
    | _ -> failwith __LOC__
  in
  g t

let test = 
  Global.register ~name:"Tjr_seq.test" 
    (fun () -> 
       Printf.printf "Tjr_seq.test: running tests...\n%!";
       let {take_and_drop},seq = 1 -- 1000 in
       assert(take_and_drop 2 seq |> function [1;2],_ -> true | _ -> false);
       assert(take_and_drop 2 seq |> function [1;2],_ -> true | _ -> false);
       assert(take_and_drop 100 seq |> fun (seq,_) -> List.hd seq = 1 && List_.last seq = 100);
       let _,seq = take_and_drop 100 seq in
       assert(take_and_drop 2 seq |> function [101;102],_ -> true | _ -> false);
       let {take_and_drop} = map (fun x -> 2*x) {take_and_drop} in
       assert(take_and_drop 2 seq |> function [202;204],_ -> true | _ -> false);
       Printf.printf "Tjr_seq.test: all tests pass!\n%!"
    )

  
