open Tjr_monad.Types
open Insert_with_mutation

type ('k,'v,'t) dnode = ('k,'v,'t) Pre_monad.dnode

type ('k,'v,'r) insert_state = ('k,'v,'r) Pre_monad.insert_state

(* NOTE in the following, the monad ops are for a fixed type t *)
let make_insert_step (type t) ~(monad_ops:t monad_ops) = 
  let module Monad = struct
    type nonrec t = t
    type ('a,'t) mm = ('a,t) Tjr_monad.Types.m 
    let bind ab a = monad_ops.bind a ab
    let return a = monad_ops.return a
    let dummy = ()
    let fmap f a = a |> bind (fun a -> return (f a))
  end
  in
  let module M = Insert_with_mutation(Monad) in
  let insert_step ~cs ~k_cmp ~store_ops : ('k,'v,'r) insert_state -> (('k,'v,'r) insert_state,t)m =
    let cs = 
      let (a,b,c,d) = cs in
      let f i = Arith.nat_of_integer (Big_int.big_int_of_int i) in
      Pre_monad.Make_constants(f a, f b, f c, f d)
    in
    let k_cmp x y =
      k_cmp x y |> fun i -> Arith.Int_of_integer (Big_int.big_int_of_int i)
    in
    let store_ops = 
      let (a,b,c) = store_ops in
      M.Make_store_ops(a,b,c)
    in
    M.insert_step cs k_cmp store_ops
  in
  insert_step


let insert ~(monad_ops:'t monad_ops) ~cs ~k_cmp ~store_ops =
  let ( >>= ) = monad_ops.bind in
  let return = monad_ops.return in
  let step = make_insert_step ~monad_ops ~cs ~k_cmp ~store_ops in
  fun ~(r:'r) ~(k:'k) ~(v:'v) ->
    let find_state = Pre_monad.make_initial_find_state k r in
    let s = find_state,v in
    let open Pre_monad in
    let rec loop s = 
      match s with
      | I_finished r -> return (Some r)
      | I_finished_with_mutate -> return None
      | _ ->
        step s >>= loop
    in
    return (I_down s) >>= loop

let _ = insert
  
