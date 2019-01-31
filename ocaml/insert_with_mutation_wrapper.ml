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
  let insert_step ~cs ~k_cmp ~blk_ops ~marshal_ops ~alloc_ops : ('k,'v,'r) insert_state -> (('k,'v,'r) insert_state,t)m =
    let cs = 
      let (a,b,c,d) = cs in
      let f i = Arith.nat_of_integer (Big_int.big_int_of_int i) in
      Pre_monad.Make_constants(f a, f b, f c, f d)
    in
    let k_cmp x y =
      k_cmp x y |> fun i -> Arith.Int_of_integer (Big_int.big_int_of_int i)
    in
    let blk_ops = 
      let (a,b,c) = blk_ops in
      M.Make_blk_ops(a,b,c)
    in
    let marshal_ops = 
      let (a,b) = marshal_ops in
      M.Make_marshal_ops(a,b)
    in
    let alloc_ops =
      let (a,b) = alloc_ops in
      M.Make_alloc_ops(a,b)
    in
    M.insert_step cs k_cmp blk_ops marshal_ops alloc_ops
  in
  insert_step


let _ : monad_ops:'a monad_ops ->
cs:int * int * int * int ->
k_cmp:('b -> 'b -> int) ->
blk_ops:('c -> ('d, 'a) m) * ('d -> ('c, 'a) m) *
        ('c -> 'd -> ('c option, 'a) m) ->
marshal_ops:('d -> ('b, 'e, 'c) Pre_monad.dnode) *
            (('b, 'e, 'c) Pre_monad.dnode -> 'd) ->
alloc_ops:(unit -> ('c, 'a) m) * ('c list -> (unit, 'a) m) ->
('b, 'e, 'c) Pre_monad.insert_state ->
(('b, 'e, 'c) Pre_monad.insert_state, 'a) m
 = make_insert_step

let insert ~(monad_ops:'t monad_ops) ~cs ~k_cmp ~blk_ops ~marshal_ops ~alloc_ops =
  let ( >>= ) = monad_ops.bind in
  let return = monad_ops.return in
  let step = make_insert_step ~monad_ops ~cs ~k_cmp ~blk_ops ~marshal_ops ~alloc_ops in
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
  
