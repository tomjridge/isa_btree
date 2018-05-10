(* a thin layer above the isabelle defns, eg iterating the small
   steps *)

open Isa_export


module Basic_conversions = struct

  (** Translations between Isabelle types and OCaml native types. *)

  let x5 (x,(y,(z,(w,u)))) = (x,y,z,w,u)

  let int_to_nat x = (x |>Big_int.big_int_of_int|>Arith.nat_of_integer)

  let int_to_int x = (
    x |>Big_int.big_int_of_int|>(fun x -> Arith.Int_of_integer x))

  let x_cmp cmp x y = cmp x y |> int_to_int
  (*  let x_ps0 ~constants ~cmp : 'k IE.Params.ps0 = (
      Ps0(constants|>x_constants, cmp|>x_cmp)) *)

end
include Basic_conversions


module Constants = struct 

  (* no need to introduce a separate type FIXME remove constants.ml *)
  type constants = unit Prelude.constants_ext

  let mk_constants ~min_leaf_size ~max_leaf_size ~min_node_keys ~max_node_keys : constants =
    Prelude.Constants_ext(
      min_leaf_size|>int_to_nat,
      max_leaf_size|>int_to_nat,
      min_node_keys|>int_to_nat,
      max_node_keys|>int_to_nat,
      ())

  let x_constants (cs:constants) = cs

end
include Constants


let x_ps1 ~constants ~cmp = Params.(Ps1(x_constants constants, x_cmp cmp))

let _ = x_ps1


type ('k,'v,'r) dnode = ('k,'v,'r) Isa_export.Disk_node.dnode


type ('k,'v,'r) find_state = ('k,'v,'r) Find_state.find_state
type ('k,'v,'r) insert_state = ('k,'v,'r) Insert_state.insert_state
type ('k,'v,'r) im_state = ('k,'v,'r) Insert_many_state.imst
type ('k,'v,'r) delete_state = ('k,'v,'r) Delete_state.delete_state

(* isa doesn't export type abbrevs *)
type ('k,'r) rsplit_node = ('k,'r,unit) Searching_and_splitting.rsplit_node_ext
type ('k,'r) rstack = ('k,'r) rsplit_node list
type ('k,'r) rstk = ('k,'r) rstack

type ('k,'v) tree = ('k,'v) Isa_export.Tree.tree

type ('k,'v,'r) ls_state = ('k,'v,'r) Leaf_stream_state.ls_state

(* find_state ------------------------------------------------------- *)


(** Construct an initial "find state" given a key and a reference to
    a B-tree root. *)
let  mk_find_state k r : ('k,'v,'r) find_state = Find_state.mk_find_state k r

(** Check whether we have reached a leaf. Returns the reference to the
    B-tree root (when [mk_find_state] was called), the key we are
    looking for (ditto), a reference to a leaf (that may contain the
    key... if any leaf contains the key, this leaf does) and a the list
    of (key,values) in that leaf. *)
let dest_f_finished (fs:('k,'v,'r)find_state) : ('r * 'k * 'r * 'kvs * ('k,'r) rstk) option = (
  Find_state.dest_f_finished fs 
  |> (function None -> None | Some  x -> Some (x5 x)))

(*open Params2*)

(* only check if we have access to the relevant r2t and spec_tree *)
(* ASSUMES r2t ps <> None *)
(** Wellformedness check. Assumes access to the "spec tree", the
    global state and the find state.  *)
let wellformed_find_state ~r2t ~cmp : 'tree -> 't -> ('k,'v,'r) find_state -> bool = (
  fun t s fs -> 
    Find_state.wellformed_find_state 
      (x_cmp cmp) r2t t s fs)



(* insert_state ----------------------------------------------------- *)

let mk_insert_state: 'k->'v->'r->('k,'v,'r) insert_state = 
  Insert_state.mk_insert_state

(** Result is a reference to the updated B-tree *)
let dest_i_finished: ('k,'v,'r)insert_state -> 'r option = 
  Insert_state.dest_i_finished

let wellformed_insert_state ~cmp ~constants ~r2t :'tree->'t->'k->'v->('k,'v,'r) insert_state->bool = (
  fun t s k v is ->
    Insert_state.wellformed_insert_state 
      (x_constants constants) (x_cmp cmp)
      r2t t s k v is)


(* im_state --------------------------------------------------------- *)


let mk_im_state: 'k -> 'v -> ('k*'v) list -> 'r -> ('k,'v,'r) im_state = 
  Insert_many_state.mk_im_state

let dest_im_finished: ('k,'v,'r)im_state -> ('r*('k*'v)list) option = 
  Insert_many_state.dest_im_finished
(* no wf *)


(* delete_state ----------------------------------------------------- *)

let dest_d_finished : ('a, 'b, 'c) delete_state -> 'c option = Delete_state.dest_d_finished
let mk_delete_state : 'a -> 'b -> ('a, 'c, 'b) delete_state = Delete_state.mk_delete_state

let wellformed_delete_state ~constants ~cmp ~r2t ~t ~(s:'t) ~k ~(ds:('k,'v,'r)delete_state) 
  = Delete_state.wellformed_delete_state
      (x_constants constants)
      (x_cmp cmp) r2t t s k ds
  
let mk_delete_state = Delete_state.mk_delete_state


(* ls_state --------------------------------------------------------- *)

(** Given a reference to a B-tree root, construct a stream of leaves *)
let mk_ls_state : 'r -> ('k,'v,'r) ls_state = Leaf_stream_state.mk_ls_state

(** Return the (key,value) list at the current leaf in the stream. *)
let ls_dest_leaf (ls:('k,'v,'r) ls_state) = Leaf_stream_state.dest_LS_leaf ls

let ls_is_finished (lss:('k,'v,'r) ls_state) : bool = (lss |> Leaf_stream_state.lss_is_finished)




module Make(Monad: MONAD) = struct

  include Isa_export.Make(Monad)



  (** Leaf stream state. Needed early for store_ops *)

  (* NOTE this type is made abstract in isa_export; it supports step,
     dest_LS_leaf, and lss_is_finished ops *)
  type ('k,'v,'r) ls_state = ('k,'v,'r) Leaf_stream_state.ls_state

  (* FIXME not included in ocamldoc for some reason... *)
  module Store_ops' = struct
    open Store_ops

    module Store_ops_type = struct 

    end

    (* NOTE isa iterated pairs nest to right *)
    type ('k,'v,'r,'t) store_ops = Store_ops of (
 ('r -> (('k,'v,'r) dnode,'t) Monad.mm) * 
 ((('k,'v,'r) dnode -> ('r,'t) Monad.mm) *
 ('r list -> (unit,'t) Monad.mm)))

    let mk_store_ops ~store_free ~store_read ~store_alloc : ('k,'v,'r,'t)store_ops =
      Store_ops(store_read,(store_alloc,store_free))
    
    let dest_store_ops (store_ops:('k,'v,'r,'t)store_ops) = fun f ->
      let Store_ops store_ops = store_ops in
      f ~store_free:(store_free store_ops) ~store_read:(store_read store_ops)
        ~store_alloc:(store_alloc store_ops)

    let x_store_ops = function (Store_ops s) -> s

  end
  include Store_ops'

  open Monad



  module Small_step = struct

    (* find ---------------------------------------- *)

    (** Small step the find state: take a find state and return an updated
        find state (in the monad). *)
    let find_step ~constants ~cmp ~store_ops : 'fs->('fs,'t) mm = (fun fs -> 
        Find.find_step (x_ps1 ~constants ~cmp) store_ops fs)


    (* delete ---------------------------------------- *)

    (** Similar functionality to [mk_find_state] *)
    let mk_delete_state: 'k -> 'r -> ('k,'v,'r) delete_state = 
      Delete_state.mk_delete_state

    let delete_step ~constants ~cmp ~store_ops : 'ds -> ('ds,'t) mm = 
      (fun ds -> Delete2.delete_step (x_ps1 ~constants ~cmp) store_ops ds)

    (** The result is a reference to the updated B-tree *)
    let dest_d_finished: ('k,'v,'r) delete_state->'r option = Delete_state.dest_d_finished

    let wellformed_delete_state ~cmp ~constants ~r2t : 'tree->'t->'k->('k,'v,'r) delete_state->bool = (
      fun t s k ds -> 
        Delete_state.wellformed_delete_state 
          (x_constants constants) (x_cmp cmp)
          r2t t s k ds)


    (* insert ---------------------------------------- *)

    let insert_step ~cmp ~constants ~store_ops : 'is -> ('is,'t) mm = 
      (fun is -> Insert.insert_step (x_ps1 ~cmp ~constants) store_ops is)

    (* insert_many ---------------------------------------- *)

    let im_step ~constants ~cmp ~store_ops : 'im -> ('im,'t) mm = 
      (fun is -> Insert_many.insert_step (x_ps1 ~constants ~cmp) store_ops is)


    (* leaf stream ---------------------------------------- *)

    (** Step the leaf stream to the next leaf. If the leaf stream is
        finished (no more leaves), stepping will just return the leaf
        stream unchanged. So in the loop you need to check whether you have
        finished using [ls_is_finished]. FIXME here and elsewhere, staging *)
    let ls_step ~constants ~cmp ~store_ops ls 
      : (('k,'v,'r) ls_state,'t) mm = 
      Leaf_stream.lss_step (x_ps1 ~constants ~cmp) store_ops ls

    let _ = ls_step

  end


end

(*
  let x_store_ops store_ops : ('k,'v,'r,'t,unit) store_ops_ext = (
    dest_store_ops store_ops @@ fun ~store_free ~store_read ~store_alloc ->
    Store_ops_ext(
      store_read,
      store_alloc,
      store_free,()))
*)



(*
module Free_monad_instance = struct

  (** The functor [Make] allows the Monad to be a parameter of the
      whole code. The following instantiates the monad as a "syntactic"
      monad, which may or may not be useful. *)

  type ('a,'k,'v,'r,'t) free =
    | Return : 'a -> ('a,'k,'v,'r,'t) free
    | Bind: ('a,'k,'v,'r,'t) free * ('a -> ('b,'k,'v,'r,'t) free) -> ('b,'k,'v,'r,'t) free
    | Store_free: 'r list -> (unit,'k,'v,'r,'t) free
    | Store_read: 'r -> (('k,'v,'r)Disk_node.dnode,'k,'v,'r,'t) free
    | Store_alloc: ('k,'v,'r)Disk_node.dnode -> ('r,'k,'v,'r,'t) free

  let return x = Return x
  let bind a ab = Bind (a,ab)
  let store_free rs = Store_free rs
  let store_read r = Store_read r
  let store_alloc dnode = Store_alloc dnode 


  (* alternatively, at this point we can interpret into another monad?
     but then we might as well interpret directly into our phantom
     monad *)

  let store_ops_to_pre_map_ops 



    = Made.store_ops_to_pre_map_ops

      
  (* ah! the problem is that we can't treat ('a,'k,'v,'r,'t) free as a
     monad 'a m with parameters 'k,'v,'r,'t *)
  module Make(S:sig type k type v type r end) = struct
    open S
    module Monad : MONAD = struct
      type ('a,'t) mm = ('a,k,v,r,'t) free
      let bind ab a = bind a ab
      let return = return
      let dummy = ()
      let fmap f a = bind (fun a -> return (f a)) a
    end
    
    include Make(Monad)

    let _ = store_ops_to_pre_map_ops
        
    (* NOTE this allows us to generalize over the k v r types *)
    let store_ops_to_pre_map_ops 
      (type kk vv rr) ~ps ~store_free ~store_read ~store_alloc 
      = 
      store_ops_to_pre_map_ops ~ps ~store_free ~store_read ~store_alloc

    let _ = store_ops_to_pre_map_ops
    
  end

  module Made = Make(struct type k type v type r end)

  let _ = store_ops_to_pre_map_ops
   
  (* Ah, but this won't work because the monad type is in Made, with a fixed k etc *)
  let example ps = 
    store_ops_to_pre_map_ops ~ps ~store_free ~store_read ~store_alloc


  (* so it looks like we have to do the whole thing in a function? *)

end
*)
