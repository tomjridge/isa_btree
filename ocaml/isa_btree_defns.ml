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


module Make(Monad: MONAD) = struct

  include Isa_export.Make(Monad)

  
  type ('k,'v,'r) find_state = ('k,'v,'r) Find.find_state
  type ('k,'v,'r) insert_state = ('k,'v,'r) Insert.insert_state
  type ('k,'v,'r) im_state = ('k,'v,'r) Insert_many.ist
  type ('k,'v,'r) delete_state = ('k,'v,'r) Delete2.delete_state

  (* isa doesn't export type abbrevs *)
  type ('k,'r) rsplit_node = ('k,'r,unit) Searching_and_splitting.rsplit_node_ext
  type ('k,'r) rstack = ('k,'r) rsplit_node list
  type ('k,'r) rstk = ('k,'r) rstack


  (** Leaf stream state. Needed early for store_ops *)

  (* NOTE this type is made abstract in isa_export; it supports step,
     dest_LS_leaf, and lss_is_finished ops *)
  type ('k,'v,'r) ls_state = ('k,'v,'r) Leaf_stream.ls_state

  (* FIXME not included in ocamldoc for some reason... *)
  module Store_ops' = struct
    open Store_ops

    type ('k,'v,'r,'t) store_ops = ('k,'v,'r,'t,unit) Store_ops.store_ops_ext

    let mk_store_ops ~store_free ~store_read ~store_alloc : ('k,'v,'r,'t)store_ops =
      Store_ops_ext(store_read,store_alloc,store_free,())

    let dest_store_ops (store_ops:('k,'v,'r,'t)store_ops) = fun f ->
      f ~store_free:(store_free store_ops) ~store_read:(store_read store_ops)
        ~store_alloc:(store_alloc store_ops)
  end
  include Store_ops'

  open Monad



  module Small_step = struct

    (* find ---------------------------------------- *)

    (** Construct an initial "find state" given a key and a reference to
        a B-tree root. *)
    let  mk_find_state k r : ('k,'v,'r) find_state = Find.mk_find_state k r

    (** Small step the find state: take a find state and return an updated
        find state (in the monad). *)
    let find_step ~constants ~cmp ~store_ops : 'fs->('fs,'t) mm = (fun fs -> 
        Find.find_step (x_ps1 ~constants ~cmp) store_ops fs)

    (** Check whether we have reached a leaf. Returns the reference to the
        B-tree root (when [mk_find_state] was called), the key we are
        looking for (ditto), a reference to a leaf (that may contain the
        key... if any leaf contains the key, this leaf does) and a the list
        of (key,values) in that leaf. *)
    let dest_f_finished fs: ('r * 'k * 'r * 'kvs * ('k,'r) rstk) option = (
      Find.dest_f_finished fs 
      |> (function None -> None | Some  x -> Some (x5 x)))

    (*open Params2*)

    (* only check if we have access to the relevant r2t and spec_tree *)
    (* ASSUMES r2t ps <> None *)
    (** Wellformedness check. Assumes access to the "spec tree", the
        global state and the find state.  *)
    let wellformed_find_state ~r2t ~cmp : 'tree -> 't -> ('k,'v,'r) find_state -> bool = (
      fun t s fs -> 
        Find.wellformed_find_state 
          (x_cmp cmp) r2t t s fs)


    (* delete ---------------------------------------- *)

    (** Similar functionality to [mk_find_state] *)
    let mk_delete_state: 'k -> 'r -> ('k,'v,'r) delete_state = 
      Delete2.mk_delete_state

    let delete_step ~constants ~cmp ~store_ops : 'ds -> ('ds,'t) mm = 
      (fun ds -> Delete2.delete_step (x_ps1 ~constants ~cmp) store_ops ds)

    (** The result is a reference to the updated B-tree *)
    let dest_d_finished: ('k,'v,'r) delete_state->'r option = Delete2.dest_d_finished

    let wellformed_delete_state ~cmp ~constants ~r2t : 'tree->'t->'k->('k,'v,'r) delete_state->bool = (
      fun t s k ds -> 
        Delete2.wellformed_delete_state 
          (x_constants constants) (x_cmp cmp)
          r2t t s k ds)


    (* insert ---------------------------------------- *)

    let mk_insert_state: 'k->'v->'r->('k,'v,'r) insert_state = 
      Insert.mk_insert_state

    let insert_step ~cmp ~constants ~store_ops : 'is -> ('is,'t) mm = 
      (fun is -> Insert.insert_step (x_ps1 ~cmp ~constants) store_ops is)

    (** Result is a reference to the updated B-tree *)
    let dest_i_finished: ('k,'v,'r)insert_state -> 'r option = 
      Insert.dest_i_finished

    let wellformed_insert_state ~cmp ~constants ~r2t :'tree->'t->'k->'v->('k,'v,'r) insert_state->bool = (
      fun t s k v is ->
        Insert.wellformed_insert_state 
          (x_constants constants) (x_cmp cmp)
          r2t t s k v is)

    (* insert_many ---------------------------------------- *)

    let mk_im_state: 'k -> 'v -> ('k*'v) list -> 'r -> ('k,'v,'r) im_state = 
      Insert_many.mk_insert_state

    let im_step ~constants ~cmp ~store_ops : 'im -> ('im,'t) mm = 
      (fun is -> Insert_many.insert_step (x_ps1 ~constants ~cmp) store_ops is)

    let dest_im_finished: ('k,'v,'r)im_state -> ('r*('k*'v)list) option = 
      Insert_many.dest_i_finished
    (* no wf *)


    (* leaf stream ---------------------------------------- *)

    (** Given a reference to a B-tree root, construct a stream of leaves *)
    let mk_ls_state : 'r -> ('k,'v,'r) ls_state = Leaf_stream.mk_ls_state

    (** Step the leaf stream to the next leaf. If the leaf stream is
        finished (no more leaves), stepping will just return the leaf
        stream unchanged. So in the loop you need to check whether you have
        finished using [ls_is_finished]. FIXME here and elsewhere, staging *)
    let ls_step ~constants ~cmp ~store_ops ls 
      : (('k,'v,'r) ls_state,'t) mm = 
      Leaf_stream.lss_step (x_ps1 ~constants ~cmp) store_ops ls

    let _ = ls_step

    (** Return the (key,value) list at the current leaf in the stream. *)
    let ls_dest_leaf ls = Leaf_stream.dest_LS_leaf ls

    let ls_is_finished lss : bool = (lss |> Leaf_stream.lss_is_finished)

  end



  module Pre_map_ops = struct

    type ('k,'v,'r,'t) pre_map_ops = {
      (** NOTE the return value includes a reference to a leaf, not a
          reference to the updated B-tree... find does not alter the B-tree
      *)
      find_leaf: 'k -> 'r -> ('r*('k*'v)list*('k,'r)rstk,'t) mm;
      find: 'k -> 'r -> ('r * ('k*'v)list,'t) mm;
      insert: 'k -> 'v -> 'r -> ('r,'t) mm;
      insert_many: 'k -> 'v -> ('k*'v)list -> 'r -> ('r * ('k*'v)list,'t) mm;
      delete: 'k -> 'r -> ('r,'t) mm;
    }

    let mk_pre_map_ops ~find_leaf ~find ~insert ~insert_many ~delete =
      {find_leaf;find;insert;insert_many;delete}

    let dest_pre_map_ops r =
      let find_leaf,find,insert,insert_many,delete = 
        r.find_leaf,r.find,r.insert,r.insert_many,r.delete 
      in
      fun k -> k ~find_leaf ~find ~insert ~insert_many ~delete

  end
  include Pre_map_ops
      

  module Big_step = struct


    (** The order on keys. B-trees work with ordered keys. *)
    let cmp x : 'k -> 'k -> int = (x#cmp)

    (** Constants. See {!Constants} *)
    let constants x : constants = (x#constants)


    (** Iterate small-step map operations to provide big-step map
        operations. The important functions in this module are [find],
        [insert], [insert_many] and [delete] (together with the leaf stream
        big-step operations). *)


    (* used by store_to_map *)

    (* FIXME separate out wellformedness checking *)

    (* iterate small-step operations till finished ---------------------- *)

    module X = Small_step

    let step ~small_step ~dest fs =
      let rec step fs =
        match dest fs with
        | Some x -> return x
        | None -> small_step fs |> bind (fun fs -> step fs)
      in
      step fs


    (* find leaf -------------------------------------------------------- *)

    let find_leaf' (type k v r t) ~cmp ~constants ~store_ops ~(k:k) ~(r:r) = 
      let small_step = X.find_step ~constants ~cmp ~store_ops in
      let dest = X.dest_f_finished in
      (step ~small_step ~dest) (X.mk_find_state k r)

    let _ = find_leaf'

    open Params

    let find_leaf ~ps ~store_ops ~k ~r = 
      find_leaf' ~cmp:(cmp ps) ~constants:(constants ps) ~store_ops ~k ~r 
      |> fmap (fun ((r1:'r),(k:'k),(r2:'r),kvs,stk) -> (r2,kvs,stk))

    let _ = find_leaf


    (* find ---------------------------------------- *)

    let find' ~cmp ~constants ~store_ops ~(k:'k) ~(r:'r) = 
      find_leaf' ~cmp ~constants ~store_ops ~k ~r

    (** Find. Take a key, a pointer to the root of a B-tree, and the
        global state. Return the updated state, a reference to the leaf of
        the B-tree that possibly contains the key (or alternatively return
        an error). *)
    let find ~ps ~store_ops ~k ~r =
      find' ~cmp:(cmp ps) ~constants:(constants ps) ~store_ops ~k ~r 
      |> fmap (fun (_,_,r,kvs,_) -> (r,kvs))



    (* insert ---------------------------------------- *)

    let insert' ~cmp ~constants ~store_ops ~k ~v ~r = 
      let small_step = X.insert_step ~constants ~cmp ~store_ops in
      let dest = X.dest_i_finished in
      (step ~small_step ~dest) (X.mk_insert_state k v r)


    (** Insert. Take a key, a value, a reference (to the B-tree root) and
        a state and return an updated state, with a new reference to the
        root of the updated B-tree. *)
    let insert ~ps ~store_ops ~k ~v ~r = 
      insert' ~cmp:(cmp ps) ~constants:(constants ps) ~store_ops ~k ~v ~r  


    (* insert many ---------------------------------------- *)

    let im' ~cmp ~constants ~store_ops ~k ~v ~kvs ~r =
      let small_step = X.im_step ~constants ~cmp ~store_ops in
      let dest = X.dest_im_finished in
      (step ~small_step ~dest) (X.mk_im_state k v kvs r)


    (** Insert many. Take a key, value, and list of further key/values, a
        pointer to the B-tree root and a global state. Return the updated
        state, a new pointer to a B-tree root, and a list of key/values
        which could not be inserted into the same leaf as the first
        key/value. Typically this function is called in a loop till all kvs
        have been inserted. It is assumed faster than multiple inserts,
        although caching may invalidate this assumption. *)
    let insert_many ~ps ~store_ops ~(k:'k) ~(v:'v) ~kvs ~(r:'r) = 
      im' ~cmp:(cmp ps) ~constants:(constants ps) ~store_ops ~k ~v ~kvs ~r 

    let _ = insert_many


    (* delete ---------------------------------------- *)

    let delete' ~cmp ~constants ~store_ops ~(k:'k) ~(r:'r) = 
      let small_step = X.delete_step ~constants ~cmp ~store_ops in
      let dest = X.dest_d_finished in
      (step ~small_step ~dest) (X.mk_delete_state k r)


    (** Delete. Take a key and a reference to a B-tree root, and a global
        state. Return the updated state and a reference to the new root. *)
    let delete ~ps ~store_ops ~(k:'k) ~(r:'r) = 
      delete' ~cmp:(cmp ps) ~constants:(constants ps) ~store_ops ~k ~r 

    let _ = delete


    (* make pre_map_ops ---------------------------------------- *)

    open Store_ops

    (** Construct [pre_map_ops] using functions above. Takes a "parameters" object ps. *)
    let store_ops_to_pre_map_ops ~ps ~(store_ops:('k,'v,'r,'t)store_ops) = 
      dest_store_ops store_ops @@ 
      fun ~store_free ~store_read ~store_alloc ->
      let find_leaf=(fun (k:'k) (r:'r) -> find_leaf ~ps ~store_ops ~k ~r) in
      let find=(fun k r -> find ~ps ~store_ops ~k ~r) in
      let insert=(fun k (v:'v) r -> insert ~ps ~store_ops ~k ~v ~r) in
      let insert_many=(fun k v kvs r -> insert_many ~ps ~store_ops ~k ~v ~kvs ~r) in
      let delete=(fun k r -> delete ~ps ~store_ops ~k ~r) in
      Pre_map_ops.mk_pre_map_ops ~find_leaf ~find ~insert ~insert_many ~delete

    let _ = store_ops_to_pre_map_ops

  end

  (** The main functionality exported by the B-tree code: implement a
      map on top of a store *)
  (* NOTE we phrase it in this form so that we avoid types like
     store_ops that are dependent on the monad *)
  let store_ops_to_pre_map_ops ~ps ~store_free ~store_read ~store_alloc = 
    mk_store_ops ~store_free ~store_read ~store_alloc |> fun store_ops ->
    Big_step.store_ops_to_pre_map_ops ~ps ~store_ops |> fun map_ops ->
    fun f -> 
      f 
        ~find_leaf:map_ops.find_leaf ~find:map_ops.find ~insert:map_ops.insert 
        ~insert_many:map_ops.insert_many ~delete:map_ops.delete

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
