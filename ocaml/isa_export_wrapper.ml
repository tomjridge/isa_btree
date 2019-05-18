open Util.No_profiler

(** Wrap Isabelle-exported code in an OCaml-friendly interface *)

(** Control isabelle assert flag *)
module Isa_export_assert_flag = struct
  let _ = 
    Isa_export.assert_flag
    |> Tjr_global.register ~name:"Isa_export.assert_flag" 

  let enable_isa_checks () = Isa_export.assert_flag:=true
  let disable_isa_checks () = Isa_export.assert_flag:=false
end
include Isa_export_assert_flag

(* now wrap isabelle operations ------------------------------------- *)

(** {2 Misc} *)

(* open Tjr_monad.Types *)
(* open Constants_type *)
open Isa_export

let dest_Some x = match x with Some x -> x | _ -> failwith "dest_Some"

module Dnode_type = struct
  (** Recall [dnode] type *)
  type ('node,'leaf) dnode = ('node,'leaf) Disk_node.dnode = 
      Disk_node of 'node | Disk_leaf of 'leaf
end
include Dnode_type

(* leaf ops --------------------------------------------------------- *)

(** {2 Leaf operations} *)

module Leaf_ops_type = struct
  (** As Isabelle def. See \doc(doc:leaf_ops). *)
  type ('k,'v,'leaf) leaf_ops = {
    leaf_lookup: 'k -> 'leaf -> 'v option;
    leaf_insert: 'k -> 'v -> 'leaf -> 'leaf * 'v option;
    leaf_remove: 'k -> 'leaf -> 'leaf;
    leaf_length: 'leaf -> int;
    leaf_steal_right: 'leaf * 'leaf -> 'leaf * 'k * 'leaf;
    leaf_steal_left: 'leaf*'leaf -> 'leaf*'k*'leaf;
    leaf_merge: 'leaf * 'leaf -> 'leaf;
    split_large_leaf: int -> 'leaf -> 'leaf*'k*'leaf;
    dbg_leaf_kvs: 'leaf -> ('k*'v) list;
    dbg_leaf: 'leaf -> unit;
  }
end
include Leaf_ops_type

module Internal_leaf_impl = struct

  let make_leaf_ops ~k_cmp = 
    let map_ops = Tjr_poly_map.make_map_ops k_cmp in
    let leaf_lookup k l = 
      profile "ab" @@ fun () -> 
      map_ops.find_opt k l
    in
    let leaf_insert k v l = 
      profile "ae" @@ fun () -> 
      map_ops.find_opt k l |> fun v' ->
      map_ops.add k v l |> fun l -> (l,v')
    in
    let leaf_remove k l = 
      profile "ah" @@ fun () -> 
      map_ops.remove k l in
    let leaf_length l = 
      profile "aj" @@ fun () -> 
      map_ops.cardinal l in
    let dbg_leaf_kvs l = 
      profile "ak" @@ fun () -> 
      map_ops.bindings l in
    let leaf_steal_right (l1,l2) =
      profile "al" @@ fun () ->      
      map_ops.min_binding_opt l2 |> dest_Some |> fun (k,v) ->
      l2 |> map_ops.remove k |> map_ops.min_binding_opt |> dest_Some |> fun (k',_) ->
      l1 |> map_ops.add k v |> fun l1 ->
      (l1,k',l2)
    in
    let leaf_steal_left (l1,l2) =
      profile "am" @@ fun () ->      
      map_ops.max_binding_opt l1 |> dest_Some |> fun (k,v) ->
      l1 |> map_ops.remove k |> fun l1 ->
      l2 |> map_ops.add k v |> fun l2 ->
      (l1,k,l2)
    in
    let leaf_merge (l1,l2) = 
      profile "an" @@ fun () ->      
      map_ops.disjoint_union l1 l2 
    in
    let split_large_leaf i l1 = 
      profile "ao" @@ fun () ->      
      l1 |> map_ops.bindings |> Tjr_list.drop i |> fun binds -> 
      match binds with
      | [] -> failwith __LOC__
      | (k,v)::rest -> 
        l1 |> map_ops.split k |> fun (l1,_,l2) -> 
        l2 |> map_ops.add k v |> fun l2 ->
        (l1,k,l2)
    in
    (* by default, there is no debugging; override the dbg_leaf field to enable *)
    let dbg_leaf = fun l -> () in
    let kvs_to_leaf = fun kvs -> 
      profile "ap" @@ fun () ->      
      map_ops.of_bindings kvs in
    let leaf_to_kvs = fun l -> 
      profile "aq" @@ fun () ->      
      dbg_leaf_kvs l in
    let ops = ({ leaf_lookup; leaf_insert; leaf_remove; leaf_length; 
       leaf_steal_right; leaf_steal_left; 
       leaf_merge; split_large_leaf; dbg_leaf_kvs; dbg_leaf } : ('k,'v,('k,'v,unit)Tjr_poly_map.map) leaf_ops)
    in
    fun f -> f ~leaf_ops:ops ~kvs_to_leaf ~leaf_to_kvs

  let _ :
k_cmp:('k -> 'k -> int) ->
(leaf_ops:('k, 'v, ('k, 'v, unit) Tjr_poly_map.map) leaf_ops ->
 kvs_to_leaf:(('k * 'v) list -> ('k, 'v, unit) Tjr_poly_map.map) ->
 leaf_to_kvs:(('k, 'v, unit) Tjr_poly_map.map -> ('k * 'v) list) -> 'a) ->
'a
    = make_leaf_ops
    

end
open Internal_leaf_impl

type ('k,'v) _leaf_impl = ('k,'v,unit) Tjr_poly_map.map

(*
let make_leaf_ops ~k_cmp : ('k,'v,('k,'v)_leaf_impl) leaf_ops = 
  make_leaf_ops ~k_cmp 
*)

(* node ops --------------------------------------------------------- *)

(** {2 Node operations} *)

(* NOTE defn. in Isabelle *)
(* type ('k,'r,'node) node_ops' = ('k,'r,'node) Disk_node.node_ops *)

module Node_ops_type = struct
  (* As Isabelle defn. See \doc(doc:node_ops) *)
  type ('k,'r,'node) node_ops = {
    split_node_at_k_index: int -> 'node -> ('node*'k*'node);
    node_merge: 'node*'k*'node -> 'node;
    node_steal_right: 'node*'k*'node -> 'node*'k*'node;
    node_steal_left: 'node*'k*'node -> 'node*'k*'node;
    node_keys_length: 'node -> int;
    node_make_small_root: 'r*'k*'r -> 'node;
    node_get_single_r: 'node -> 'r;
    dbg_node_krs: 'node -> ('k list * 'r list);
    dbg_node: 'node -> unit
  }
end
include Node_ops_type

module Internal_node_impl = struct

  (* implement node ops using a map from option; see impl notes in \doc(doc:node_ops) *)

  (* None is less than any other lower bound; this corresponds to the
     "lowest" interval below k0 *)
  let rec key_compare k_cmp k1 k2 =
    match k1,k2 with 
    | None,None -> 0
    | None,_ -> -1
    | _,None -> 1
    | Some k1, Some k2 -> k_cmp k1 k2

  let make_node_ops (type k) ~(k_cmp:k -> k -> int) = 
    let map_ops = Tjr_poly_map.make_map_ops (key_compare k_cmp) in
    let make_node ks rs = 
      profile "bb" @@ fun () -> 
      assert(List.length rs = 1 + List.length ks);
      let ks = None::(List.map (fun x -> Some x) ks) in
      let krs = List.combine ks rs in
      map_ops.of_bindings krs
    in
    let _ = make_node in
    let split_node_at_k_index i n =   (* i counts from 0 *)
      profile "bc" @@ fun () -> 
      (* FIXME this is rather inefficient... is there a better way?
         without altering the map implementation? *)
      map_ops.bindings n |> fun krs -> 
      let ks,rs = List.split krs in
      let ks = List.tl ks |> List.map dest_Some in  (* drop None *)
      assert(
        let len = List.length ks in 
        let _ = 
          match i < len with
          | false -> Printf.printf "NOTE %s: %d %d\n%!" __LOC__ i len
          | true -> ()
        in
        i < len);
      let k = List.nth ks i in
      let r = map_ops.find_opt (Some k) n |> dest_Some in
      let (n1,_,n2) = map_ops.split (Some k) n in
      n2 |> map_ops.add None r |> fun n2 ->
      (n1,k,n2)
    in
    let node_merge (n1,k,n2) = 
      profile "bd" @@ fun () -> 
      n2 |> map_ops.find_opt None |> dest_Some |> fun r2 -> 
      n2 |> map_ops.remove None |> map_ops.add (Some k) r2 |> fun n2 ->
      map_ops.disjoint_union n1 n2
    in
    let node_steal_right (n1,k,n2) =
      profile "be" @@ fun () -> 
      n2 |> map_ops.find_opt None |> dest_Some |> fun r2 ->
      n2 |> map_ops.remove None |> fun n2 ->
      n1 |> map_ops.add (Some k) r2 |> fun n1 ->
      n2 |> map_ops.min_binding_opt |> dest_Some |> fun (k,_) ->
      k |> dest_Some |> fun k ->
      (n1,k,n2)
    in
    let node_steal_left (n1,k,n2) = 
      profile "bf" @@ fun () -> 
      n1 |> map_ops.max_binding_opt |> dest_Some |> fun (k,r) ->
      k |> dest_Some |> fun k ->
      n1 |> map_ops.remove (Some k) |> fun n1 ->
      n2 |> map_ops.add (Some k) r |> fun n2 ->
      (n1,k,n2)
    in
    let node_keys_length n = 
      profile "bg" @@ fun () -> 
      (map_ops.cardinal n) -1
    in
    let node_make_small_root (r1,k,r2) =
      profile "bh" @@ fun () -> 
      Printf.printf "Making small root\n%!";
      map_ops.empty |> map_ops.add None r1 |> map_ops.add (Some k) r2
    in
    let node_get_single_r n =
      profile "bi" @@ fun () -> 
      assert(map_ops.cardinal n = 1);
      map_ops.bindings n |> fun [(_,r)] -> r
    in
    let dbg_node_krs n = 
      profile "bj" @@ fun () -> 
      n |> map_ops.bindings |> List.split |> fun (ks,rs) ->
      (List.tl ks |> List.map dest_Some,rs)
    in
    let dbg_node = fun n -> () in
    let node_ops = 
      ({ split_node_at_k_index; node_merge; node_steal_right; node_steal_left; node_keys_length;
         node_make_small_root; node_get_single_r;
         dbg_node_krs; dbg_node
       } : (k,'v,(k option,'v,unit)Tjr_poly_map.map) node_ops)
    in
    let krs_to_node = fun (ks,rs) -> make_node ks rs in
    let node_to_krs = dbg_node_krs in
    fun f -> f ~node_ops ~krs_to_node ~node_to_krs
    
  let _ :
k_cmp:('a -> 'a -> int) ->
(node_ops:('a, 'v, ('a option, 'v, unit) Tjr_poly_map.map) node_ops ->
 krs_to_node:('a list * 'v list -> ('a option, 'v, unit) Tjr_poly_map.map) ->
 node_to_krs:(('a option, 'v, unit) Tjr_poly_map.map -> 'a list * 'v list) ->
 'b) ->
'b
    = make_node_ops

end
open Internal_node_impl

type ('k,'r) _node_impl = ('k option, 'r, unit) Tjr_poly_map.map

(* let make_node_ops ~k_cmp : ('k,'r,('k,'r)_node_impl)node_ops = make_node_ops ~k_cmp *)

(* frame_ops -------------------------------------------------------- *)

(** {2 Frame operations} *)

module Internal_bottom_or_top = struct
  type 'k or_top = 'k option

  type 'k or_bottom = 'k option
end
open Internal_bottom_or_top

type ('k,'r) segment = 'k or_bottom * 'r * ('k*'r) list * 'k or_top

(** See Isabelle defn. See \doc(doc:frame_ops) *)
type ('k,'r,'frame,'node) frame_ops = {
  split_node_on_key: 'r -> 'k -> 'node -> 'frame;
  midpoint: 'frame -> 'r;

  get_focus: 'frame -> ('k or_bottom * 'r * 'k or_top);
  get_focus_and_right_sibling: 'frame -> ('k or_bottom * 'r * 'k * 'r * 'k or_top) option;
  get_left_sibling_and_focus: 'frame -> ('k or_bottom * 'r * 'k * 'r * 'k or_top) option;
  replace: ('k,'r) segment -> ('k,'r) segment -> 'frame -> 'frame;
  frame_to_node: 'frame -> 'node;

  get_midpoint_bounds: 'frame -> ('k option * 'k option);
  backing_node_blk_ref: 'frame -> 'r;

  split_node_for_leaf_stream: 'r -> 'node -> 'frame;
  step_frame_for_leaf_stream: 'frame -> 'frame option;

  dbg_frame: 'frame -> unit;
}

(* FIXME maybe move elsewhere *)

module Internal_frame_impl = struct

  type ('k,'r,'node) frame = {
    midkey: 'k option;  (* really or_bottom; may be None *)
    midpoint: 'r;
    node: 'node;
    backing_node_blk_ref: 'r
  } [@@deriving to_yojson]

  let make_frame_ops (type k) ~(k_cmp:k->k->int) =
    let map_ops = Tjr_poly_map.make_map_ops (key_compare k_cmp) in
    Tjr_fs_shared.Map_with_key_traversal.make_ops ~map_ops @@ fun ~get_next_binding ~get_prev_binding ->
    (* map_ops is a map from 'k option *)
    let split_node_on_key backing_node_blk_ref k n = 
      profile "cb" @@ fun () -> 
      (* get the relevant key *)
      let midkey,midpoint = 
        n |> map_ops.find_last_opt (fun k' -> key_compare k_cmp k' (Some k) <= 0) |> function
        | None -> failwith "impossible: None is < Some k" 
        | Some (k,r) -> (k,r)
        (*
        map_ops.find_opt (Some k) n |> function
        | None -> get_prev_binding (Some k) n |> dest_Some |> fun (k,r) ->
                  (k,r)
        | Some r -> (Some k,(r:r))
           *)
      in
      { midkey; midpoint; backing_node_blk_ref; node=n }
    in
    let _ = split_node_on_key in
    let midpoint f = f.midpoint in
    let get_focus f = 
      profile "cc" @@ fun () -> 
      let k1 = f.midkey in
      let k2 = f.node |> get_next_binding f.midkey |> function 
        | None -> None 
        | Some (k,r) -> k
      in
      (k1,f.midpoint,k2)
    in
    let get_focus_and_right_sibling f =
      profile "cd" @@ fun () -> 
      let k1,r1 = f.midkey,f.midpoint in
      f.node |> get_next_binding f.midkey |> function
      | None -> None
      | Some (k2,r2) -> 
        let k2 = k2 |> dest_Some in
        (* NOTE as a hack, we just return None for k3, since it is never used... *)
        Some(k1,r1,k2,r2,None)
    in
    let get_left_sibling_and_focus f = 
      profile "ce" @@ fun () -> 
      f.node |> get_prev_binding f.midkey |> function
      | None -> None 
      | Some(k1,r1) ->
        let k2,r2 = f.midkey,f.midpoint in
        let k2 = k2 |> dest_Some in
        (* NOTE hack *)
        Some(k1,r1,k2,r2,None)
    in
    let replace (k,r,krs,_) (k',r',krs',_) f =
      profile "cf" @@ fun () -> 
      assert(key_compare k_cmp k k' = 0);
      f.node |> map_ops.add k' r' |> fun n ->
      (* remove old ks *)
      (krs,n) 
      |> Tjr_list.iter_opt (fun (krs,n) ->
          match krs with 
          | [] -> None
          | (k,r)::krs ->
            n |> map_ops.remove (Some k) |> fun n -> Some(krs,n))
      |> snd
      (* add new krs *)
      |> fun n ->
      (krs',n) 
      |> Tjr_list.iter_opt (fun (krs,n) -> 
          match krs with
          | [] -> None
          | (k,r)::krs ->
            n |> map_ops.add (Some k) r |> fun n -> Some(krs,n))
      |> snd
      |> fun node ->
      { f with node }
    in
    let frame_to_node f = f.node in
    let get_midpoint_bounds f = 
      profile "cg" @@ fun () -> 
      let l : k option = f.midkey in
      let u = f.node |> get_next_binding f.midkey |> function
        | None -> None
        | Some (k,r) -> (k:k option)
      in
      (l,u)
    in
    let backing_node_blk_ref f = f.backing_node_blk_ref in
    let split_node_for_leaf_stream r n = 
      profile "ch" @@ fun () -> 
      let midkey = None in
      let midpoint = map_ops.min_binding_opt n |> function
        | None -> Printf.sprintf "impossible %s" __LOC__ |> failwith
        | Some (k,r) -> 
          assert(k=None);
          r
      in
      { midkey; midpoint; node=n; backing_node_blk_ref=r }
    in
    let step_frame_for_leaf_stream f = 
      profile "ci" @@ fun () -> 
      f.node |> get_next_binding f.midkey |> function
      | None -> None
      | Some (k,r) -> Some {f with midkey=k; midpoint=r}
    in
    let dbg_frame = fun f -> () in
    { split_node_on_key; midpoint; get_focus; get_focus_and_right_sibling; 
      get_left_sibling_and_focus; replace; frame_to_node; get_midpoint_bounds;
      backing_node_blk_ref; split_node_for_leaf_stream;
      step_frame_for_leaf_stream; dbg_frame }
  ;;


  let _ :
k_cmp:('a -> 'a -> int) ->
('a, 'b, ('a, 'b, ('a, 'b) _node_impl) frame, ('a, 'b) _node_impl) frame_ops
    = make_frame_ops

  ;;
end
open Internal_frame_impl

(* make types appear slightly nicer by introducing aliases and restricting inferred type *)
type ('k,'r) _frame_impl = ('k,'r,('k,'r)_node_impl) frame

let make_frame_ops (type k r) 
    ~(k_cmp:k->k->int)  
  : (k,r,(k,r)_frame_impl,(k,r)_node_impl) frame_ops
  =
  make_frame_ops ~k_cmp 


(* store_ops -------------------------------------------------------- *)

(** {2 Store operations} *)

module Store_ops_type = struct
  type ('r,'dnode,'t) store_ops = {
    read: 'r -> ('dnode,'t) m;
    wrte: 'dnode -> ('r,'t) m;
    rewrite: 'r -> 'dnode -> ('r option, 't) m;
    free: 'r list -> (unit,'t) m
  }
end
include Store_ops_type

(* leaf stream ------------------------------------------------------ *)

(** {2 Leaf stream operations} *)


module Leaf_stream_ops_type = struct
  (** The type of operations on leaf streams. Note that [ls_leaf]
      always returns a leaf. So each step transitions from one leaf to
      the next. *)
  type ('k,'v,'r,'leaf_stream_state,'t) leaf_stream_ops = {
    make_leaf_stream: 'r -> ('leaf_stream_state,'t) m;
    ls_step: 'leaf_stream_state -> ('leaf_stream_state option,'t) m;
    ls_kvs: 'leaf_stream_state -> ('k*'v)list;
  }
end
include Leaf_stream_ops_type
    (* ls_leaf: 'leaf_stream_state -> 'leaf; *)

module Internal_leaf_stream_impl = struct
  
  (** We augment the basic Isabelle type with some extra information:
     the current leaf. This type is for debugging - you shouldn't need
     to access components. *)
  type ('r,'leaf,'frame) _t = { 
    leaf: 'leaf;
    isa_ls_state: ('r,'leaf,'frame)Isa_export.Leaf_stream_state.leaf_stream_state 
  }

  (* we need to repeatedly step the leaf state to the point that we
     hit a leaf and dest_LS_leaf <> None; INVARIANT every ls_state
     constructed or exposed here has dest_LS_leaf <> None; FIXME do we
     want to introduce a new type for this? *)

  
  (* FIXME there is a similarly named function in store_to_map - rename this one *)
  let make_leaf_stream_ops (type k v r leaf frame) ~monad_ops ~(leaf_kvs:leaf -> (k*v)list)  
      ~isa_ls_step_to_next_leaf 
    =
    let ( >>= ) = monad_ops.bind in
    let return = monad_ops.return in

    let dest_leaf = Isa_export.Leaf_stream_state.dest_LS_leaf in
    let is_finished = Isa_export.Leaf_stream_state.ls_is_finished in
    
    let next_leaf t1 : ((r,leaf,frame) _t option,'t) m = 
      match is_finished t1.isa_ls_state with
      | true -> return None
      | false -> (
          t1.isa_ls_state |> isa_ls_step_to_next_leaf >>= function
          | None -> return None
          | Some isa_ls_state ->
            dest_leaf isa_ls_state |> fun (Some leaf) -> 
            return (Some{leaf;isa_ls_state}))
    in
    let _ = next_leaf in
    
    let make_leaf_stream r : ((r,leaf,frame) _t,'t) m = 
      Isa_export.Leaf_stream_state.make_initial_ls_state r |> fun isa_ls_state ->
      match dest_leaf isa_ls_state with
      | None -> (
          isa_ls_step_to_next_leaf isa_ls_state >>= fun (Some isa_ls_state) -> 
          isa_ls_state |> dest_leaf |> fun (Some leaf) -> 
          return { leaf; isa_ls_state })
      | Some leaf -> return { leaf; isa_ls_state }
    in
    let ls_leaf t1 = t1.leaf in
    let ls_step t1 = next_leaf t1 in
    let ls_kvs t1 = t1.leaf |> leaf_kvs in
    {make_leaf_stream; ls_step; ls_kvs}



  (* util ---------------------- *)

  (** Get all (key,value) pairs from a leaf stream. Debugging only. *)
  let _all_leaves ~monad_ops ~leaf_stream_ops ~r : ('leaf list,'t) m = 
    let ( >>= ) = monad_ops.bind in
    let return = monad_ops.return in
    let {make_leaf_stream; ls_step; ls_kvs} = leaf_stream_ops in
    let rec loop leaves s =
      Isa_export.Leaf_stream_state.ls_is_finished s |> function
      | true -> return leaves
      | false -> 
        ls_step s >>= fun (Some s) -> loop (ls_kvs s::leaves) s
    in 
    r |> make_leaf_stream >>= fun s -> loop [] s


(*
  (** Utility: call [insert_many] in a loop. *)
  let insert_all ~monad_ops ~insert_many =
    let ( >>= ) = monad_ops.bind in
    let return = monad_ops.return in
    let rec loop k v kvs =
      insert_many k v kvs >>= (fun kvs' -> 
        match kvs' with
        | [] -> return ()
        | (k,v)::kvs -> loop k v kvs)
    in loop
*)

end

type ('k,'v,'r) _leaf_stream_impl = 
  ('r, ('k, 'v) _leaf_impl, ('k, 'r) _frame_impl) Internal_leaf_stream_impl._t


(* conversions isa<->ocaml ------------------------------------------ *)

(** {2 Conversions between Isabelle types and OCaml types} *)

module Internal_conversions = struct
  (* isa numbers:
     type nat = Nat of Big_int.big_int;;
     type int = Int_of_integer of Big_int.big_int;;
  *)
  let int2nat n = Arith.nat_of_integer (Big_int.big_int_of_int n) 
  let nat2bigint (Arith.Nat n) = n 
  let bigint2int = Big_int.int_of_big_int 
  let nat2int (n:Arith.nat) = n |> nat2bigint |> bigint2int 
  let int2isa i = Arith.Int_of_integer(Big_int.big_int_of_int i) 
  open Constants_type
  let cs2isa (cs:constants) = 
    Constants_and_size_types.make_constants 
      (int2nat cs.min_leaf_size) 
      (int2nat cs.max_leaf_size)
      (int2nat cs.min_node_keys)
      (int2nat cs.max_node_keys)
  let cmp2isa (f: 'k -> 'k -> int) = fun k1 k2 -> f k1 k2 |> int2isa 
end



(* pre-map operations ----------------------------------------------- *)

(** {2 Pre-map operations} *)

module Pre_map_ops_type = struct
  (** Pre-map ops, with an explicit root pointer *)
  type ('k,'v,'r,'leaf,'frame,'t) pre_map_ops = {
    leaf_lookup: 'k -> 'leaf -> 'v option;
    find: r:'r -> k:'k -> ('r * 'leaf * 'frame list,'t) m;
    insert: r:'r -> k:'k -> v:'v -> ('r option,'t) m;
    delete: r:'r -> k:'k -> ('r,'t) m;
  }
end
include Pre_map_ops_type


(* ------------------------------------------------------------------ *)
(** {2 Insert many} 

The semantics of this operation is: for a list of (k,v), the operation
inserts all kvs, and returns the updated root (or None to indicate the
tree was updated in place).

*) 

module Pre_insert_many_type = struct
  type ('k,'v,'r,'t) pre_insert_many_op = {
    insert_many: r:'r -> kvs:('k*'v)list -> (('k*'v)list * 'r option,'t) m
  }
end
include Pre_insert_many_type

(* make_find_insert_delete ------------------------------------------ *)


module Internal_make_pre_map_ops = struct
  (* NOTE the following fixes the types for leaves and nodes *)
  let  make_pre_map_ops_etc (type t) ~(monad_ops:t monad_ops) =
    let module Monad = struct
      type nonrec t = t
      type ('a,'t) mm = ('a,t) m 
      let bind ab a = monad_ops.bind a ab
      let return a = monad_ops.return a
      let fmap f a = a |> bind (fun a -> return (f a))
    end
    in
    let module M = Isa_export.Make(Monad) in
    let open Internal_conversions in
    let leaf_ops2isa leaf_ops  = 
      let { leaf_lookup; leaf_insert; leaf_remove; leaf_length;
            leaf_steal_right; leaf_steal_left;
            leaf_merge; split_large_leaf; dbg_leaf_kvs; dbg_leaf } = leaf_ops 
      in
      Isa_export.Disk_node.make_leaf_ops
        leaf_lookup 
        leaf_insert 
        leaf_remove
        (fun l -> leaf_length l |> int2nat)
        (fun (l1,l2) -> leaf_steal_right (l1,l2) |> fun (a,b,c) -> (a,(b,c)))
        (fun (l1,l2) -> leaf_steal_left (l1,l2) |> fun (a,b,c) -> (a,(b,c)))
        leaf_merge
        (fun n l -> split_large_leaf (nat2int n) l |> fun (a,b,c) -> (a,(b,c)))
        dbg_leaf_kvs
        dbg_leaf
    in
    let node_ops2isa node_ops = 
      let {split_node_at_k_index; node_merge; node_steal_right;
           node_steal_left; node_keys_length; node_make_small_root;
           node_get_single_r;dbg_node_krs; dbg_node} = node_ops 
      in
      Isa_export.Disk_node.make_node_ops
        (fun nat n -> split_node_at_k_index (nat2int nat) n |> fun (x,y,z) -> (x,(y,z)))
        (fun (a,(b,c)) -> node_merge (a,b,c))
        (fun (a,(b,c)) -> node_steal_right (a,b,c) |> fun (a,b,c) -> (a,(b,c)))
        (fun (a,(b,c)) -> node_steal_left (a,b,c) |> fun (a,b,c) -> (a,(b,c))) 
        (fun x -> x |> node_keys_length |> int2nat)
        (fun (a,(b,c)) -> node_make_small_root (a,b,c))
        node_get_single_r
        dbg_node_krs
        dbg_node
    in
    let frame_ops2isa frame_ops = 
      let { split_node_on_key; midpoint; get_focus;
            get_focus_and_right_sibling; get_left_sibling_and_focus;
            replace; frame_to_node; get_midpoint_bounds;
            backing_node_blk_ref; split_node_for_leaf_stream;
            step_frame_for_leaf_stream; dbg_frame } = frame_ops
      in
      let seg2isa (a,b,c,d) = (a,(b,(c,d))) in
      let isa2seg (a,(b,(c,d))) = (a,b,c,d) in
      Isa_export.Stacks_and_frames.make_frame_ops
        split_node_on_key
        midpoint
        (fun f -> get_focus f |> fun (a,b,c) -> (a,(b,c)))
        (fun f -> get_focus_and_right_sibling f |> function None -> None | Some(a,b,c,d,e) -> Some(a,(b,(c,(d,e)))))
        (fun f -> get_left_sibling_and_focus f |> function None -> None | Some(a,b,c,d,e) -> Some(a,(b,(c,(d,e)))))
        (fun seg1 seg2 -> replace (isa2seg seg1) (isa2seg seg2))
        frame_to_node
        get_midpoint_bounds
        backing_node_blk_ref
        split_node_for_leaf_stream
        step_frame_for_leaf_stream
        dbg_frame 
    in
    let store_ops2isa store_ops = 
      let {read;wrte;rewrite;free} = store_ops in
      M.Post_monad.make_store_ops read wrte rewrite free
    in
    fun ~cs ~k_cmp ~store_ops ~dbg_tree_at_r -> 
      make_leaf_ops ~k_cmp @@ fun ~leaf_ops:leaf_ops0 ~kvs_to_leaf ~leaf_to_kvs -> 
      make_node_ops ~k_cmp @@ fun ~node_ops:node_ops0 ~krs_to_node ~node_to_krs -> 
      let frame_ops0 = Internal_frame_impl.make_frame_ops ~k_cmp in
      let cs,k_cmp,leaf_ops,node_ops,frame_ops,store_ops = 
        (cs2isa cs),(cmp2isa k_cmp),(leaf_ops2isa leaf_ops0),(node_ops2isa node_ops0),(frame_ops2isa frame_ops0),(store_ops2isa store_ops)
      in
      let find  = 
        let find = M.Find.find frame_ops store_ops in
        fun ~(r:'r) ~(k:'k) -> find r k |> Monad.fmap (fun (a,(b,c)) -> (a,b,c))
      in
      let insert = 
        let insert = M.Insert.insert cs leaf_ops node_ops frame_ops store_ops dbg_tree_at_r in
        fun  ~(r:'r) ~(k:'k) ~(v:'v) -> insert r k v
      in
      let delete  =
        let delete = M.Delete.delete cs leaf_ops node_ops frame_ops store_ops dbg_tree_at_r in
        fun ~(r:'r) ~(k:'k) -> delete r k
      in
      let leaf_stream_ops = 
        let open M.Leaf_stream in
        Internal_leaf_stream_impl.make_leaf_stream_ops ~monad_ops ~leaf_kvs:leaf_to_kvs ~isa_ls_step_to_next_leaf:(ls_step_to_next_leaf frame_ops store_ops)
      in
      let _ = leaf_stream_ops in
      let leaf_lookup = leaf_ops0.leaf_lookup in
      let pre_map_ops = {leaf_lookup;find;insert;delete} in
      let pre_insert_many_op = 
        (* let im_step = M.Insert_many.im_step cs k_cmp leaf_ops node_ops frame_ops store_ops in *)
        let insert_many = M.Insert_many.insert_many cs k_cmp leaf_ops node_ops frame_ops store_ops in 
        let insert_many ~r ~kvs = 
          match kvs with 
          [] -> Monad.return ([],None)
          | (k,v)::kvs -> insert_many r k v kvs 
        in
        { insert_many }
      in
      fun f -> f
        ~pre_map_ops
        ~pre_insert_many_op
        ~leaf_stream_ops
        ~leaf_ops:leaf_ops0
        ~node_ops:node_ops0
        ~frame_ops:frame_ops0
        ~kvs_to_leaf
        ~leaf_to_kvs
        ~krs_to_node
        ~node_to_krs
      
  let _ :
    monad_ops:'a monad_ops ->
cs:Constants_type.constants ->
k_cmp:('k -> 'k -> int) ->
store_ops:('r,
           (('k or_top, 'r, unit) Tjr_poly_map.map,
            ('k, 'v, unit) Tjr_poly_map.map)
           dnode, 'a)
          store_ops ->
dbg_tree_at_r:('r -> (unit, 'a) m) ->
(pre_map_ops:('k, 'v, 'r, ('k, 'v, unit) Tjr_poly_map.map,
              ('k, 'r, ('k or_top, 'r, unit) Tjr_poly_map.map) frame, 'a)
             pre_map_ops ->
 pre_insert_many_op:('k, 'v, 'r, 'a) pre_insert_many_op ->
 leaf_stream_ops:('k, 'v, 'r,
                  ('r, ('k, 'v, unit) Tjr_poly_map.map,
                   ('k, 'r, ('k or_top, 'r, unit) Tjr_poly_map.map) frame)
                  Internal_leaf_stream_impl._t, 'a)
                 leaf_stream_ops ->
 leaf_ops:('k, 'v, ('k, 'v, unit) Tjr_poly_map.map) leaf_ops ->
 node_ops:('k, 'r, ('k or_top, 'r, unit) Tjr_poly_map.map) node_ops ->
 frame_ops:('k, 'r, ('k, 'r, ('k or_top, 'r, unit) Tjr_poly_map.map) frame,
            ('k or_top, 'r, unit) Tjr_poly_map.map)
           frame_ops ->
 kvs_to_leaf:(('k * 'v) list -> ('k, 'v, unit) Tjr_poly_map.map) ->
 leaf_to_kvs:(('k, 'v, unit) Tjr_poly_map.map -> ('k * 'v) list) ->
 krs_to_node:('k list * 'r list -> ('k or_top, 'r, unit) Tjr_poly_map.map) ->
 node_to_krs:(('k or_top, 'r, unit) Tjr_poly_map.map -> 'k list * 'r list) ->
 'b) ->
'b
    = make_pre_map_ops_etc

end
open Internal_make_pre_map_ops



(** {2 Recap, packaging and export}  *)

(** Finally, redeclare make_find_insert_delete, hiding the internal
   types as much as possible. If you need access to the implementations, use the {!Internal_make_ops} module above. *)

module Node_leaf_conversions_type = struct
  (** Type for converting nodes and leaves into lists of k,v,r *)
  type ('k,'v,'r,'node,'leaf) node_leaf_conversions = {
    node_to_krs: 'node -> ('k list * 'r list);
    leaf_to_kvs: 'leaf -> ('k*'v) list;
    krs_to_node: ('k list * 'r list) -> 'node;
    kvs_to_leaf: ('k*'v)list -> 'leaf
  }
end
open Node_leaf_conversions_type


module Internal_export : sig
  type ('k,'r) node_impl
  type ('k,'v) leaf_impl
  val node_leaf_conversions: k_cmp:('k -> 'k -> int) -> ('k,'v,'r,('k,'r) node_impl,('k,'v) leaf_impl)node_leaf_conversions
  type ('k,'v,'r) dnode_impl = (('k,'r) node_impl, ('k,'v) leaf_impl)dnode
  type ('k,'r) frame_impl 
  type ('k,'v,'r) leaf_stream_impl

  (** The [isa_btree] type is what is exported by the make function; use the projections such as pre_map_ops to break this down *)
  type ('k,'v,'r,'t) isa_btree
(** Internal impl: {%html:<pre>
  type ('k,'v,'r,'a) isa_btree = 
    ('k, 'v, 'r, ('k, 'v) leaf_impl, ('k, 'r) frame_impl, 'a) pre_map_ops 
    * ('r, ('k,'v)leaf_impl, ('k,'v,'r) leaf_stream_impl, 'a) leaf_stream_ops 
    * ('k, 'v, ('k, 'v) leaf_impl) leaf_ops 
    * ('k, 'r, ('k, 'r) node_impl) node_ops
    * ('k, 'r, ('k, 'r) frame_impl, ('k,'r) node_impl) frame_ops 
    * (('k * 'v) list -> ('k, 'v) leaf_impl)
    * ('k list * 'r list -> ('k,'r) node_impl)
</pre>%}*)


  val make_isa_btree : 
    monad_ops:'a monad_ops ->
    cs:Constants.constants ->
    k_cmp:('k -> 'k -> int) ->
    store_ops:('r, (('k, 'r) node_impl, ('k, 'v) leaf_impl) dnode, 'a)
        store_ops ->
    dbg_tree_at_r:('r -> (unit, 'a) m) ->
    ('k,'v,'r,'a)isa_btree
(** Prettier type (essentially [store_ops -> isa_btree]): {%html:
<pre>
    monad_ops:'a monad_ops ->
    cs:constants ->
    k_cmp:('k -> 'k -> int) ->
    store_ops:('r, (('k, 'r) node_impl, ('k, 'v) leaf_impl) dnode, 'a) store_ops ->
    dbg_tree_at_r:('r -> (unit, 'a) m) ->
    ('k,'v,'r,'a)isa_btree
</pre> %} *)

  val pre_map_ops: ('k,'v,'r,'a) isa_btree -> 
    ('k, 'v, 'r, ('k, 'v) leaf_impl, ('k, 'r) frame_impl, 'a) pre_map_ops 

  val pre_insert_many_op : ('k,'v,'r,'a) isa_btree -> 
    ('k,'v,'r,'a) pre_insert_many_op

  val leaf_stream_ops: ('k,'v,'r,'a) isa_btree -> 
    ('k,'v,'r, ('k,'v,'r) leaf_stream_impl, 'a) leaf_stream_ops

(*
  val pre_insert_many_op: ('k,'v,'r,'a) isa_btree -> 
(('k, 'v, 'r, ('k, 'v) _leaf_impl,
                      ('k, 'r, ('k, 'r) _node_impl) frame)
                     Insert_state.insert_state * ('k * 'v) list ->
                     (('k, 'v, 'r, ('k, 'v) _leaf_impl,
                       ('k, 'r, ('k, 'r) _node_impl) frame)
                      Insert_state.insert_state * ('k * 'v) list, 'a)
                     m)    
*)

(* FIXME do we have to expose these?
  val leaf_ops: ('k,'v,'r,'a) isa_btree -> 
    ('k, 'v, ('k, 'v) leaf_impl) leaf_ops

  val node_ops:  ('k,'v,'r,'a) isa_btree -> 
    ('k, 'r, ('k, 'r) node_impl) node_ops
*)


  val leaf_to_kvs : ('k,'v,'r,'a) isa_btree -> 
    ('k, 'v) leaf_impl -> ('k * 'v) list

(*
  val kvs_to_leaf : ('k,'v,'r,'a) isa_btree -> 
    (('k * 'v) list -> ('k, 'v) leaf_impl)

  val krs_to_node : ('k,'v,'r,'a) isa_btree -> 
    ('k list * 'r list -> ('k,'r) node_impl)
*)
end = struct
  type ('k,'r) node_impl = ('k,'r)_node_impl
  type ('k,'v) leaf_impl = ('k,'v)_leaf_impl
      
  type ('k,'v,'r) dnode_impl = (('k,'r) node_impl, ('k,'v) leaf_impl)dnode
  type ('k,'r) frame_impl = ('k,'r)_frame_impl
  type ('k,'v,'r) leaf_stream_impl = ('k,'v,'r)_leaf_stream_impl

  type ('k,'v,'r,'a) isa_btree = 
(* a *)    ('k, 'v, 'r, ('k, 'v) leaf_impl, ('k, 'r) frame_impl, 'a) pre_map_ops 
(* b *)    * ('k, 'v, 'r, ('k,'v,'r)leaf_stream_impl, 'a) leaf_stream_ops
(* c *)    * ('k, 'v, ('k, 'v) leaf_impl) leaf_ops 
(* d *)    * ('k, 'r, ('k, 'r) node_impl) node_ops
(* e *)    * ('k, 'r, ('k, 'r) frame_impl, ('k,'r) node_impl) frame_ops 
(* f *)    * (('k * 'v) list -> ('k, 'v) leaf_impl)
(* g *)    * (('k, 'v) leaf_impl -> ('k * 'v) list)
(* h *)    * ('k list * 'r list -> ('k,'r) node_impl)
(* i *)    * (('k,'r) node_impl -> 'k list * 'r list)
(* j *)    * ('k, 'v, 'r, 'a) pre_insert_many_op    

  let make_isa_btree ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r : ('k,'v,'r,'a) isa_btree = 
    make_pre_map_ops_etc ~monad_ops ~cs ~k_cmp ~store_ops ~dbg_tree_at_r
    @@ fun ~pre_map_ops
      ~pre_insert_many_op
        ~leaf_stream_ops
        ~leaf_ops
        ~node_ops
        ~frame_ops
        ~kvs_to_leaf
        ~leaf_to_kvs
        ~krs_to_node
        ~node_to_krs ->
    (pre_map_ops,leaf_stream_ops,leaf_ops,node_ops,frame_ops,kvs_to_leaf,leaf_to_kvs,krs_to_node,node_to_krs,pre_insert_many_op)

  let node_leaf_conversions ~k_cmp = 
    Internal_node_impl.make_node_ops ~k_cmp @@  fun ~node_ops ~krs_to_node ~node_to_krs ->
    Internal_leaf_impl.make_leaf_ops ~k_cmp @@  fun ~leaf_ops ~kvs_to_leaf ~leaf_to_kvs ->
    (* FIXME remove profiling *)
    let node_to_krs n = profile "gb" @@ fun () -> node_to_krs n in
    let krs_to_node krs = profile "gc" @@ fun () -> krs_to_node krs in
    let leaf_to_kvs l = profile "gd" @@ fun () -> leaf_to_kvs l in
    let kvs_to_leaf kvs = profile "ge" @@ fun () -> kvs_to_leaf kvs in
    { node_to_krs; krs_to_node; leaf_to_kvs; kvs_to_leaf }


  let _ = make_pre_map_ops_etc
    
  let pre_map_ops = fun (a,b,c,d,e,f,g,h,i,j) -> a

  let leaf_stream_ops = fun (a,b,c,d,e,f,g,h,i,j) -> b

  let leaf_ops = fun (a,b,c,d,e,f,g,h,i,j) -> c

  let node_ops = fun (a,b,c,d,e,f,g,h,i,j) -> d

  let kvs_to_leaf = fun (a,b,c,d,e,f,g,h,i,j) -> f
    
  let leaf_to_kvs = fun (a,b,c,d,e,f,g,h,i,j) -> g
    
  let krs_to_node = fun (a,b,c,d,e,f,g,h,i,j) -> h

  let pre_insert_many_op = fun (a,b,c,d,e,f,g,h,i,j) -> j

end
include Internal_export

let wf_tree ~cs ~ms ~k_cmp = 
  let open Internal_conversions in
  Isa_export.Tree.wf_tree 
    (cs |> cs2isa)
    ms
    (k_cmp |> cmp2isa)

let _ = wf_tree
