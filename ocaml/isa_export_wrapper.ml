open Isa_btree_intf

(** Wrap Isabelle-exported code in an OCaml-friendly interface *)

(** Control isabelle assert flag *)
module Isa_export_assert_flag = struct
  let _ : bool ref = 
    Isa_export.assert_flag
    (* |> Global.register ~name:"Isa_export.assert_flag"  *)

  let enable_isa_checks () = Isa_export.assert_flag:=true
  let disable_isa_checks () = Isa_export.assert_flag:=false
  let _ : unit = disable_isa_checks ()  (* default is to disable *)
end
include Isa_export_assert_flag

open Isa_export

(** {2 Leaf stream implementation} *)

module Internal_leaf_stream_impl = struct
  (* open Leaf_node_frame_impls *)

  include Isa_btree_intf.Internal_leaf_stream_impl_t
(*
  (** We augment the basic Isabelle type with some extra information:
     the current leaf. This type is for debugging - you shouldn't need
     to access components. *)
  type ('r,'leaf,'frame) _t = { 
    leaf: 'leaf;
    isa_ls_state: ('r,'leaf,'frame)Isa_export.Leaf_stream_state.leaf_stream_state 
  }
*)

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


module Internal1 = struct
  open Internal_conversions

  let leaf_ops2isa leaf_ops  = 
    let { leaf_lookup; leaf_insert; leaf_remove; leaf_length;
          leaf_steal_right; leaf_steal_left;
          leaf_merge; split_large_leaf; leaf_to_kvs; kvs_to_leaf } = leaf_ops 
    in
    let dbg_leaf = fun l -> () in  (* FIXME *)
    Isa_export.Disk_node.make_leaf_ops
      leaf_lookup 
      leaf_insert 
      leaf_remove
      (fun l -> leaf_length l |> int2nat)
      (fun (l1,l2) -> leaf_steal_right (l1,l2) |> fun (a,b,c) -> (a,(b,c)))
      (fun (l1,l2) -> leaf_steal_left (l1,l2) |> fun (a,b,c) -> (a,(b,c)))
      leaf_merge
      (fun n l -> split_large_leaf (nat2int n) l |> fun (a,b,c) -> (a,(b,c)))
      leaf_to_kvs 
      dbg_leaf

  let dbg_node = fun n -> ()   (* FIXME *)

  let node_ops2isa node_ops = 
    let {split_node_at_k_index; node_merge; node_steal_right;
         node_steal_left; node_keys_length; node_make_small_root;
         node_get_single_r;node_to_krs;krs_to_node} = node_ops 
    in
    Isa_export.Disk_node.make_node_ops
      (fun nat n -> split_node_at_k_index (nat2int nat) n |> fun (x,y,z) -> (x,(y,z)))
      (fun (a,(b,c)) -> node_merge (a,b,c))
      (fun (a,(b,c)) -> node_steal_right (a,b,c) |> fun (a,b,c) -> (a,(b,c)))
      (fun (a,(b,c)) -> node_steal_left (a,b,c) |> fun (a,b,c) -> (a,(b,c))) 
      (fun x -> x |> node_keys_length |> int2nat)
      (fun (a,(b,c)) -> node_make_small_root (a,b,c))
      node_get_single_r
      node_to_krs
      dbg_node

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

  let wf_tree ~cs ~ms ~k_cmp = Isa_export.Tree.wf_tree (cs2isa cs) ms (cmp2isa k_cmp)
end


let wf_tree = Internal1.wf_tree


(** This is the most general implementation, where we just require k_cmp and map implementations *)
module Internal_make_with_k_maps = struct
  open Isa_btree_intf.Pre_btree_ops_type 
(*
  type ('k,'v,'r,'t,'leaf,'node,'leaf_stream) t1 = {
    find : r:'r -> k:'k -> ('r * 'leaf * ('k, 'r, 'node) frame list, 't) m;
    insert : r:'r -> k:'k -> v:'v -> ('r option, 't) m;
    delete: r:'r -> k:'k -> ('r, 't) m;
    leaf_stream_ops :
      ('k, 'v, 'r,
       'leaf_stream,
       't)
        leaf_stream_ops;
    pre_map_ops : ('k, 'v, 'r, 'leaf, ('k, 'r, 'node) frame, 't) pre_map_ops;
    insert_many : ('k, 'v, 'r, 't) insert_many_type;
    insert_all : ('k, 'v, 'r, 't) insert_all_type
  }
*)
  (* we want to have leaf and node ops available before we supply store_ops *)
  type ('k,'v,'r,'t,'leaf,'node,'leaf_stream,'store_ops) t2 = {
    (* leaf_lookup : 'k -> 'leaf -> 'v option; *)
    leaf_ops: ('k,'v,'leaf) leaf_ops;
    node_ops: ('k,'r,'node) node_ops;
    rest: store_ops:'store_ops -> ('k,'v,'r,'t,'leaf,'node,'leaf_stream) pre_btree_ops
  }

  open Leaf_node_frame_impls
         
  (* FIXME do we need k_cmp? can we just get it from k_map? *)
  let make_with_k_maps (type k v r t leaf node) ~monad_ops ~cs ~k_cmp ~k_map ~kopt_map ~dbg_tree_at_r =
    let leaf_ops0 = make_leaf_ops ~map_ops:k_map in    
    let node_ops0 = make_node_ops ~map_ops:kopt_map in
    let frame_ops0 = make_frame_ops ~map_ops:kopt_map in
    let rest = (fun ~store_ops -> 
      let module A = struct
        open Internal_conversions
        open Internal1

        module Monad = struct
          type nonrec t = t
          type ('a,'t) mm = ('a,t) m 
          let bind ab a = monad_ops.bind a ab
          let return a = monad_ops.return a
          let fmap f a = a |> bind (fun a -> return (f a))
        end

        let ( >>= ) = monad_ops.bind
        let return = monad_ops.return

        module M = Isa_export.Make(Monad) 


        (* this is in the monad *)
        let store_ops2isa store_ops = 
          let {read;wrte;rewrite;free} = store_ops in
          M.Post_monad.make_store_ops read wrte rewrite free

        let cs,k_cmp,leaf_ops,node_ops,frame_ops,store_ops = 
          (cs2isa cs),(cmp2isa k_cmp),(leaf_ops2isa leaf_ops0),
          (node_ops2isa node_ops0),(frame_ops2isa frame_ops0),
          (store_ops2isa store_ops)

        module type EXPORT = sig
          val find : r:r -> k:k -> (r * leaf * (k, r, node) Frame_type.frame list, t) m
          val insert : r:r -> k:k -> v:v -> (r option, t) Monad.mm
          val delete : r:r -> k:k -> (r, t) Monad.mm
          val leaf_stream_ops :
            (k, v, r,
             (r, leaf, (k, r, node) Frame_type.frame) Internal_leaf_stream_impl._t, 
             t)
              leaf_stream_ops
          val leaf_lookup : k -> leaf -> v option
          val pre_map_ops : (k, v, r, leaf, (k, r, node) Frame_type.frame, t) pre_map_ops
          val insert_many : (k, v, r, t) insert_many_type
          val insert_all : (k, v, r, t) insert_all_type
        end

        module Export : EXPORT = struct
          let find  = 
            let find = M.Find.find frame_ops store_ops in
            fun ~(r:r) ~(k:k) -> find r k |> Monad.fmap (fun (a,(b,c)) -> (a,(b:leaf),c))

          let insert = 
            let insert = M.Insert.insert cs leaf_ops node_ops frame_ops store_ops dbg_tree_at_r in
            fun  ~(r:r) ~(k:k) ~(v:v) -> (insert r k v : (r option,t)Monad.mm)

          let delete  =
            let delete = M.Delete.delete cs leaf_ops node_ops frame_ops store_ops dbg_tree_at_r in
            fun ~(r:r) ~(k:k) -> (delete r k : (r,t)Monad.mm)

          let leaf_stream_ops = 
            let open M.Leaf_stream in
            Internal_leaf_stream_impl.make_leaf_stream_ops ~monad_ops ~leaf_kvs:leaf_ops0.leaf_to_kvs ~isa_ls_step_to_next_leaf:(ls_step_to_next_leaf frame_ops store_ops)


          let leaf_lookup = leaf_ops0.leaf_lookup 

          let pre_map_ops = {leaf_lookup;find;insert;delete} 

          let insert_many =
            let insert_many = M.Insert_many.insert_many cs k_cmp leaf_ops node_ops frame_ops store_ops in 
            let insert_many = fun ~(r:r) ~(k:k) ~(v:v) ~kvs -> insert_many r k v kvs in
            { insert_many }

          let insert_all = 
            (* let im_step = M.Insert_many.im_step cs k_cmp leaf_ops node_ops frame_ops store_ops in *)
            let insert_many = M.Insert_many.insert_many cs k_cmp leaf_ops node_ops frame_ops store_ops in 
            (* let iter_m = iter_m ~monad_ops in *)
            let insert_all ~r ~kvs = 
              (r,kvs) |> 
              iter_k  (fun ~k:kont (r,kvs) -> 
                  match kvs with 
                  | [] -> return r
                  | (k,v)::kvs -> (
                      insert_many r k v kvs >>= fun (kvs,r') -> 
                      match r' with
                      | None -> kont (r,kvs)
                      | Some r' -> kont (r',kvs)))
              >>= fun r' -> return r'  (* NOTE may return the original r *)
            in
            let _ = insert_all in
            { insert_all }
        end
      end
      in
      A.Export.{
        find;insert;delete;leaf_stream_ops;leaf_ops=leaf_ops0; node_ops=node_ops0;
        pre_map_ops;insert_many;insert_all})
    in
    { leaf_ops=leaf_ops0; node_ops=node_ops0; rest }
end
include Internal_make_with_k_maps

let make_with_k_maps 
: monad_ops:'a monad_ops ->
cs:Constants_type.constants ->
k_cmp:('b -> 'b -> int) ->
k_map:('b, 'c, 'd) Leaf_node_frame_map_ops_type.map_ops ->
kopt_map:('b option, 'e, 'f) Leaf_node_frame_map_ops_type.map_ops ->
dbg_tree_at_r:('e -> (unit, 'a) m) ->
('b, 'c, 'e, 'a, 'd, 'f,
 ('e, 'd, ('b, 'e, 'f) frame)
 Isa_btree__Isa_btree_intf.Internal_leaf_stream_impl_t._t,
 ('e, ('f, 'd) dnode, 'a) store_ops)
t2
= make_with_k_maps



(* open Isa_btree_intf.Pre_btree_ops_type *)

(*
(** The advantage of this interface is that we provide the types of the k_map and kopt_map from the "outside", thereby avoiding type generativity issues. *)
module Internal_make_with_kargs = struct
  type ('a,'b,'c) k_args = {
    k_cmp: 'a;
    k_map: 'b;
    kopt_map: 'c;
  }


  (** {%html:<pre>
monad_ops:'t monad_ops ->
cs:Constants_type.constants ->
k_args:('k -> 'k -> int, ('k, 'v, 'leaf) Leaf_node_frame_impls.map_ops,
        ('k option, 'r, 'node) Leaf_node_frame_impls.map_ops)
       k_args ->
dbg_tree_at_r:('r -> (unit, 't) m) ->
store_ops:('r, ('node, 'leaf) dnode, 't) store_ops ->
('k, 'v, 'r, 't, 'leaf, 'node,
 ('r, 'leaf, ('k, 'r, 'node) Frame_type.frame) Internal_leaf_stream_impl._t)
pre_btree_ops
      </pre> %}
  *)
  let make_with_kargs ~monad_ops ~cs ~k_args ~store_ops 
    : ('k,'v,'r,'t,'leaf,'node,'leaf_stream)pre_btree_ops 
    = 
    let dbg_tree_at_r = fun _ -> monad_ops.return () in
    let { k_cmp; k_map; kopt_map } = k_args in
    make_with_k_maps ~monad_ops ~cs ~k_cmp ~k_map ~kopt_map ~dbg_tree_at_r ~store_ops

  let _ = make_with_kargs
end


include Internal_make_with_kargs
*)

(*
module Internal_make_with_comparators = struct
  open Isa_btree_util
  let make_with_comparators 
    (type k k_cmp kopt_cmp)
    ~monad_ops
    ~cs
    ~(k_cmp:(k,k_cmp)Base.Map.comparator)
    ~(kopt_cmp:(k option,kopt_cmp)Base.Map.comparator)
    ~store_ops
    =
    let k_map = comparator_to_map_ops k_cmp in
    let kopt_map = comparator_to_map_ops kopt_cmp in
    let k_cmp =
      let (module A) = k_cmp in
        A.comparator.compare
    in
    let dbg_tree_at_r = fun _ -> monad_ops.return () in
    make_with_k_maps ~monad_ops ~cs ~k_cmp ~k_map ~kopt_map ~dbg_tree_at_r ~store_ops
                     
  let _ = make_with_comparators
end

include Internal_make_with_comparators
*)
(* include Isa_btree_util *)

