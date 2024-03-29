(** {2 Leaf operations}

For generality, these use an arbitrary "map_ops". Typically we use
   Base.Map to implement these underlying maps.

 *)

open Isa_btree_intf
open Leaf_node_frame_map_ops_type
open Profilers

module Internal_leaf_impl = struct

  let {mark; time_thunk; _ } = leaf_profiler

  let 
    [ll   ; li   ; lr   ; llen   ; lsr_  ; lsl_  ; lm   ; lspl   ; l2kvs   ; kvs2l] =
    ["ll" ; "li" ; "lr" ; "llen" ; "lsr" ; "lsl" ; "lm" ; "lspl" ; "l2kvs" ;"kvs2l"] 
    |> List.map intern

  let profile = time_thunk

  let rec drop n xs = 
    if n = 0 then xs else drop (n-1) (List.tl xs)

  let make_leaf_ops (type k v t) ~(map_ops:(k,v,t)map_ops) = 
    let leaf_lookup k l = 
      profile ll @@ fun () -> 
      map_ops.find_opt k l
    in
    let leaf_insert k v l = 
      profile li @@ fun () -> 
      let old = ref None in
      let l' = 
        map_ops.update 
          k 
          (function
            | None -> Some v
            | Some v' -> 
              old:=Some v';
              Some v)
          l
      in
      l',!old
    in
    let leaf_remove k l = 
      profile lr @@ fun () -> 
      map_ops.remove k l in
    let leaf_length l = 
      profile llen @@ fun () -> 
      map_ops.cardinal l in
    let leaf_steal_right (l1,l2) =
      (* Printf.printf "leaf_steal_right\n"; *)
      profile lsr_ @@ fun () -> 
      map_ops.min_binding_opt l2 |> dest_Some |> fun (k,v) ->
      l2 |> map_ops.remove k |> fun l2 -> 
      l2 |> map_ops.min_binding_opt |> dest_Some |> fun (k',_) ->
      l1 |> map_ops.add k v |> fun l1 ->
      (l1,k',l2)
    in
    let leaf_steal_left (l1,l2) =
      profile lsl_ @@ fun () ->      
      map_ops.max_binding_opt l1 |> dest_Some |> fun (k,v) ->
      l1 |> map_ops.remove k |> fun l1 ->
      l2 |> map_ops.add k v |> fun l2 ->
      (l1,k,l2)
    in
    let leaf_merge (l1,l2) = 
      profile lm @@ fun () ->      
      map_ops.disjoint_union l1 l2 
    in
    let split_large_leaf i l1 = 
      profile lspl @@ fun () ->      
      (*      Printf.printf "split_large_leaf: i=%d len=%d"
        i
        (map_ops.cardinal l1);*)
      l1 |> map_ops.bindings |> drop i |> fun binds -> 
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
      profile kvs2l @@ fun () ->
      map_ops.of_bindings kvs in
    let leaf_to_kvs = fun l -> 
      profile l2kvs @@ fun () ->      
      map_ops.bindings l in
    let ops = ({ leaf_lookup; leaf_insert; leaf_remove; leaf_length; 
       leaf_steal_right; leaf_steal_left; 
       leaf_merge; split_large_leaf; leaf_to_kvs; kvs_to_leaf })
    in
    ops


  let test_leaf_impl () = 
    let k_cmp: int -> int -> int = Stdlib.compare in
    let module Comp = Isa_btree_util.Internal_make_map_ops(struct type k = int let k_cmp = k_cmp end) in
    let open Comp in
    let map_ops = Tjr_map.With_base_as_record.make_map_ops k_comparator in
    let ops = make_leaf_ops ~map_ops in
    let kvs0 = from_upto 1 20 |> List.map (fun x -> (x,2*x)) in
    let l0 = kvs0 |> ops.kvs_to_leaf in
    let l1,k,l2 = ops.split_large_leaf 10 l0 in
    (* Printf.printf "%s k is %d\n%!" __LOC__ k; *)
    assert(k=11);
    let xs,ys = ops.leaf_to_kvs l1,ops.leaf_to_kvs l2 in
    assert(xs@ys=kvs0);
    assert(List.hd ys = (k,2*k));
    let (l1',k',l2') = ops.leaf_steal_right (l1,l2) in
    assert(k'=12);
    let xs',ys' = ops.leaf_to_kvs l1',ops.leaf_to_kvs l2' in
    let zs = xs'@ys' |> List.map fst |> List.map string_of_int |> String.concat "," in
    (* Printf.printf "%s %s\n%!" __LOC__ zs; *)
    assert(xs'@ys'=kvs0);
    ()

  (* let _ : unit -> unit = Global.register ~name:(__MODULE__^".test_leaf_impl") test_leaf_impl *)


end



(** {2 Node operations} *)

module Internal_node_impl = struct

  (* implement node ops using a map from option; see impl notes in
     \doc(doc:node_ops) *)

  let { time_thunk; _ } = node_profiler
  let profile = time_thunk

  let 
    [n1;n2;n3;n4;n5;n6;n7;n8;n9]
    =  ["n1";"n2";"n3";"n4";"n5";"n6";"n7";"n8";"n9"]
    |> List.map intern
      

  let make_node_ops (type k r t) ~(map_ops:(k option,r,t)map_ops) = 
    let make_node ks rs = 
      profile n1 @@ fun () -> 
      (* assert(List.length rs = 1 + List.length ks); *)

(* attempt at optimization; failed see test_btree_main.2019-05-19_19:06:49.log
      let b1 = None,List.hd rs in
      let rest = 
        (ks,List.tl rs,[])
        |> Tjr_list.iter_opt 
             (function
              | ([],[],acc) -> None
              | (k::ks,r::rs,acc) -> Some(ks,rs,(Some k,r)::acc)
              | _ -> failwith __LOC__)
        |> fun (_,_,acc) -> acc
      in              
*)
      let ks = None::(List.map (fun x -> Some x) ks) in
      Test.assert_(fun() -> 
          let b = List.length ks = List.length rs in
          let _ : unit = 
            if not b then  Printf.printf "%s: lengths differ, %d %d \n%!" __LOC__ (List.length ks) (List.length rs)
          in
          assert(b));
      let krs = List.combine ks rs in
      map_ops.of_bindings krs
    in
    let _ = make_node in

    (* check a node has a binding for None *)
    let check_node_has_none_binding n = 
      assert(map_ops.min_binding_opt n |> function
        | None -> failwith __LOC__
        | Some(None,_) -> true
        | _ -> failwith __LOC__);
      ()
    in

    let check_node = check_node_has_none_binding in

    let split_node_at_k_index i n =   (* i counts from 0 *)
      profile n2 @@ fun () -> 
      (* FIXME this is rather inefficient... is there a better way?
         without altering the map implementation? *)
      map_ops.bindings n |> fun krs -> 
      let ks,rs = List.split krs in
      let ks = List.tl ks |> List.map dest_Some in  (* drop None *)
      assert(  (* FIXME use Test.assert_ or similar *)
        let len = List.length ks in 
        let _ : unit = 
          match i < len with
          | false -> Printf.printf "NOTE %s: %d %d\n%!" __LOC__ i len
          | true -> ()
        in
        i < len);
      let k = List.nth ks i in
      let r = map_ops.find_opt (Some k) n |> dest_Some in
      let (n1,_,n2) = map_ops.split (Some k) n in
      n2 |> map_ops.add None r |> fun n2 ->
      Test.check (fun () -> check_node n1;check_node n2);
      (n1,k,n2)
    in
    let node_merge (n1,k,n2) = 
      profile n3 @@ fun () -> 
      n2 |> map_ops.find_opt None |> dest_Some |> fun r2 -> 
      n2 |> map_ops.remove None |> map_ops.add (Some k) r2 |> fun n2 ->
      map_ops.disjoint_union n1 n2 |> fun n -> 
      Test.check (fun () -> check_node n);
      n
    in
    let node_steal_right (n1,k0,n2) =
      profile n4 @@ fun () -> 
      n2 |> map_ops.find_opt None |> dest_Some |> fun r ->
      n2 |> map_ops.remove None |> fun n2 ->
      n2 |> map_ops.min_binding_opt |> dest_Some |> fun (k',r') ->
      k' |> dest_Some |> fun k' ->
      n2 |> map_ops.remove (Some k') |> map_ops.add None r' |> fun n2 ->
      n1 |> map_ops.add (Some k0) r |> fun n1 ->
      Test.check (fun () -> check_node n1;check_node n2);
      (n1,k',n2)
    in
    let node_steal_left (n1,k0,n2) = 
      profile n5 @@ fun () -> 
      n1 |> map_ops.max_binding_opt |> dest_Some |> fun (k,r) ->
      k |> dest_Some |> fun k ->
      n1 |> map_ops.remove (Some k) |> fun n1 ->
      n2 |> map_ops.min_binding_opt |> dest_Some |> fun (k',r') -> 
      assert(k'=None);
      n2 |> map_ops.remove None |> fun n2 -> 
      n2 |> map_ops.add (Some k0) r' |> fun n2 ->
      n2 |> map_ops.add None r |> fun n2 -> 
      Test.check (fun () -> check_node n1;check_node n2);
      (n1,k,n2)
    in
    let node_keys_length n = 
      profile n6 @@ fun () -> 
      (map_ops.cardinal n) -1
    in
    let node_make_small_root (r1,k,r2) =
      profile n7 @@ fun () -> 
      (* Printf.printf "Making small root\n%!"; *)
      map_ops.empty |> map_ops.add None r1 |> map_ops.add (Some k) r2
    in
    let node_get_single_r n =
      profile n8 @@ fun () -> 
      assert(map_ops.cardinal n = 1);
      map_ops.bindings n |> fun [(_,r)] -> r
    in
    let node_to_krs n = 
      profile n9 @@ fun () -> 
      n |> map_ops.bindings |> List.split |> fun (ks,rs) ->
      assert(List.hd ks = None);
      (List.tl ks |> List.map dest_Some,rs)
    in
    let krs_to_node = fun (ks,rs) -> make_node ks rs in
    (* let dbg_node = fun n -> () in *)
    let node_ops = 
      ({ split_node_at_k_index; node_merge; node_steal_right;
         node_steal_left; node_keys_length; node_make_small_root;
         node_get_single_r; node_to_krs; krs_to_node
       })
    in
    node_ops

  let test_node_impl () = 
    let k_cmp: int -> int -> int = Stdlib.compare in
    let module Comp = Isa_btree_util.Internal_make_map_ops(struct type k = int let k_cmp = k_cmp end) in
    let open Comp in
    let map_ops = Tjr_map.With_base_as_record.make_map_ops kopt_comparator in
    let ops = make_node_ops ~map_ops in
    (* debugging *)
    let node_to_string n =
      let opt_to_string = function None -> "*" | Some k -> (string_of_int k) in
      n |> ops.node_to_krs |> fun (ks,rs) -> 
      let ks = "*"::(List.map string_of_int ks)  in
      List.combine ks rs 
      |> List.map (fun (k,v) -> (k^","^(string_of_int v)))
      |> String.concat ","
    in
    let krs0 = [1;2;3],[91;92;93;94] in
    let n0 = krs0 |> ops.krs_to_node in    
    let n1,k,n2 = ops.split_node_at_k_index 0 n0 in
    (* Printf.printf "%s k is %d\n%!" __LOC__ k; *)
    assert(k=1);
    let n3 = ops.node_merge (n1,k,n2) in
    assert(ops.node_to_krs n3 = krs0);
    let n1,k,n2 = ops.split_node_at_k_index 1 n0 in
    assert(k=2);
    (* steal right *)
    let n1,k,n2 = ops.node_steal_right (n1,k,n2) in
    assert(ops.node_merge(n1,k,n2) |> ops.node_to_krs = krs0);
    (* steal left *)
    let (n1,k,n2) = ops.split_node_at_k_index 1 n0 in
    let log s = Printf.printf "%s\n" s in
    log(Printf.sprintf "%d %s" __LINE__ (n1 |> node_to_string));
    log(Printf.sprintf "%d %d" __LINE__ k);
    log(Printf.sprintf "%d %s" __LINE__ (n2 |> node_to_string));
    log(Printf.sprintf "%d %s" __LINE__ (n3 |> node_to_string));
    let n1,k,n2 = ops.node_steal_left (n1,k,n2) in
    let n3 = ops.node_merge (n1,k,n2) in
    log(Printf.sprintf "%d %s" __LINE__ (n1 |> node_to_string));
    log(Printf.sprintf "%d %d" __LINE__ k);
    log(Printf.sprintf "%d %s" __LINE__ (n2 |> node_to_string));
    log(Printf.sprintf "%d %s" __LINE__ (n3 |> node_to_string));
    assert(n3 |> ops.node_to_krs = krs0);
    ()

  (* let _ : unit -> unit = Global.register ~name:(__MODULE__^".test_node_impl") test_node_impl *)
end


(** {2 Frame operations} *)

module Internal_frame_impl = struct

  open Isa_btree_intf.Frame_type

  let { time_thunk; _ } = frame_profiler
  let profile = time_thunk

  let 
    [f1;f2;f3;f4;f5;f6;f7;f8;f9]
    =  ["f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9"]
    |> List.map intern
  

  (* FIXME replace with iter_k *)
  let iter_opt (f:'a -> 'a option) = 
    let rec loop x = 
      match f x with
      | None -> x
      | Some x -> loop x
    in
    fun x -> loop x


  (* note that the map_ops is the map ops for the node type *)
  let make_frame_ops (type k r node) ~(map_ops:(k option,r,node)map_ops) =
    let split_node_on_key backing_node_blk_ref k n = 
      profile f1 @@ fun () -> 
      (* get the relevant key *)
      let midkey,midpoint = 
        n |> map_ops.closest_key `Less_or_equal_to (Some k) |> function
        | None -> failwith "impossible: None is < Some k" 
        | Some (k,r) -> (k,r)
      in
      { midkey; midpoint; backing_node_blk_ref; node=n }
    in
    let _ = split_node_on_key in
    let midpoint f = f.midpoint in
    let get_next_binding (k:k option) node : (k*r) option = 
      map_ops.closest_key `Greater_than k node |> function
      | None -> None
      | Some (None,_) -> failwith __LOC__  (* impossible *)
      (* NOTE that we know that None cannot be a key greater than some
         other key, and this means that the returned value could be
         plain k rather than map_ops.k *)
      | Some (Some k,v) -> Some (k,v)
      (* | Some (Some k,v) -> Some (Some k,v)  (\* NOTE guaranteed to be Some k *\) *)
    in
    let get_prev_binding (k:k option) node : (k option*r)option = 
      map_ops.closest_key `Less_than k node |> function
      | None -> None
      | Some(mk,v) -> Some(mk,v)
    in
    let _ = get_prev_binding in
    let get_focus f : k option * r * k option = 
      profile f2 @@ fun () -> 
      let k1 = f.midkey in
      let k2 = f.node |> get_next_binding f.midkey |> function 
        | None -> None 
        | Some (k,r) -> Some k
      in
      (k1,f.midpoint,k2)
    in
    let get_focus_and_right_sibling f =
      profile f3 @@ fun () -> 
      let k1,r1 = f.midkey,f.midpoint in
      f.node |> get_next_binding f.midkey |> function
      | None -> None
      | Some (k2,r2) -> 
        (* let k2 = k2 |> dest_Some in *)
        (* NOTE as a hack, we just return None for k3, since it is
           never used... *)
        Some(k1,r1,k2,r2,None)
    in
    let get_left_sibling_and_focus f = 
      profile f4 @@ fun () -> 
      f.node |> get_prev_binding f.midkey |> function
      | None -> None 
      | Some(k1,r1) ->
        let k2,r2 = f.midkey,f.midpoint in
        let k2 = k2 |> dest_Some in (* k2 can't be None if left sib *)
        (* NOTE None hack *)
        Some(k1,r1,k2,r2,None)
    in
    let replace (k,r,krs,_) (k',r',krs',_) f =
      profile f5 @@ fun () -> 
      assert(map_ops.k_cmp k k' = 0);
      f.node |> map_ops.add k' r' |> fun n ->
      (* remove old ks *)
      (krs,n) 
      |> iter_opt (fun (krs,n) ->
          match krs with 
          | [] -> None
          | (k,r)::krs ->
            n |> map_ops.remove (Some k) |> fun n -> Some(krs,n))
      |> snd
      (* add new krs *)
      |> fun n ->
      (krs',n) 
      |> iter_opt (fun (krs,n) -> 
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
      profile f6 @@ fun () -> 
      let l : k option = f.midkey in
      let u = f.node |> get_next_binding f.midkey |> function
        | None -> None
        | Some(k,r) -> (Some k:k option)
      in
      (l,u)
    in
    let backing_node_blk_ref f = f.backing_node_blk_ref in
    let split_node_for_leaf_stream r n = 
      profile f7 @@ fun () -> 
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
      profile f8 @@ fun () -> 
      f.node |> get_next_binding f.midkey |> function
      | None -> None
      | Some (k,r) -> Some {f with midkey=(Some k); midpoint=r}
    in
    let dbg_frame = fun f -> () in
    { split_node_on_key; midpoint; get_focus; get_focus_and_right_sibling; 
      get_left_sibling_and_focus; replace; frame_to_node; get_midpoint_bounds;
      backing_node_blk_ref; split_node_for_leaf_stream;
      step_frame_for_leaf_stream; dbg_frame }
end

module Internal_ = struct
  let make_leaf_ops = Internal_leaf_impl.make_leaf_ops
  let make_node_ops = Internal_node_impl.make_node_ops
  let make_frame_ops = Internal_frame_impl.make_frame_ops


  (** Given a two comparators (k and kopt) we can construct leaf node and
      frame impls *)      

  let make_leaf_node_frame_ops_from_comparators ~k_cmp ~kopt_cmp = 
    let module A = struct
      let f (type a b) (x:('c1,'c2)ty_eq) : ((a,b,'c1)leaf_ops,(a,b,'c2)leaf_ops)ty_eq =
        let module X = struct
          type 'c t = (a,b,'c)leaf_ops
        end
        in
        let module A = Base.Type_equal.Lift(X) in
        A.lift x

      let f = f Isa_btree_intf.Internal_leaf_node.leaf_ty_eq |> Base.Type_equal.sym
      let _ = f

      let g (type a b) (x:('c1,'c2)ty_eq) : ((a,b,'c1)node_ops,(a,b,'c2)node_ops)ty_eq =
        let module X = struct
          type 'c t = (a,b,'c)node_ops
        end
        in
        let module A = Base.Type_equal.Lift(X) in
        A.lift x

      let g = g Isa_btree_intf.Internal_leaf_node.node_ty_eq |> Base.Type_equal.sym
      let _ = g
    end
    in
    let map_ops = Tjr_map.With_base_as_record.make_map_ops k_cmp in
    let leaf_ops = make_leaf_ops ~map_ops |> Base.Type_equal.conv A.f in
    let _ = leaf_ops in
    (* at this point, we would like to hide the Base.Map impl type via
       the type_equality from Isa_btree_intr.Internal_leaf_node;
       however, this is not straightforward: ('a, 'b, ('a, 'b, 'c)
       Base.Map.t) leaf_ops is not easily convertable into ('a, 'b,
       ('a, 'b, 'c) leaf) leaf_ops :( We seem to need to traverse all
       the operations, inserting conversion functions everywhere,
       which is horrible; fortunately, Base.Type_equal has a "lift3"
       functor which should do the trick *)
    let map_ops = Tjr_map.With_base_as_record.make_map_ops kopt_cmp in
    let node_ops = make_node_ops ~map_ops |> Base.Type_equal.conv A.g in
    let frame_ops = make_frame_ops ~map_ops in
    { leaf_ops; node_ops; frame_ops }

end
include Internal_

let make_leaf_node_frame_ops_from_comparators 
:k_cmp:('a, 'b) Base.Map.comparator ->
kopt_cmp:('c option, 'd) Base.Map.comparator ->
(('a, 'e, ('a, 'e, 'b) leaf) leaf_ops, ('c, 'f, ('c, 'f, 'd) node) node_ops,
 ('c, 'f, ('c, 'f, ('c option, 'f, 'd) Base.Map.t) frame,
  ('c option, 'f, 'd) Base.Map.t)
 frame_ops)
leaf_node_frame_ops
= Internal_.make_leaf_node_frame_ops_from_comparators

(*
sig
  val make_leaf_ops : map_ops:('a, 'b, 'c) map_ops -> ('a, 'b, 'c) leaf_ops
  val make_node_ops :
    map_ops:('a option, 'b, 'c) map_ops -> ('a, 'b, 'c) node_ops
  val make_frame_ops :
    map_ops:('a option, 'b, 'c) map_ops ->
    ('a, 'b, ('a, 'b, 'c) frame, 'c) frame_ops
end
*)

(*
include (Export : sig
  val make_leaf_ops : map_ops:('a, 'b, 'c) map_ops -> ('a, 'b, 'c) leaf_ops
  val make_node_ops :
    map_ops:('a option, 'b, 'c) map_ops -> ('a, 'b, 'c) node_ops
  val make_frame_ops :
    map_ops:('a option, 'b, 'c) map_ops ->
    ('a, 'b, ('a, 'b, 'c) frame, 'c) frame_ops
  val make_leaf_node_frame_ops_from_comparators :
    k_cmp:('a, 'b) Base.Map.comparator ->
    kopt_cmp:('c option, 'd) Base.Map.comparator ->
    (('a, 'e, ('a, 'e, 'b) leaf) leaf_ops,
     ('c, 'f, ('c, 'f, 'd) node) node_ops,
     ('c, 'f, ('c, 'f, ('c option, 'f, 'd) Base.Map.t) frame,
      ('c option, 'f, 'd) Base.Map.t)
     frame_ops)
    leaf_node_frame_ops
end)
*)
