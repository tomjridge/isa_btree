(** {2 Leaf operations} *)

open Isa_btree_intf

type ('k,'v,'t) map_ops = ('k,'v,'t) Tjr_map.With_base.map_ops

(*
module Internal_misc = struct
  (* None is less than any other lower bound; this corresponds to the
     "lowest" interval below k0 *)
  let rec key_compare k_cmp k1 k2 =
    match k1,k2 with 
    | None,None -> 0
    | None,_ -> -1
    | _,None -> 1
    | Some k1, Some k2 -> k_cmp k1 k2
end
open Internal_misc
*)

module Internal_leaf_impl = struct

  let leaf_profiler = Init_ref.create dummy_profiler
      
  module Internal_ = struct
    open Init_ref
    let profile x z =
      let profiler = leaf_profiler in
      !profiler.mark x;
      let r = z() in
      !profiler.mark (x^"'");
      r
  end
  open Internal_

  let make_leaf_ops (type k v t) ~(map_ops:(k,v,t)map_ops) = 
    let module M = (val map_ops) in
    let leaf_lookup k l = 
      profile (*"ab"*) "ll" @@ fun () -> 
      M.find_opt k l
    in
    let leaf_insert k v l = 
      profile (*"ae"*) "li" @@ fun () -> 
      let old = ref None in
      let l' = 
        M.update 
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
      profile (*"ah"*) "lr" @@ fun () -> 
      M.remove k l in
    let leaf_length l = 
      profile (*"aj"*) "llen" @@ fun () -> 
      M.cardinal l in
    let leaf_steal_right (l1,l2) =
      (* Printf.printf "leaf_steal_right\n"; *)
      profile (*"al"*) "lsr" @@ fun () -> 
      M.min_binding_opt l2 |> dest_Some |> fun (k,v) ->
      l2 |> M.remove k |> fun l2 -> 
      l2 |> M.min_binding_opt |> dest_Some |> fun (k',_) ->
      l1 |> M.add k v |> fun l1 ->
      (l1,k',l2)
    in
    let leaf_steal_left (l1,l2) =
      profile (*"am"*) "lsl" @@ fun () ->      
      M.max_binding_opt l1 |> dest_Some |> fun (k,v) ->
      l1 |> M.remove k |> fun l1 ->
      l2 |> M.add k v |> fun l2 ->
      (l1,k,l2)
    in
    let leaf_merge (l1,l2) = 
      profile (*"an"*) "lm" @@ fun () ->      
      M.disjoint_union l1 l2 
    in
    let split_large_leaf i l1 = 
      profile (*"ao"*) "lspl" @@ fun () ->      
(*      Printf.printf "split_large_leaf: i=%d len=%d"
        i
        (M.cardinal l1);*)
      l1 |> M.bindings |> List_.drop i |> fun binds -> 
      match binds with
      | [] -> failwith __LOC__
      | (k,v)::rest -> 
        l1 |> M.split k |> fun (l1,_,l2) -> 
        l2 |> M.add k v |> fun l2 ->
        (l1,k,l2)
    in
    (* by default, there is no debugging; override the dbg_leaf field to enable *)
    let dbg_leaf = fun l -> () in
    let kvs_to_leaf = fun kvs -> 
      profile "kvs2l" @@ fun () ->
      M.of_bindings kvs in
    let leaf_to_kvs = fun l -> 
      profile "l2kvs" @@ fun () ->      
      M.bindings l in
    let ops = ({ leaf_lookup; leaf_insert; leaf_remove; leaf_length; 
       leaf_steal_right; leaf_steal_left; 
       leaf_merge; split_large_leaf; leaf_to_kvs; kvs_to_leaf })
    in
    ops

  let test_leaf_impl () = 
    let k_cmp: int -> int -> int = Pervasives.compare in
    let module Comp = Util.Internal_make_map_ops(struct type k = int let k_cmp = k_cmp end) in
    let open Comp in
    let map_ops = Tjr_map.With_base.make_map_ops k_comparator in
    let ops = make_leaf_ops ~map_ops in
    let kvs0 = List_.from_to 1 20 |> List.map (fun x -> (x,2*x)) in
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

  let _ = Global.register ~name:(__MODULE__^".test_leaf_impl") test_leaf_impl

end



(** {2 Node operations} *)

module Internal_node_impl = struct

  let node_profiler = Init_ref.create dummy_profiler

  module Internal_ = struct
    open Init_ref
    let profile x z =
      let profiler = node_profiler in
      !profiler.mark x;
      let r = z() in
      !profiler.mark (x^"'");
      r
  end
  open Internal_

  (* implement node ops using a map from option; see impl notes in
     \doc(doc:node_ops) *)

  let make_node_ops (type k v t) ~(map_ops:(k option,v,t)map_ops) = 
    let module M = (val map_ops) in    
    let make_node ks rs = 
      profile "bb" @@ fun () -> 
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
      let krs = List.combine ks rs in
      M.of_bindings krs
    in
    let _ = make_node in

    (* check a node has a binding for None *)
    let check_node_has_none_binding n = 
      assert(M.min_binding_opt n |> function
        | None -> failwith __LOC__
        | Some(None,_) -> true
        | _ -> failwith __LOC__);
      ()
    in

    let check_node = check_node_has_none_binding in

    let split_node_at_k_index i n =   (* i counts from 0 *)
      profile "bc" @@ fun () -> 
      (* FIXME this is rather inefficient... is there a better way?
         without altering the map implementation? *)
      M.bindings n |> fun krs -> 
      let ks,rs = List.split krs in
      let ks = List.tl ks |> List.map dest_Some in  (* drop None *)
      assert(  (* FIXME use Test.assert_ or similar *)
        let len = List.length ks in 
        let _ = 
          match i < len with
          | false -> Printf.printf "NOTE %s: %d %d\n%!" __LOC__ i len
          | true -> ()
        in
        i < len);
      let k = List.nth ks i in
      let r = M.find_opt (Some k) n |> dest_Some in
      let (n1,_,n2) = M.split (Some k) n in
      n2 |> M.add None r |> fun n2 ->
      Test.test (fun () -> check_node n1;check_node n2);
      (n1,k,n2)
    in
    let node_merge (n1,k,n2) = 
      profile "bd" @@ fun () -> 
      n2 |> M.find_opt None |> dest_Some |> fun r2 -> 
      n2 |> M.remove None |> M.add (Some k) r2 |> fun n2 ->
      M.disjoint_union n1 n2 |> fun n -> 
      Test.test (fun () -> check_node n);
      n
    in
    let node_steal_right (n1,k0,n2) =
      profile "be" @@ fun () -> 
      n2 |> M.find_opt None |> dest_Some |> fun r ->
      n2 |> M.remove None |> fun n2 ->
      n2 |> M.min_binding_opt |> dest_Some |> fun (k',r') ->
      k' |> dest_Some |> fun k' ->
      n2 |> M.remove (Some k') |> M.add None r' |> fun n2 ->
      n1 |> M.add (Some k0) r |> fun n1 ->
      Test.test (fun () -> check_node n1;check_node n2);
      (n1,k',n2)
    in
    let node_steal_left (n1,k0,n2) = 
      profile "bf" @@ fun () -> 
      n1 |> M.max_binding_opt |> dest_Some |> fun (k,r) ->
      k |> dest_Some |> fun k ->
      n1 |> M.remove (Some k) |> fun n1 ->
      n2 |> M.min_binding_opt |> dest_Some |> fun (k',r') -> 
      assert(k'=None);
      n2 |> M.remove None |> fun n2 -> 
      n2 |> M.add (Some k0) r' |> fun n2 ->
      n2 |> M.add None r |> fun n2 -> 
      Test.test (fun () -> check_node n1;check_node n2);
      (n1,k,n2)
    in
    let node_keys_length n = 
      profile "bg" @@ fun () -> 
      (M.cardinal n) -1
    in
    let node_make_small_root (r1,k,r2) =
      profile "bh" @@ fun () -> 
      (* Printf.printf "Making small root\n%!"; *)
      M.empty |> M.add None r1 |> M.add (Some k) r2
    in
    let node_get_single_r n =
      profile "bi" @@ fun () -> 
      assert(M.cardinal n = 1);
      M.bindings n |> fun [(_,r)] -> r
    in
    let node_to_krs n = 
      profile "bj" @@ fun () -> 
      n |> M.bindings |> List.split |> fun (ks,rs) ->
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
    let k_cmp: int -> int -> int = Pervasives.compare in
    let module M = struct
      module T = struct
        open Core_kernel
        type t = int option [@@deriving compare,sexp]
      end
      include T
      include Core_kernel.Comparator.Make(T)
    end
    in
    let map_ops = Tjr_map.With_base.make_map_ops (module M) in
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
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n1 |> node_to_string));
    Logger.log(Printf.sprintf "%d %d" __LINE__ k);
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n2 |> node_to_string));
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n3 |> node_to_string));
    let n1,k,n2 = ops.node_steal_left (n1,k,n2) in
    let n3 = ops.node_merge (n1,k,n2) in
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n1 |> node_to_string));
    Logger.log(Printf.sprintf "%d %d" __LINE__ k);
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n2 |> node_to_string));
    Logger.log(Printf.sprintf "%d %s" __LINE__ (n3 |> node_to_string));
    assert(n3 |> ops.node_to_krs = krs0);
    ()

  let _ = Global.register ~name:(__MODULE__^".test_node_impl") test_node_impl
end


(** {2 Frame operations} *)

module Internal_frame_impl = struct

  open Isa_btree_intf.Frame_type

  let frame_profiler = Init_ref.create dummy_profiler

  module Internal_ = struct
    open Init_ref
    let profile x z =
      let profiler = frame_profiler in
      !profiler.mark x;
      let r = z() in
      !profiler.mark (x^"'");
      r
  end
  open Internal_

  (* note that the map_ops is the map ops for the node type *)
  let make_frame_ops (type k r node) ~(map_ops:(k option,r,node)map_ops) =
    let module M = (val map_ops) in      (* M.k is k option! *)
    let split_node_on_key backing_node_blk_ref k n = 
      profile "cb" @@ fun () -> 
      (* get the relevant key *)
      let midkey,midpoint = 
        n |> M.closest_key `Less_or_equal_to (Some k) |> function
        | None -> failwith "impossible: None is < Some k" 
        | Some (k,r) -> (k,r)
      in
      { midkey; midpoint; backing_node_blk_ref; node=n }
    in
    let _ = split_node_on_key in
    let midpoint f = f.midpoint in
    let get_next_binding (k:M.k) node : (k*r) option = 
      M.closest_key `Greater_than k node |> function
      | None -> None
      | Some (None,_) -> failwith __LOC__  (* impossible *)
      (* NOTE that we know that None cannot be a key greater than some
         other key, and this means that the returned value could be
         plain k rather than M.k *)
      | Some (Some k,v) -> Some (k,v)
      (* | Some (Some k,v) -> Some (Some k,v)  (\* NOTE guaranteed to be Some k *\) *)
    in
    let get_prev_binding (k:M.k) node : (M.k*r)option = 
      M.closest_key `Less_than k node |> function
      | None -> None
      | Some(mk,v) -> Some(mk,v)
    in
    let _ = get_prev_binding in
    let get_focus f : k option * r * k option = 
      profile "cc" @@ fun () -> 
      let k1 = f.midkey in
      let k2 = f.node |> get_next_binding f.midkey |> function 
        | None -> None 
        | Some (k,r) -> Some k
      in
      (k1,f.midpoint,k2)
    in
    let get_focus_and_right_sibling f =
      profile "cd" @@ fun () -> 
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
      profile "ce" @@ fun () -> 
      f.node |> get_prev_binding f.midkey |> function
      | None -> None 
      | Some(k1,r1) ->
        let k2,r2 = f.midkey,f.midpoint in
        let k2 = k2 |> dest_Some in (* k2 can't be None if left sib *)
        (* NOTE None hack *)
        Some(k1,r1,k2,r2,None)
    in
    let replace (k,r,krs,_) (k',r',krs',_) f =
      profile "cf" @@ fun () -> 
      assert(M.k_cmp k k' = 0);
      f.node |> M.add k' r' |> fun n ->
      (* remove old ks *)
      (krs,n) 
      |> List_.iter_opt (fun (krs,n) ->
          match krs with 
          | [] -> None
          | (k,r)::krs ->
            n |> M.remove (Some k) |> fun n -> Some(krs,n))
      |> snd
      (* add new krs *)
      |> fun n ->
      (krs',n) 
      |> List_.iter_opt (fun (krs,n) -> 
          match krs with
          | [] -> None
          | (k,r)::krs ->
            n |> M.add (Some k) r |> fun n -> Some(krs,n))
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
        | Some(k,r) -> (Some k:k option)
      in
      (l,u)
    in
    let backing_node_blk_ref f = f.backing_node_blk_ref in
    let split_node_for_leaf_stream r n = 
      profile "ch" @@ fun () -> 
      let midkey = None in
      let midpoint = M.min_binding_opt n |> function
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
      | Some (k,r) -> Some {f with midkey=(Some k); midpoint=r}
    in
    let dbg_frame = fun f -> () in
    { split_node_on_key; midpoint; get_focus; get_focus_and_right_sibling; 
      get_left_sibling_and_focus; replace; frame_to_node; get_midpoint_bounds;
      backing_node_blk_ref; split_node_for_leaf_stream;
      step_frame_for_leaf_stream; dbg_frame }
end


module Export = struct
  let make_leaf_ops = Internal_leaf_impl.make_leaf_ops
  let make_node_ops = Internal_node_impl.make_node_ops
  let make_frame_ops = Internal_frame_impl.make_frame_ops
end

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

include Export
