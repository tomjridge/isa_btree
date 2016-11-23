let string_of_chars chars = chars|>List.map (String.make 1)|>String.concat ""

type any_t

let any_ref = ref ((Obj.magic 1):any_t)


open Gen_isa
  
module Util : sig
  val failwitha : char list -> 'a
  val split_at : Arith.nat -> 'a list -> 'a list * 'a list
  val rev_apply : 'a -> ('a -> 'b) -> 'b
  val impossible : unit -> 'a
  val split_at_3 : Arith.nat -> 'a list -> 'a list * ('a * 'a list)
  val assert_true : 'a -> bool -> bool
end = struct

let rec failwitha x = x|>string_of_chars|>failwith;;

let rec split_at n xs = (List.take n xs, List.drop n xs);;

let rec rev_apply x f = f x;;

let rec impossible
  uu = failwitha ['i'; 'm'; 'p'; 'o'; 's'; 's'; 'i'; 'b'; 'l'; 'e'];;

let rec split_at_3
  n xs =
    (List.take n xs,
      (List.nth xs n, List.drop (Arith.plus_nat n Arith.one_nat) xs));;

let rec assert_true arg b = (
  let _ = any_ref := ((Obj.magic arg):any_t) in
  if b then b else failwith "assert_true")
;;


end;;


module Prelude : sig
  val from_to : Arith.nat -> Arith.nat -> Arith.nat list
end = struct

let rec from_to x y = List.upt x (Arith.suc y);;


end;;


module type Constants_t = sig
  type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
  val max_leaf_size : Arith.nat
  val max_node_keys : Arith.nat
  val min_leaf_size : Arith.nat
  val min_node_keys : Arith.nat
end (*= struct

type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf;;

let max_leaf_size : Arith.nat = Util.failwitha ['F'; 'I'; 'X'; 'M'; 'E'];;

let max_node_keys : Arith.nat = Util.failwitha ['F'; 'I'; 'X'; 'M'; 'E'];;

let min_leaf_size : Arith.nat = Util.failwitha ['F'; 'I'; 'X'; 'M'; 'E'];;

let min_node_keys : Arith.nat = Util.failwitha ['F'; 'I'; 'X'; 'M'; 'E'];;


end;; *)


module type Key_value_types_t = sig
  type key [@@deriving yojson]
  val equal_keya : key -> key -> bool
  val equal_key : key HOL.equal
  type value_t [@@deriving yojson]
  val equal_value_ta : value_t -> value_t -> bool
  val equal_value_t : value_t HOL.equal
  val key_ord : key -> key -> Arith.int
end (*= struct

type key = Private_key of Arith.nat;;

let rec equal_keya (Private_key x) (Private_key ya) = Arith.equal_nat x ya;;

let equal_key = ({HOL.equal = equal_keya} : key HOL.equal);;

type value_t = Private_value of Arith.nat;;

let rec equal_value_ta
  (Private_value x) (Private_value ya) = Arith.equal_nat x ya;;

let equal_value_t = ({HOL.equal = equal_value_ta} : value_t HOL.equal);;

let rec key_ord k1 k2 = Util.failwitha ['k'; 'e'; 'y'; '_'; 'o'; 'r'; 'd'];;


end;; *)

module Make = functor (Constants : Constants_t) -> functor(Key_value_types: Key_value_types_t) -> struct


module Key_value : sig
  val key_eq : Key_value_types.key -> Key_value_types.key -> bool
  val key_lt : Key_value_types.key -> Key_value_types.key -> bool
  val check_keys :
    Key_value_types.key option ->
      Key_value_types.key Set.set -> Key_value_types.key option -> bool
  val kvs_insert :
    Key_value_types.key ->
      Key_value_types.value_t ->
        (Key_value_types.key * Key_value_types.value_t) list ->
          (Key_value_types.key * Key_value_types.value_t) list
  val split_leaf :
    (Key_value_types.key * Key_value_types.value_t) list ->
      (Key_value_types.key * Key_value_types.value_t) list *
        (Key_value_types.key *
          (Key_value_types.key * Key_value_types.value_t) list)
  val split_node :
    Key_value_types.key list * 'a list ->
      (Key_value_types.key list * 'a list) *
        (Key_value_types.key * (Key_value_types.key list * 'a list))
  val check_keys_2 :
    Key_value_types.key Set.set ->
      Key_value_types.key option ->
        Key_value_types.key Set.set ->
          Key_value_types.key option -> Key_value_types.key Set.set -> bool
  val ordered_key_list : Key_value_types.key list -> bool
end = struct

let rec key_eq
  k1 k2 = Arith.equal_int (Key_value_types.key_ord k1 k2) Arith.zero_int;;

let rec key_lt
  k1 k2 = Arith.less_int (Key_value_types.key_ord k1 k2) Arith.zero_int;;

let rec key_le k1 k2 = key_lt k1 k2 || key_eq k1 k2;;

let rec check_keys
  kl ks kr =
    let b1 = (match kl with None -> true | Some kla -> Set.ball ks (key_le kla))
      in
    let a =
      (match kr with None -> true
        | Some kra -> Set.ball ks (fun k -> key_lt k kra))
      in
    b1 && a;;

let rec kvs_insert
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, kv :: kvs ->
        let (ka, va) = kv in
        let i = Key_value_types.key_ord ka k in
        (if Arith.less_int i Arith.zero_int then (ka, va) :: kvs_insert k v kvs
          else (if Arith.equal_int i Arith.zero_int then (k, v) :: kvs
                 else (k, v) :: (ka, va) :: kvs));;

let rec split_leaf
  kvs = let min = Constants.min_leaf_size in
        let (l, r) = Util.split_at min kvs in
        let k = (match r with [] -> Util.impossible () | (k, _) :: _ -> k) in
        (l, (k, r));;

let rec split_node
  n = let (ks, rs) = n in
      let min = Constants.min_node_keys in
      let (ks1, (k, ks2)) = Util.split_at_3 min ks in
      let (rs1, rs2) = Util.split_at (Arith.plus_nat min Arith.one_nat) rs in
      ((ks1, rs1), (k, (ks2, rs2)));;

let rec check_keys_2
  xs l ks u zs =
    (match Option.is_none l
      with true -> Set.equal_set Key_value_types.equal_key xs Set.bot_set
      | false -> true) &&
      ((match Option.is_none u
         with true -> Set.equal_set Key_value_types.equal_key zs Set.bot_set
         | false -> true) &&
        (check_keys None xs l && (check_keys l ks u && check_keys u zs None)));;

let rec ordered_key_list
  ks = Arith.less_nat (List.size_list ks)
         (Arith.nat_of_integer (Big_int.big_int_of_int 2)) ||
         List.pred_list
           (fun i ->
             key_lt (List.nth ks i)
               (List.nth ks (Arith.plus_nat i Arith.one_nat)))
           (Prelude.from_to Arith.zero_nat
             (Arith.minus_nat (List.size_list ks)
               (Arith.nat_of_integer (Big_int.big_int_of_int 2))));;


end;;


module Tree : sig
  type tree = Node of (Key_value_types.key list * tree list) |
    Leaf of (Key_value_types.key * Key_value_types.value_t) list [@@deriving yojson]
  val equal_Tree : tree HOL.equal
  val height : tree -> Arith.nat
  val dest_Leaf : tree -> (Key_value_types.key * Key_value_types.value_t) list
  val dest_Node : tree -> Key_value_types.key list * tree list
  val tree_to_leaves :
    tree -> ((Key_value_types.key * Key_value_types.value_t) list) list
  val tss_to_keys : (tree list) list -> Key_value_types.key Set.set
  val tree_to_keys : tree -> Key_value_types.key Set.set
  val tss_to_leaves :
    (tree list) list ->
      ((Key_value_types.key * Key_value_types.value_t) list) list
  val ks_to_max_child_index : Key_value_types.key list -> Arith.nat
  val min_child_index : Arith.nat
  val wellformed_tree : Constants.min_size_t option -> tree -> bool
end = struct

type tree = Node of (Key_value_types.key list * tree list) |
  Leaf of (Key_value_types.key * Key_value_types.value_t) list [@@deriving yojson];;

let rec equal_Tree () = ({HOL.equal = equal_Treea} : tree HOL.equal)
and equal_Treea
  x0 x1 = match x0, x1 with Node x1, Leaf x2 -> false
    | Leaf x2, Node x1 -> false
    | Leaf x2, Leaf y2 ->
        List.equal_lista
          (Product_Type.equal_prod Key_value_types.equal_key
            Key_value_types.equal_value_t)
          x2 y2
    | Node x1, Node y1 ->
        Product_Type.equal_proda (List.equal_list Key_value_types.equal_key)
          (List.equal_list (equal_Tree ())) x1 y1;;
let equal_Tree = equal_Tree ();;

let rec tree_to_subtrees
  t0 = (match t0
         with Node (_, cs) ->
           t0 :: Util.rev_apply (List.map tree_to_subtrees cs) List.concat
         | Leaf _ -> [t0]);;

let rec keys_1
  t0 = (match t0 with Node (l, _) -> l
         | Leaf a -> List.map Product_Type.fst a);;

let rec keys
  t0 = Util.rev_apply
         (Util.rev_apply (Util.rev_apply t0 tree_to_subtrees) (List.map keys_1))
         List.concat;;

let rec height
  t0 = (match t0
         with Node (_, cs) ->
           Arith.plus_nat Arith.one_nat
             (Lattices_Big.max Arith.linorder_nat
               (Set.Set (List.map height cs)))
         | Leaf _ -> Arith.one_nat);;

let rec forall_subtrees
  p t = List.pred_list p (Util.rev_apply t tree_to_subtrees);;

let rec get_min_size
  mt = (match mt
         with (Constants.Small_root_node_or_leaf, Node _) -> Arith.one_nat
         | (Constants.Small_root_node_or_leaf, Leaf _) -> Arith.zero_nat
         | (Constants.Small_node, Node _) ->
           Arith.minus_nat Constants.min_node_keys Arith.one_nat
         | (Constants.Small_leaf, Leaf _) ->
           Arith.minus_nat Constants.min_leaf_size Arith.one_nat);;

let rec wf_size_1
  t1 = (match t1
         with Node (l, _) ->
           let n = List.size_list l in
           Arith.less_eq_nat Arith.one_nat n &&
             (Arith.less_eq_nat Constants.min_node_keys n &&
               Arith.less_eq_nat n Constants.max_node_keys)
         | Leaf xs ->
           let n = List.size_list xs in
           Arith.less_eq_nat Constants.min_leaf_size n &&
             Arith.less_eq_nat n Constants.max_leaf_size);;

let rec wf_size
  ms t0 =
    Util.assert_true (ms, t0)
      (match ms with None -> forall_subtrees wf_size_1 t0
        | Some m ->
          let min = get_min_size (m, t0) in
          (match t0
            with Node (l, cs) ->
              let n = List.size_list l in
              Arith.less_eq_nat min n &&
                (Arith.less_eq_nat n Constants.max_node_keys &&
                  List.pred_list (forall_subtrees wf_size_1) cs)
            | Leaf xs ->
              let n = List.size_list xs in
              Arith.less_eq_nat min n &&
                Arith.less_eq_nat n Constants.max_leaf_size));;

let rec balanced_1
  t0 = (match t0
         with Node (_, cs) ->
           List.null cs ||
             List.pred_list
               (fun c ->
                 Arith.equal_nat (height c)
                   (height (List.nth cs Arith.zero_nat)))
               cs
         | Leaf _ -> true);;

let rec balanced t = Util.assert_true t (forall_subtrees balanced_1 t);;

let rec wf_ks_rs_1
  t0 = (match t0
         with Node (l, cs) ->
           Arith.equal_nat (Arith.plus_nat Arith.one_nat (List.size_list l))
             (List.size_list cs)
         | Leaf _ -> true);;

let rec wf_ks_rs t0 = Util.assert_true t0 (forall_subtrees wf_ks_rs_1 t0);;

let rec dest_Leaf
  = function Leaf kvs -> kvs
    | Node v -> Util.failwitha ['d'; 'e'; 's'; 't'; '_'; 'L'; 'e'; 'a'; 'f'];;

let rec dest_Node
  = function Node (ks, rs) -> (ks, rs)
    | Leaf uu -> Util.failwitha ['d'; 'e'; 's'; 't'; '_'; 'N'; 'o'; 'd'; 'e'];;

let rec tree_to_leaves
  t0 = (match t0
         with Node (_, cs) ->
           Util.rev_apply (Util.rev_apply cs (List.map tree_to_leaves))
             List.concat
         | Leaf l -> [l]);;

let rec tree_to_kvs
  t = Util.rev_apply (Util.rev_apply t tree_to_leaves) List.concat;;

let rec trees_to_keys
  ts = Util.rev_apply
         (Util.rev_apply
           (Util.rev_apply (Util.rev_apply ts (List.map tree_to_kvs))
             List.concat)
           (List.map Product_Type.fst))
         (fun a -> Set.Set a);;

let rec tss_to_keys
  tss = Util.rev_apply (Util.rev_apply tss List.concat) trees_to_keys;;

let rec keys_ordered_1
  t0 = Util.rev_apply (Util.rev_apply t0 keys_1) Key_value.ordered_key_list;;

let rec keys_ordered t = Util.assert_true t (forall_subtrees keys_ordered_1 t);;

let rec tree_to_keys
  t = Util.rev_apply
        (Util.rev_apply (Util.rev_apply t tree_to_kvs)
          (List.map Product_Type.fst))
        (fun a -> Set.Set a);;

let rec tss_to_leaves
  tss = Util.rev_apply
          (Util.rev_apply (Util.rev_apply tss List.concat)
            (List.map tree_to_leaves))
          List.concat;;

let rec ks_to_max_child_index ks = List.size_list ks;;

let min_child_index : Arith.nat = Arith.zero_nat;;

let rec index_to_bound
  ks i =
    let l =
      (if Arith.equal_nat i min_child_index then None
        else Some (List.nth ks (Arith.minus_nat i Arith.one_nat)))
      in
    let a =
      (if Arith.less_eq_nat (ks_to_max_child_index ks) i then None
        else Some (List.nth ks i))
      in
    (l, a);;

let rec subtree_indexes
  node =
    let (ks, _) = node in
    Prelude.from_to min_child_index (ks_to_max_child_index ks);;

let rec keys_consistent_1
  t0 = (match t0
         with Node (ks, rs) ->
           List.pred_list
             (fun i ->
               let a = index_to_bound ks i in
               let (l, aa) = a in
               Key_value.check_keys l (Set.Set (keys (List.nth rs i))) aa)
             (subtree_indexes (ks, rs))
         | Leaf _ -> true);;

let rec keys_consistent
  t = Util.assert_true t (forall_subtrees keys_consistent_1 t);;

let rec wellformed_tree
  ms t0 =
    Util.assert_true (ms, t0)
      (let b1 = wf_size ms t0 in
       let b2 = wf_ks_rs t0 in
       let b3 = balanced t0 in
       let b4 = keys_consistent t0 in
       let b5 = keys_ordered t0 in
       let wf = b1 && (b2 && (b3 && (b4 && b5))) in
       wf);;


end;;


module Tree_stack : sig
  type ('a, 'b) core_t_ext =
    Core_t_ext of
      Key_value_types.key * (Tree.tree list) list * Key_value_types.key option *
        'a * Key_value_types.key option * (Tree.tree list) list * 'b[@@deriving yojson]
  val equal_core_t_exta :
    'a HOL.equal -> 'b HOL.equal ->
      ('a, 'b) core_t_ext -> ('a, 'b) core_t_ext -> bool
  val f_t : ('a, 'b) core_t_ext -> 'a
  val f_k : ('a, 'b) core_t_ext -> Key_value_types.key
  val dest_core :
    ('a, unit) core_t_ext ->
      Key_value_types.key *
        ((Tree.tree list) list *
          (Key_value_types.key option *
            ('a * (Key_value_types.key option * (Tree.tree list) list))))
  val wf_core : Key_value_types.key Set.set -> ('a, unit) core_t_ext -> bool
  val with_t : ('a -> 'b) -> ('a, unit) core_t_ext -> ('b, unit) core_t_ext
  val nf_to_aux :
    Key_value_types.key ->
      ((Key_value_types.key list * Tree.tree list), unit) core_t_ext ->
        Arith.nat *
          (Tree.tree list *
            (Key_value_types.key list *
              (Tree.tree * (Key_value_types.key list * Tree.tree list))))
  val mk_child :
    ((Key_value_types.key list * Tree.tree list), unit) core_t_ext ->
      (Tree.tree, unit) core_t_ext
  val ts_to_ms :
    ((Key_value_types.key list * Tree.tree list), unit) core_t_ext list ->
      Constants.min_size_t option
  val without_t : ('a, unit) core_t_ext -> (unit, unit) core_t_ext
  val wellformed_ts :
    ((Key_value_types.key list * Tree.tree list), unit) core_t_ext list -> bool
end = struct

type ('a, 'b) core_t_ext =
  Core_t_ext of
    Key_value_types.key * (Tree.tree list) list * Key_value_types.key option *
      'a * Key_value_types.key option * (Tree.tree list) list * 'b[@@deriving yojson];;

let rec equal_core_t_exta _A _B
  (Core_t_ext (f_ka, f_tss1a, f_kla, f_ta, f_kua, f_tss2a, morea))
    (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) =
    Key_value_types.equal_keya f_ka f_k &&
      (List.equal_lista (List.equal_list Tree.equal_Tree) f_tss1a f_tss1 &&
        (Option.equal_option Key_value_types.equal_key f_kla f_kl &&
          (HOL.eq _A f_ta f_t &&
            (Option.equal_option Key_value_types.equal_key f_kua f_ku &&
              (List.equal_lista (List.equal_list Tree.equal_Tree) f_tss2a
                 f_tss2 &&
                HOL.eq _B morea more)))));;

let rec equal_core_t_ext _A _B =
  ({HOL.equal = equal_core_t_exta _A _B} : ('a, 'b) core_t_ext HOL.equal);;

let rec f_t (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_t;;

let rec f_tss2
  (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_tss2;;

let rec f_tss1
  (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_tss1;;

let rec f_ku (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_ku;;

let rec f_kl (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_kl;;

let rec f_k (Core_t_ext (f_k, f_tss1, f_kl, f_t, f_ku, f_tss2, more)) = f_k;;

let rec dest_core
  f = (Util.rev_apply f f_k,
        (Util.rev_apply f f_tss1,
          (Util.rev_apply f f_kl,
            (Util.rev_apply f f_t,
              (Util.rev_apply f f_ku, Util.rev_apply f f_tss2)))));;

let rec wf_core
  t_keys x =
    Util.assert_true (t_keys, x)
      (let (k, (tss1, (kl, (_, (ku, tss2))))) = Util.rev_apply x dest_core in
       Key_value.check_keys_2 (Util.rev_apply tss1 Tree.tss_to_keys) kl
         (Set.insert Key_value_types.equal_key k t_keys) ku
         (Util.rev_apply tss2 Tree.tss_to_keys));;

let rec wf_nf
  ms f =
    Util.assert_true (ms, f)
      (let (ks, ts) = Util.rev_apply f f_t in
       wf_core (Util.rev_apply (Tree.Node (ks, ts)) Tree.tree_to_keys) f);;

let rec with_t
  f x = let (k, (tss1, (kl, (t, (ku, tss2))))) = Util.rev_apply x dest_core in
        Core_t_ext (k, tss1, kl, f t, ku, tss2, ());;

let rec search_key_to_index
  ks k =
    let num_keys = List.size_list ks in
    let i =
      List.find (fun x -> Key_value.key_lt k (List.nth ks x))
        (List.upt Arith.zero_nat num_keys)
      in
    let ia = (match i with None -> num_keys | Some x -> x) in
    ia;;

let rec nf_to_aux
  k0 f =
    let a = Util.rev_apply f dest_core in
    let (_, aa) = a in
    let (_, ab) = aa in
    let (_, ac) = ab in
    let (ad, b) = ac in
    let (ks, ts) = ad in
    (fun (_, _) ->
      let i = search_key_to_index ks k0 in
      let (ts1, (t, ts2)) = Util.split_at_3 i ts in
      let (ks1, ks2) = Util.split_at i ks in
      (i, (ts1, (ks1, (t, (ks2, ts2))))))
      b;;

let rec mk_child
  p = let a = Util.rev_apply p dest_core in
      let (k, aa) = a in
      let (tss1, ab) = aa in
      let (kl, ac) = ab in
      let (ad, b) = ac in
      let (ks, _) = ad in
      (fun (ku, tss2) ->
        let (i, (ts1, (ks1, (t, (ks2, ts2))))) = nf_to_aux k p in
        let f2 =
          Core_t_ext
            (k, tss1 @ [ts1],
              (if Arith.equal_nat i Tree.min_child_index then kl
                else Some (List.last ks1)),
              t, (if Arith.equal_nat i (Tree.ks_to_max_child_index ks) then ku
                   else Some (List.hd ks2)),
              [ts2] @ tss2, ())
          in
        f2)
        b;;

let rec ts_to_ms
  ts = (match ts with [] -> Some Constants.Small_root_node_or_leaf
         | _ :: _ -> None);;

let rec without_t x = Util.rev_apply x (with_t (fun _ -> ()));;

let rec mk_next_frame
  p = let c = mk_child p in
      (match Util.rev_apply c f_t
        with Tree.Node (ks, ts) ->
          Some (Util.rev_apply c (with_t (fun _ -> (ks, ts))))
        | Tree.Leaf _ -> None);;

let rec wellformed_ts
  xs = Util.assert_true xs
         (match xs with [] -> true
           | c :: xsa ->
             wf_nf (ts_to_ms xsa) c &&
               (wellformed_ts xsa &&
                 (match xsa with [] -> true
                   | p :: _ ->
                     Option.equal_option
                       (equal_core_t_ext
                         (Product_Type.equal_prod
                           (List.equal_list Key_value_types.equal_key)
                           (List.equal_list Tree.equal_Tree))
                         Product_Type.equal_unit)
                       (mk_next_frame p) (Some c))));;


end;;


module Find_tree_stack : sig
  type fts_state_t[@@deriving yojson]
  val dest_fts_state :
    fts_state_t ->
      (Tree.tree, unit) Tree_stack.core_t_ext *
        ((Key_value_types.key list * Tree.tree list), unit)
          Tree_stack.core_t_ext list
  val step_fts : fts_state_t -> fts_state_t option
  val mk_fts_state : Key_value_types.key -> Tree.tree -> fts_state_t
  val focus_to_leaves :
    (Tree.tree, unit) Tree_stack.core_t_ext ->
      ((Key_value_types.key * Key_value_types.value_t) list) list
  val wf_fts_trans : fts_state_t -> fts_state_t -> bool
  val wellformed_fts : fts_state_t -> bool
end = struct

type fts_state_t =
  Fts_state of
    ((Tree.tree, unit) Tree_stack.core_t_ext *
      ((Key_value_types.key list * Tree.tree list), unit)
        Tree_stack.core_t_ext list)[@@deriving yojson];;

let rec dest_fts_state s = let Fts_state x = s in
                           x;;

let rec step_fts
  fts = let (f, xs) = Util.rev_apply fts dest_fts_state in
        (match Util.rev_apply f Tree_stack.f_t
          with Tree.Node (ks, rs) ->
            let p = Util.rev_apply f (Tree_stack.with_t (fun _ -> (ks, rs))) in
            let c = Tree_stack.mk_child p in
            Some (Fts_state (c, p :: xs))
          | Tree.Leaf _ -> None);;

let rec mk_fts_state
  k t = let f = Tree_stack.Core_t_ext (k, [], None, t, None, [], ()) in
        Fts_state (f, []);;

let rec focus_to_leaves
  f = let (_, (tss1, (_, (t, (_, tss2))))) =
        Util.rev_apply f Tree_stack.dest_core in
      Util.rev_apply (tss1 @ [[t]] @ tss2) Tree.tss_to_leaves;;

let rec wf_fts_trans
  s1 s2 =
    Util.assert_true (s1, s2)
      (List.equal_lista
        (List.equal_list
          (Product_Type.equal_prod Key_value_types.equal_key
            Key_value_types.equal_value_t))
        (focus_to_leaves
          (Util.rev_apply (Util.rev_apply s2 dest_fts_state) Product_Type.fst))
        (focus_to_leaves
          (Util.rev_apply (Util.rev_apply s1 dest_fts_state)
            Product_Type.fst)));;

let rec wellformed_fts_focus
  ms f =
    Util.assert_true (ms, f)
      (let t = Util.rev_apply f Tree_stack.f_t in
       Tree_stack.wf_core (Util.rev_apply t Tree.tree_to_keys) f &&
         Tree.wellformed_tree ms t);;

let rec wellformed_fts_1
  fts = Util.assert_true fts
          (match Util.rev_apply fts dest_fts_state with (_, []) -> true
            | (c, p :: _) ->
              Tree_stack.equal_core_t_exta Tree.equal_Tree
                Product_Type.equal_unit (Tree_stack.mk_child p) c);;

let rec wellformed_fts
  fts = Util.assert_true fts
          (let (f, ts) = Util.rev_apply fts dest_fts_state in
           let ms = Tree_stack.ts_to_ms ts in
           Tree_stack.wellformed_ts ts &&
             (wellformed_fts_focus ms f && wellformed_fts_1 fts));;


end;;


module Delete_tree_stack : sig
  type dts_t =
    D_small_leaf of (Key_value_types.key * Key_value_types.value_t) list |
    D_small_node of (Key_value_types.key list * Tree.tree list) |
    D_updated_subtree of Tree.tree
  type dts_state_t = Dts_down of Find_tree_stack.fts_state_t |
    Dts_up of
        ((dts_t, unit) Tree_stack.core_t_ext *
          ((Key_value_types.key list * Tree.tree list), unit)
            Tree_stack.core_t_ext list)
    | Dts_finished of Tree.tree[@@deriving yojson]
  val step_dts : dts_state_t -> dts_state_t option
  val mk_dts_state : Key_value_types.key -> Tree.tree -> dts_state_t
  val focus_to_leaves :
    (dts_t, unit) Tree_stack.core_t_ext ->
      ((Key_value_types.key * Key_value_types.value_t) list) list
  val wf_dts_trans : dts_state_t -> dts_state_t -> bool
  val dest_dts_state : dts_state_t -> Tree.tree option
  val wellformed_dts_state : dts_state_t -> bool
end = struct

type 'a d12_t = D1 of 'a | D2 of ('a * (Key_value_types.key * 'a));;

  type dts_t =
    D_small_leaf of (Key_value_types.key * Key_value_types.value_t) list |
    D_small_node of (Key_value_types.key list * Tree.tree list) |
    D_updated_subtree of Tree.tree[@@deriving yojson];;
type dts_state_t = Dts_down of Find_tree_stack.fts_state_t |
  Dts_up of
    ((dts_t, unit) Tree_stack.core_t_ext *
      ((Key_value_types.key list * Tree.tree list), unit)
        Tree_stack.core_t_ext list)
  | Dts_finished of Tree.tree[@@deriving yojson];;

let rec unzip
  xs = (Util.rev_apply xs (List.map Product_Type.fst),
         Util.rev_apply xs (List.map Product_Type.snd));;

let rec frac_mult
  xs ys =
    let a = xs in
    let (aa, b) = a in
    let (aaa, ba) = ys in
    (aa @ aaa, b @ ba);;

let rec post_steal_or_merge
  stk p p_1 p_2 x =
    let m = frac_mult in
    (match x
      with D1 c ->
        let pa = Tree.Node (m (m p_1 ([], [c])) p_2) in
        let p_sz =
          Util.rev_apply
            (Util.rev_apply (Util.rev_apply pa Tree.dest_Node) Product_Type.fst)
            List.size_list
          in
        let f =
          (match Arith.equal_nat p_sz Arith.zero_nat
            with true ->
              let _ = Util.assert_true (List.null stk) in
              D_updated_subtree c
            | false ->
              (match Arith.less_nat p_sz Constants.min_node_keys
                with true -> D_small_node (Util.rev_apply pa Tree.dest_Node)
                | false -> D_updated_subtree pa))
          in
        let fa = Util.rev_apply p (Tree_stack.with_t (fun _ -> f)) in
        Dts_up (fa, stk)
      | D2 (c1, (k, c2)) ->
        let pa = Tree.Node (m (m p_1 ([k], [c1; c2])) p_2) in
        let p_sz =
          Util.rev_apply
            (Util.rev_apply (Util.rev_apply pa Tree.dest_Node) Product_Type.fst)
            List.size_list
          in
        let f =
          (match Arith.less_nat p_sz Constants.min_node_keys
            with true ->
              let _ = Util.assert_true (List.null stk) in
              D_small_node (Util.rev_apply pa Tree.dest_Node)
            | false -> D_updated_subtree pa)
          in
        let fa = Util.rev_apply p (Tree_stack.with_t (fun _ -> f)) in
        Dts_up (fa, stk));;

let rec dest_lista
  xs = (match xs
         with [] ->
           Util.failwitha
             ['d'; 'e'; 's'; 't'; '_'; 'l'; 'i'; 's'; 't'; '\039'; ' ']
         | _ :: _ -> (List.butlast xs, List.last xs));;

let rec dest_list
  xs = (match xs
         with [] -> Util.failwitha ['d'; 'e'; 's'; 't'; '_'; 'l'; 'i'; 's'; 't']
         | a :: b -> (a, b));;

let rec steal_or_merge
  right is_leaf mk_c c p_k s =
    let m = frac_mult in
    let (s_ks, s_ts) = s in
    let a =
      (match right
        with true ->
          let a = (dest_list s_ks, dest_list s_ts) in
          let (aa, b) = a in
          let (k, ks) = aa in
          (fun (t, ts) -> ((k, t), (ks, ts)))
            b
        | false ->
          let a = (dest_lista s_ks, dest_lista s_ts) in
          let (aa, b) = a in
          let (ks, k) = aa in
          (fun (ts, t) -> ((k, t), (ks, ts)))
            b)
      in
    let (aa, b) = a in
    let (s_k, s_t) = aa in
    (fun s_1 ->
      (match
        Arith.less_nat
          (if is_leaf then Constants.min_leaf_size else Constants.min_node_keys)
          (Arith.plus_nat Arith.one_nat (List.size_list (Product_Type.fst s_1)))
        with true ->
          let ca =
            let k = (if is_leaf then s_k else p_k) in
            (if right then m c ([k], [s_t]) else m ([k], [s_t]) c)
            in
          let sa = mk_c s_1 in
          let p_ka =
            (if is_leaf
              then let right_sib = (if right then s_1 else ca) in
                   Util.rev_apply (Util.rev_apply right_sib Product_Type.fst)
                     List.hd
              else s_k)
            in
          let cb = mk_c ca in
          (if right then D2 (cb, (p_ka, sa)) else D2 (sa, (p_ka, cb)))
        | false ->
          let k = (if is_leaf then ([], []) else ([p_k], [])) in
          let ab = mk_c (if right then m (m c k) s else m s (m k c)) in
          D1 ab))
      b;;

let rec get_sibling
  p = let (p_1, p_2) = p in
      (match p_2
        with ([], _) ->
          (match p_1 with ([], _) -> Util.impossible ()
            | (_ :: _, []) -> Util.impossible ()
            | (_ :: _, _ :: _) ->
              let right = false in
              let (p_ks1, p_ts1) = p_1 in
              let (p_1_ks, p_k) = dest_lista p_ks1 in
              let (p_1_ts, s) = dest_lista p_ts1 in
              let (p_1a, _) = ((p_1_ks, p_1_ts), p_2) in
              (right, ((p_1a, p_2), (s, p_k))))
        | (_ :: _, []) ->
          (match p_1 with ([], _) -> Util.impossible ()
            | (_ :: _, []) -> Util.impossible ()
            | (_ :: _, _ :: _) ->
              let right = false in
              let (p_ks1, p_ts1) = p_1 in
              let (p_1_ks, p_k) = dest_lista p_ks1 in
              let (p_1_ts, s) = dest_lista p_ts1 in
              let (p_1a, _) = ((p_1_ks, p_1_ts), p_2) in
              (right, ((p_1a, p_2), (s, p_k))))
        | (p_k :: p_ks2, s :: p_ts2) ->
          let right = true in
          let (_, p_2a) = (p_1, (p_ks2, p_ts2)) in
          (right, ((p_1, p_2a), (s, p_k))));;

let rec dts_to_tree
  dts = (match dts with D_small_leaf a -> Tree.Leaf a
          | D_small_node (ks, ts) -> Tree.Node (ks, ts)
          | D_updated_subtree t -> t);;

let rec step_up
  du = let (f, stk) = du in
       let k0 = Util.rev_apply f Tree_stack.f_k in
       (match stk
         with [] ->
           Dts_finished
             (Util.rev_apply (Util.rev_apply f Tree_stack.f_t) dts_to_tree)
         | p :: stka ->
           (match Util.rev_apply f Tree_stack.f_t
             with D_small_leaf kvs ->
               let leaf = true in
               let (_, (p_ts1, (p_ks1, (_, (p_ks2, p_ts2))))) =
                 Util.rev_apply p (Tree_stack.nf_to_aux k0) in
               let mk_c = (fun (ks, vs) -> Tree.Leaf (List.zip ks vs)) in
               let a = get_sibling ((p_ks1, p_ts1), (p_ks2, p_ts2)) in
               let (right, aa) = a in
               let (ab, b) = aa in
               let (p_1, p_2) = ab in
               (fun (s, p_k) ->
                 let ac =
                   steal_or_merge right leaf mk_c (Util.rev_apply kvs unzip) p_k
                     (Util.rev_apply (Util.rev_apply s Tree.dest_Leaf) unzip)
                   in
                 post_steal_or_merge stka p p_1 p_2 ac)
                 b
             | D_small_node (ks, ts) ->
               let leaf = true in
               let (_, (p_ts1, (p_ks1, (_, (p_ks2, p_ts2))))) =
                 Util.rev_apply p (Tree_stack.nf_to_aux k0) in
               let mk_c = (fun _ -> Tree.Node (ks, ts)) in
               let a = get_sibling ((p_ks1, p_ts1), (p_ks2, p_ts2)) in
               let (right, aa) = a in
               let (ab, b) = aa in
               let (p_1, p_2) = ab in
               (fun (s, p_k) ->
                 let ac =
                   steal_or_merge right (not leaf) mk_c (ks, ts) p_k
                     (Util.rev_apply s Tree.dest_Node)
                   in
                 post_steal_or_merge stka p p_1 p_2 ac)
                 b
             | D_updated_subtree t ->
               let (_, (ts1, (ks1, (_, (ks2, ts2))))) =
                 Util.rev_apply p (Tree_stack.nf_to_aux k0) in
               Dts_up
                 (Util.rev_apply p
                    (Tree_stack.with_t
                      (fun _ ->
                        D_updated_subtree
                          (Tree.Node (ks1 @ ks2, ts1 @ [t] @ ts2)))),
                   stka)));;

let rec step_dts
  dts = (match dts
          with Dts_down fts ->
            (match Find_tree_stack.step_fts fts
              with None ->
                let (f, stk) = Util.rev_apply fts Find_tree_stack.dest_fts_state
                  in
                let (k, (_, (_, (t, (_, _))))) =
                  Util.rev_apply f Tree_stack.dest_core in
                let kvs = Util.rev_apply t Tree.dest_Leaf in
                (match
                  List.member Key_value_types.equal_key
                    (Util.rev_apply kvs (List.map Product_Type.fst)) k
                  with true ->
                    let kvsa =
                      Util.rev_apply kvs
                        (List.filter
                          (fun x ->
                            not (Key_value.key_eq (Product_Type.fst x) k)))
                      in
                    (match
                      Arith.less_nat (List.size_list kvsa)
                        Constants.min_leaf_size
                      with true ->
                        Some (Dts_up
                               (Util.rev_apply f
                                  (Tree_stack.with_t
                                    (fun _ -> D_small_leaf kvsa)),
                                 stk))
                      | false ->
                        Some (Dts_up
                               (Util.rev_apply f
                                  (Tree_stack.with_t
                                    (fun _ ->
                                      D_updated_subtree (Tree.Leaf kvsa))),
                                 stk)))
                  | false ->
                    (match stk with [] -> Some (Dts_finished (Tree.Leaf kvs))
                      | _ :: _ ->
                        Some (Dts_finished
                               (Tree.Node
                                 (Util.rev_apply (Util.rev_apply stk List.last)
                                   Tree_stack.f_t)))))
              | Some ftsa -> Some (Dts_down ftsa))
          | Dts_up (f, stk) -> Some (step_up (f, stk))
          | Dts_finished _ -> None);;

let rec dts_to_ms
  stack_empty dts =
    (match stack_empty with true -> Some Constants.Small_root_node_or_leaf
      | false ->
        (match dts with D_small_leaf _ -> Some Constants.Small_leaf
          | D_small_node (_, _) -> Some Constants.Small_node
          | D_updated_subtree _ -> None));;

let rec mk_dts_state k0 t = Dts_down (Find_tree_stack.mk_fts_state k0 t);;

let rec focus_to_leaves
  f = let (_, (tss1, (_, (dts, (_, tss2))))) =
        Util.rev_apply f Tree_stack.dest_core in
      Util.rev_apply (tss1 @ [[Util.rev_apply dts dts_to_tree]] @ tss2)
        Tree.tss_to_leaves;;

let rec wf_dts_trans
  s1 s2 =
    Util.assert_true (s1, s2)
      (match (s1, s2)
        with (Dts_down fts, Dts_down a) -> Find_tree_stack.wf_fts_trans fts a
        | (Dts_down _, Dts_up _) -> true | (Dts_down _, Dts_finished _) -> true
        | (Dts_up du, Dts_up dua) ->
          List.equal_lista
            (Product_Type.equal_prod Key_value_types.equal_key
              Key_value_types.equal_value_t)
            (Util.rev_apply (focus_to_leaves (Product_Type.fst dua))
              List.concat)
            (Util.rev_apply (focus_to_leaves (Product_Type.fst du)) List.concat)
        | (Dts_up du, Dts_finished t) ->
          List.equal_lista
            (List.equal_list
              (Product_Type.equal_prod Key_value_types.equal_key
                Key_value_types.equal_value_t))
            (focus_to_leaves (Product_Type.fst du)) (Tree.tree_to_leaves t));;

let rec dest_dts_state
  s = (match s with Dts_down _ -> None | Dts_up _ -> None
        | Dts_finished a -> Some a);;

let rec wellformed_dts
  stack_empty dts =
    Util.assert_true dts
      (let t = Util.rev_apply dts dts_to_tree in
       let ms = Util.rev_apply dts (dts_to_ms stack_empty) in
       Tree.wellformed_tree ms t);;

let rec wellformed_dts_focus
  stack_empty f =
    Util.assert_true (stack_empty, f)
      (let dts = Util.rev_apply f Tree_stack.f_t in
       Tree_stack.wf_core
         (Util.rev_apply (Util.rev_apply dts dts_to_tree) Tree.tree_to_keys)
         f &&
         wellformed_dts stack_empty dts);;

let rec wellformed_dup_1
  dup = Util.assert_true dup
          (match dup with (_, []) -> true
            | (f, p :: _) ->
              Tree_stack.equal_core_t_exta Product_Type.equal_unit
                Product_Type.equal_unit (Util.rev_apply f Tree_stack.without_t)
                (Util.rev_apply (Tree_stack.mk_child p) Tree_stack.without_t) &&
                Arith.equal_nat
                  (Util.rev_apply
                    (Util.rev_apply (Util.rev_apply f Tree_stack.f_t)
                      dts_to_tree)
                    Tree.height)
                  (Util.rev_apply
                    (Util.rev_apply (Util.rev_apply p Tree_stack.mk_child)
                      Tree_stack.f_t)
                    Tree.height));;

let rec wellformed_dup
  dup = Util.assert_true dup
          (let (f, stk) = dup in
           wellformed_dts_focus (List.null stk) f &&
             (Tree_stack.wellformed_ts stk && wellformed_dup_1 dup));;

let rec wellformed_dts_state
  s = Util.assert_true s
        (match s with Dts_down a -> Find_tree_stack.wellformed_fts a
          | Dts_up (f, stk) -> wellformed_dup (f, stk)
          | Dts_finished a ->
            Tree.wellformed_tree (Some Constants.Small_root_node_or_leaf) a);;


end;;


module Insert_tree_stack : sig
  type its_t = Inserting_one of Tree.tree |
    Inserting_two of (Tree.tree * (Key_value_types.key * Tree.tree))[@@deriving yojson]
  type its_state_t =
    Its_down of (Find_tree_stack.fts_state_t * Key_value_types.value_t) |
    Its_up of
      ((its_t, unit) Tree_stack.core_t_ext *
        ((Key_value_types.key list * Tree.tree list), unit)
          Tree_stack.core_t_ext list)[@@deriving yojson]
  val step_its : its_state_t -> its_state_t option
  val mk_its_state :
    Key_value_types.key -> Key_value_types.value_t -> Tree.tree -> its_state_t
  val focus_to_leaves :
    (its_t, unit) Tree_stack.core_t_ext ->
      ((Key_value_types.key * Key_value_types.value_t) list) list
  val wf_its_trans : its_state_t -> its_state_t -> bool
  val dest_its_state : its_state_t -> Tree.tree option
  val wellformed_its_state : its_state_t -> bool
end = struct

type its_t = Inserting_one of Tree.tree |
  Inserting_two of (Tree.tree * (Key_value_types.key * Tree.tree))[@@deriving yojson];;

type its_state_t =
  Its_down of (Find_tree_stack.fts_state_t * Key_value_types.value_t) |
  Its_up of
    ((its_t, unit) Tree_stack.core_t_ext *
      ((Key_value_types.key list * Tree.tree list), unit)
        Tree_stack.core_t_ext list)[@@deriving yojson];;

let rec step_focus
  p f = let k = Util.rev_apply p Tree_stack.f_k in
        let (ks, _) = Util.rev_apply p Tree_stack.f_t in
        let (_, (ts1, (ks1, (_, (ks2, ts2))))) = Tree_stack.nf_to_aux k p in
        let t =
          (match Util.rev_apply f Tree_stack.f_t
            with Inserting_one t ->
              Inserting_one (Tree.Node (ks, ts1 @ [t] @ ts2))
            | Inserting_two (tl, (ka, tr)) ->
              let ksa = ks1 @ [ka] @ ks2 in
              let ts = ts1 @ [tl; tr] @ ts2 in
              (match
                Arith.less_eq_nat (List.size_list ksa) Constants.max_node_keys
                with true -> Inserting_one (Tree.Node (ksa, ts))
                | false ->
                  let (ks_ts1, (kb, ks_ts2)) = Key_value.split_node (ksa, ts) in
                  Inserting_two (Tree.Node ks_ts1, (kb, Tree.Node ks_ts2))))
          in
        Util.rev_apply p (Tree_stack.with_t (fun _ -> t));;

let rec step_up
  iu = let (f, stk) = iu in
       (match stk
         with [] ->
           (match Util.rev_apply f Tree_stack.f_t with Inserting_one _ -> None
             | Inserting_two (t1, (k, t2)) ->
               Some (Util.rev_apply f
                       (Tree_stack.with_t
                         (fun _ -> Inserting_one (Tree.Node ([k], [t1; t2])))),
                      stk))
         | x :: xs -> Some (step_focus x f, xs));;

let rec its_to_h
  its = (match its with Inserting_one a -> Tree.height a
          | Inserting_two (t1, (_, _)) -> Tree.height t1);;

let rec step_bottom
  down =
    let (fts, v0) = down in
    let (f, stk) = Util.rev_apply fts Find_tree_stack.dest_fts_state in
    let k = Util.rev_apply f Tree_stack.f_k in
    (match Util.rev_apply f Tree_stack.f_t
      with Tree.Node _ ->
        Util.failwitha
          ['s'; 't'; 'e'; 'p'; '_'; 'b'; 'o'; 't'; 't'; 'o'; 'm'; ':'; ' '; 'i';
            'm'; 'p'; 'o'; 's'; 's'; 'i'; 'b'; 'l'; 'e'; ','; ' '; 'f'; 'i';
            'n'; 'd'; ' '; 'r'; 'e'; 't'; 'u'; 'r'; 'n'; 's'; ' '; 'l'; 'e';
            'a'; 'f']
      | Tree.Leaf kvs ->
        let kvs2 = Key_value.kvs_insert k v0 kvs in
        let its =
          (match Arith.less_eq_nat (List.size_list kvs2) Constants.max_leaf_size
            with true -> Inserting_one (Tree.Leaf kvs2)
            | false ->
              let (left, (ka, right)) = Key_value.split_leaf kvs2 in
              Inserting_two (Tree.Leaf left, (ka, Tree.Leaf right)))
          in
        Some (Util.rev_apply f (Tree_stack.with_t (fun _ -> its)), stk));;

let rec step_its
  its = (match its
          with Its_down (fts, v0) ->
            (match Find_tree_stack.step_fts fts
              with None ->
                Util.rev_apply (step_bottom (fts, v0))
                  (Option.map_option (fun a -> Its_up a))
              | Some ftsa -> Some (Its_down (ftsa, v0)))
          | Its_up iu ->
            Util.rev_apply (step_up iu)
              (Option.map_option (fun a -> Its_up a)));;

let rec its_to_tss
  its = (match its with Inserting_one t -> [[t]]
          | Inserting_two (t1, (_, t2)) -> [[t1; t2]]);;

let rec its_to_keys
  its = Util.rev_apply (Util.rev_apply its its_to_tss) Tree.tss_to_keys;;

let rec mk_its_state
  k v t = let fts = Find_tree_stack.mk_fts_state k t in
          Its_down (fts, v);;

let rec focus_to_leaves
  f = let (_, (tss1, (_, (its, (_, tss2))))) =
        Util.rev_apply f Tree_stack.dest_core in
      Util.rev_apply (tss1 @ Util.rev_apply its its_to_tss @ tss2)
        Tree.tss_to_leaves;;

let rec wf_its_trans
  s1 s2 =
    Util.assert_true (s1, s2)
      (match (s1, s2)
        with (Its_down (fts, v), Its_down (ftsa, va)) ->
          Find_tree_stack.wf_fts_trans fts ftsa &&
            Key_value_types.equal_value_ta va v
        | (Its_down (_, _), Its_up (_, _)) -> true
        | (Its_up (f, _), Its_up (fa, _)) ->
          List.equal_lista
            (List.equal_list
              (Product_Type.equal_prod Key_value_types.equal_key
                Key_value_types.equal_value_t))
            (focus_to_leaves fa) (focus_to_leaves f));;

let rec dest_its_state
  its = (match its with Its_down _ -> None
          | Its_up (f, []) ->
            let a = Util.rev_apply f Tree_stack.f_t in
            (match a with Inserting_one aa -> Some aa
              | Inserting_two _ ->
                Util.failwitha
                  ['d'; 'e'; 's'; 't'; '_'; 'i'; 't'; 's'; '_'; 's'; 't'; 'a';
                    't'; 'e'; ':'; ' '; 'i'; 'm'; 'p'; 'o'; 's'; 's'; 'i'; 'b';
                    'l'; 'e'])
          | Its_up (_, _ :: _) -> None);;

let rec wellformed_its
  stack_empty its =
    Util.assert_true (stack_empty, its)
      (match its
        with Inserting_one t ->
          let ms =
            (match stack_empty
              with true -> Some Constants.Small_root_node_or_leaf
              | false -> None)
            in
          Tree.wellformed_tree ms t
        | Inserting_two (t1, (k, t2)) ->
          Arith.equal_nat (Tree.height t2) (Tree.height t1) &&
            (Tree.wellformed_tree None t1 &&
              (Tree.wellformed_tree None t2 &&
                (Key_value.check_keys None (Util.rev_apply t1 Tree.tree_to_keys)
                   (Some k) &&
                  Key_value.check_keys (Some k)
                    (Util.rev_apply t2 Tree.tree_to_keys) None))));;

let rec wellformed_its_focus
  stack_empty f =
    Util.assert_true (stack_empty, f)
      (let its = Util.rev_apply f Tree_stack.f_t in
       Tree_stack.wf_core (Util.rev_apply its its_to_keys) f &&
         wellformed_its stack_empty its);;

let rec wellformed_iup_1
  iu = Util.assert_true iu
         (match iu with (_, []) -> true
           | (f, p :: _) ->
             Tree_stack.equal_core_t_exta Product_Type.equal_unit
               Product_Type.equal_unit (Util.rev_apply f Tree_stack.without_t)
               (Util.rev_apply (Tree_stack.mk_child p) Tree_stack.without_t) &&
               Arith.equal_nat
                 (Util.rev_apply (Util.rev_apply f Tree_stack.f_t) its_to_h)
                 (Util.rev_apply
                   (Util.rev_apply (Util.rev_apply p Tree_stack.mk_child)
                     Tree_stack.f_t)
                   Tree.height));;

let rec wellformed_iup
  iu = Util.assert_true iu
         (let (f, stk) = iu in
          wellformed_its_focus (List.null stk) f &&
            (Tree_stack.wellformed_ts stk && wellformed_iup_1 iu));;

let rec wellformed_its_state
  its = Util.assert_true its
          (match its
            with Its_down (fts, _) -> Find_tree_stack.wellformed_fts fts
            | Its_up (f, stk) -> wellformed_iup (f, stk));;


end;;




(* more below \/ *)














































module Json = struct

  let dts_state_to_string s = (
    s|>Delete_tree_stack.dts_state_t_to_yojson|>Yojson.Safe.pretty_to_string)

  let its_state_to_string s = (
    s|>Insert_tree_stack.its_state_t_to_yojson|>Yojson.Safe.pretty_to_string)

  let fts_state_to_string s = (
    s|>Find_tree_stack.fts_state_t_to_yojson|>Yojson.Safe.pretty_to_string)


end




end
(* end file *)

