(** This file is exported from Isabelle, and lightly patched (eg to
   include this comment!). The OCaml interfaces wrap this basic
   functionality. *)

let check_flag = ref true

module type MONAD = sig
   type ('a, 'b) mm
   val bind : ('a -> ('b, 'c) mm) -> ('a, 'c) mm -> ('b, 'c) mm
   val fmap : ('a -> 'b) -> ('a, 'c) mm -> ('b, 'c) mm
   val return : 'a -> ('a, 'b) mm
end




module Fun : sig
  val id : 'a -> 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Product_Type : sig
  val equal_prod : 'a HOL.equal -> 'b HOL.equal -> ('a * 'b) HOL.equal
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

end;; (*struct Product_Type*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

end;; (*struct Orderings*)

module Arith : sig
  type nat
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat Orderings.ord
  type int = Int_of_integer of Big_int.big_int
  type num = One | Bit0 of num | Bit1 of num
  val plus_nat : nat -> nat -> nat
  val one_nat : nat
  val suc : nat -> nat
  val less_int : int -> int -> bool
  val int_of_nat : nat -> int
  val zero_int : int
  val zero_nat : nat
  val nat_of_integer : Big_int.big_int -> nat
  val equal_int : int -> int -> bool
  val minus_int : int -> int -> int
  val less_eq_int : int -> int -> bool
  val minus_nat : nat -> nat -> nat
  val divide_nat : nat -> nat -> nat
end = struct

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({HOL.equal = equal_nata} : nat HOL.equal);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let ord_nat =
  ({Orderings.less_eq = less_eq_nat; Orderings.less = less_nat} :
    nat Orderings.ord);;

let ord_integer =
  ({Orderings.less_eq = Big_int.le_big_int; Orderings.less = Big_int.lt_big_int}
    : Big_int.big_int Orderings.ord);;

type int = Int_of_integer of Big_int.big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec less_int
  k l = Big_int.lt_big_int (integer_of_int k) (integer_of_int l);;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let zero_int : int = Int_of_integer Big_int.zero_big_int;;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec sgn_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int then Big_int.zero_big_int
        else (if Big_int.lt_big_int k Big_int.zero_big_int
               then (Big_int.minus_big_int (Big_int.big_int_of_int 1))
               else (Big_int.big_int_of_int 1)));;

let rec divmod_integer
  k l = (if Big_int.eq_big_int k Big_int.zero_big_int
          then (Big_int.zero_big_int, Big_int.zero_big_int)
          else (if Big_int.eq_big_int l Big_int.zero_big_int
                 then (Big_int.zero_big_int, k)
                 else Fun.comp
                        (Fun.comp Product_Type.apsnd Big_int.mult_big_int)
                        sgn_integer l
                        (if Big_int.eq_big_int (sgn_integer k) (sgn_integer l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else (let (r, s) =
                                  Big_int.quomod_big_int (Big_int.abs_big_int k)
                                    (Big_int.abs_big_int l)
                                  in
                                 (if Big_int.eq_big_int s Big_int.zero_big_int
                                   then (Big_int.minus_big_int r,
  Big_int.zero_big_int)
                                   else (Big_int.sub_big_int
   (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
  Big_int.sub_big_int (Big_int.abs_big_int l) s))))));;

let rec nat_of_integer
  k = Nat (Orderings.max ord_integer Big_int.zero_big_int k);;

let rec equal_int
  k l = Big_int.eq_big_int (integer_of_int k) (integer_of_int l);;

let rec minus_int
  k l = Int_of_integer
          (Big_int.sub_big_int (integer_of_int k) (integer_of_int l));;

let rec less_eq_int
  k l = Big_int.le_big_int (integer_of_int k) (integer_of_int l);;

let rec minus_nat
  m n = Nat (Orderings.max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let rec divide_integer k l = Product_Type.fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

end;; (*struct Arith*)

module Lista : sig
  val nth : 'a list -> Arith.nat -> 'a
  val rev : 'a list -> 'a list
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val null : 'a list -> bool
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val list_ex : ('a -> bool) -> 'a list -> bool
  val map : ('a -> 'b) -> 'a list -> 'b list
  val list_all : ('a -> bool) -> 'a list -> bool
  val size_list : 'a list -> Arith.nat
  val equal_list : 'a HOL.equal -> 'a list -> 'a list -> bool
end = struct

let rec nth
  (x :: xs) n =
    (if Arith.equal_nata n Arith.zero_nat then x
      else nth xs (Arith.minus_nat n Arith.one_nat));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec upt
  i j = (if Arith.less_nat i j then i :: upt (Arith.suc i) j else []);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec foldr f x1 = match f, x1 with f, [] -> Fun.id
                | f, x :: xs -> Fun.comp (f x) (foldr f xs);;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec hd (x21 :: x22) = x21;;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec gen_length
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.suc n) xs
    | n, [] -> n;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec size_list x = gen_length Arith.zero_nat x;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

end;; (*struct Lista*)

module Set : sig
  type 'a set = Set of 'a list | Coset of 'a list
  val ball : 'a set -> ('a -> bool) -> bool
  val is_empty : 'a set -> bool
end = struct

type 'a set = Set of 'a list | Coset of 'a list;;

let rec ball (Set xs) p = Lista.list_all p xs;;

let rec is_empty (Set xs) = Lista.null xs;;

end;; (*struct Set*)

module Constants_and_size_types : sig
  type constants =
    Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat
  type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf [@@deriving yojson]
  val make_constants :
    Arith.nat -> Arith.nat -> Arith.nat -> Arith.nat -> constants
  val max_leaf_size : constants -> Arith.nat
  val max_node_keys : constants -> Arith.nat
  val min_leaf_size : constants -> Arith.nat
  val min_node_keys : constants -> Arith.nat
end = struct

type constants =
  Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat;;

type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf [@@deriving yojson];;

let rec make_constants a b c d = Make_constants (a, b, c, d);;

let rec max_leaf_size (Make_constants (x1, x2, x3, x4)) = x2;;

let rec max_node_keys (Make_constants (x1, x2, x3, x4)) = x4;;

let rec min_leaf_size (Make_constants (x1, x2, x3, x4)) = x1;;

let rec min_node_keys (Make_constants (x1, x2, x3, x4)) = x3;;

end;; (*struct Constants_and_size_types*)

module Option : sig
  val is_none : 'a option -> bool
end = struct

let rec is_none = function Some x -> false
                  | None -> true;;

end;; (*struct Option*)

module A_start_here : sig
  type error = String_error of string [@@deriving yojson]
  val from_to : Arith.nat -> Arith.nat -> Arith.nat list
  val is_Nil : 'a list -> bool
  val rev_apply : 'a -> ('a -> 'b) -> 'b
  val failwitha : string -> 'a
  val iter_step : ('a -> 'a option) -> 'a -> 'a
  val check_true : (unit -> bool) -> bool
  val assert_true : bool -> bool
  val impossible1 : string -> 'a
  val max_of_list : Arith.nat list -> Arith.nat
  val from_to_tests : bool
  val get_check_flag : unit -> bool
end = struct

type error = String_error of string [@@deriving yojson];;

let rec from_to x y = Lista.upt x (Arith.suc y);;

let rec is_Nil x = (match x with [] -> true | _ :: _ -> false);;

let rec rev_apply x f = f x;;

let rec failwitha x = failwith x;;

let rec iter_step
  f x = (let a = f x in (match a with None -> x | Some aa -> iter_step f aa));;

let rec check_true f = if !check_flag then (let b = f () in assert(b);b) else true;;

let rec assert_true b = (if b then b else failwitha "assert_true");;

let rec impossible1 x = failwitha x;;

let rec max_of_list
  xs = Lista.foldr (Orderings.max Arith.ord_nat) xs Arith.zero_nat;;

let from_to_tests : bool
  = check_true
      (fun _ ->
        (let _ =
           assert_true
             (Lista.equal_list Arith.equal_nat
               (from_to (Arith.nat_of_integer (Big_int.big_int_of_int 3))
                 (Arith.nat_of_integer (Big_int.big_int_of_int 5)))
               [Arith.nat_of_integer (Big_int.big_int_of_int 3);
                 Arith.nat_of_integer (Big_int.big_int_of_int 4);
                 Arith.nat_of_integer (Big_int.big_int_of_int 5)])
           in
         let _ =
           assert_true
             (Lista.equal_list Arith.equal_nat
               (from_to (Arith.nat_of_integer (Big_int.big_int_of_int 3))
                 (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
               [Arith.nat_of_integer (Big_int.big_int_of_int 3)])
           in
         let _ =
           assert_true
             (Lista.null
               (from_to (Arith.nat_of_integer (Big_int.big_int_of_int 3))
                 (Arith.nat_of_integer (Big_int.big_int_of_int 2))))
           in
          true));;

let rec get_check_flag uu = !check_flag

end;; (*struct A_start_here*)

module Key_value : sig
  type compare_t = LT | EQ | GT [@@deriving yojson]
  val key_eq : ('a -> 'a -> Arith.int) -> 'a -> 'a -> bool
  val key_le : ('a -> 'a -> Arith.int) -> 'a -> 'a -> bool
  val key_lt : ('a -> 'a -> Arith.int) -> 'a -> 'a -> bool
  val check_keys :
    ('a -> 'a -> Arith.int) -> 'a option -> 'a Set.set -> 'a option -> bool
  val ck_tests : bool
  val ck2_tests : bool
  val ordered_key_list : ('a -> 'a -> Arith.int) -> 'a list -> bool
  val okl_tests : bool
  val kvs_insert_tests : bool
end = struct

type compare_t = LT | EQ | GT [@@deriving yojson];;

let rec key_eq ord k1 k2 = Arith.equal_int (ord k1 k2) Arith.zero_int;;

let rec key_le ord k1 k2 = Arith.less_eq_int (ord k1 k2) Arith.zero_int;;

let rec key_lt ord k1 k2 = Arith.less_int (ord k1 k2) Arith.zero_int;;

let rec nat_ord
  x y = (let n2i = Arith.int_of_nat in Arith.minus_int (n2i x) (n2i y));;

let rec check_keys
  cmp kl ks kr =
    (let b1 =
       (match kl with None -> true | Some kla -> Set.ball ks (key_le cmp kla))
       in
     let a =
       (match kr with None -> true
         | Some kra -> Set.ball ks (fun k -> key_lt cmp k kra))
       in
      b1 && a);;

let ck_tests : bool
  = A_start_here.check_true
      (fun _ ->
        (let _ =
           A_start_here.assert_true
             (check_keys nat_ord (Some Arith.one_nat)
               (Set.Set
                 [Arith.one_nat;
                   Arith.nat_of_integer (Big_int.big_int_of_int 2);
                   Arith.nat_of_integer (Big_int.big_int_of_int 3)])
               (Some (Arith.nat_of_integer (Big_int.big_int_of_int 4))))
           in
         let _ =
           A_start_here.assert_true
             (not (check_keys nat_ord (Some Arith.one_nat)
                    (Set.Set
                      [Arith.one_nat;
                        Arith.nat_of_integer (Big_int.big_int_of_int 2);
                        Arith.nat_of_integer (Big_int.big_int_of_int 3)])
                    (Some (Arith.nat_of_integer (Big_int.big_int_of_int 3)))))
           in
          true));;

let rec check_keys_2
  cmp xs l ks u zs =
    (match Option.is_none l with true -> Set.is_empty xs | false -> true) &&
      ((match Option.is_none u with true -> Set.is_empty zs | false -> true) &&
        (check_keys cmp None xs l &&
          (check_keys cmp l ks u && check_keys cmp u zs None)));;

let ck2_tests : bool
  = A_start_here.check_true
      (fun _ ->
        (let _ =
           A_start_here.assert_true
             (check_keys_2 nat_ord (Set.Set [Arith.zero_nat])
               (Some Arith.one_nat)
               (Set.Set
                 [Arith.one_nat;
                   Arith.nat_of_integer (Big_int.big_int_of_int 2);
                   Arith.nat_of_integer (Big_int.big_int_of_int 3)])
               (Some (Arith.nat_of_integer (Big_int.big_int_of_int 4)))
               (Set.Set
                 [Arith.nat_of_integer (Big_int.big_int_of_int 4);
                   Arith.nat_of_integer (Big_int.big_int_of_int 5)]))
           in
          true));;

let rec ordered_key_list
  ord ks =
    Arith.less_nat (Lista.size_list ks)
      (Arith.nat_of_integer (Big_int.big_int_of_int 2)) ||
      Lista.list_all
        (fun i ->
          key_lt ord (Lista.nth ks i)
            (Lista.nth ks (Arith.plus_nat i Arith.one_nat)))
        (A_start_here.from_to Arith.zero_nat
          (Arith.minus_nat (Lista.size_list ks)
            (Arith.nat_of_integer (Big_int.big_int_of_int 2))));;

let okl_tests : bool
  = A_start_here.check_true
      (fun _ ->
        (let _ =
           A_start_here.assert_true
             (ordered_key_list nat_ord
               [Arith.zero_nat; Arith.one_nat;
                 Arith.nat_of_integer (Big_int.big_int_of_int 2);
                 Arith.nat_of_integer (Big_int.big_int_of_int 3)])
           in
         let _ =
           A_start_here.assert_true
             (not (ordered_key_list nat_ord
                    [Arith.zero_nat; Arith.one_nat; Arith.one_nat;
                      Arith.nat_of_integer (Big_int.big_int_of_int 3)]))
           in
          true));;

let rec kvs_insert
  k_cmp k v kvs =
    A_start_here.rev_apply
      (A_start_here.iter_step
        (fun a ->
          (match a with (_, []) -> None
            | (kvsb, (ka, va) :: kvsa) ->
              (match key_lt k_cmp k ka with true -> None
                | false ->
                  (match key_eq k_cmp k ka with true -> Some (kvsb, kvsa)
                    | false -> Some ((ka, va) :: kvsb, kvsa)))))
        ([], kvs))
      (fun (kvsa, a) -> Lista.rev ((k, v) :: kvsa) @ a);;

let kvs_insert_tests : bool
  = A_start_here.check_true
      (fun _ ->
        (let _ =
           A_start_here.assert_true
             (Lista.equal_list
               (Product_Type.equal_prod Arith.equal_nat Arith.equal_nat)
               (kvs_insert nat_ord
                 (Arith.nat_of_integer (Big_int.big_int_of_int 2))
                 (Arith.nat_of_integer (Big_int.big_int_of_int 2))
                 (Lista.map (fun x -> (x, x))
                   [Arith.zero_nat; Arith.one_nat;
                     Arith.nat_of_integer (Big_int.big_int_of_int 3);
                     Arith.nat_of_integer (Big_int.big_int_of_int 4)]))
               (Lista.map (fun x -> (x, x))
                 [Arith.zero_nat; Arith.one_nat;
                   Arith.nat_of_integer (Big_int.big_int_of_int 2);
                   Arith.nat_of_integer (Big_int.big_int_of_int 3);
                   Arith.nat_of_integer (Big_int.big_int_of_int 4)]))
           in
         let _ =
           A_start_here.assert_true
             (Lista.equal_list
               (Product_Type.equal_prod Arith.equal_nat Arith.equal_nat)
               (kvs_insert nat_ord
                 (Arith.nat_of_integer (Big_int.big_int_of_int 6))
                 (Arith.nat_of_integer (Big_int.big_int_of_int 6))
                 (Lista.map (fun x -> (x, x))
                   [Arith.zero_nat; Arith.one_nat;
                     Arith.nat_of_integer (Big_int.big_int_of_int 3);
                     Arith.nat_of_integer (Big_int.big_int_of_int 4)]))
               (Lista.map (fun x -> (x, x))
                 [Arith.zero_nat; Arith.one_nat;
                   Arith.nat_of_integer (Big_int.big_int_of_int 3);
                   Arith.nat_of_integer (Big_int.big_int_of_int 4);
                   Arith.nat_of_integer (Big_int.big_int_of_int 6)]))
           in
          true));;

end;; (*struct Key_value*)

module Stacks_and_frames : sig
  type ('a, 'b, 'c, 'd) stk_frame = Frm of ('a * ('b * ('c * 'd))) [@@deriving yojson]
  val dest_Frm : ('a, 'b, 'c, 'd) stk_frame -> 'a * ('b * ('c * 'd))
  val make_frame :
    ('a -> 'a -> Arith.int) ->
      'a -> 'b -> 'a list ->
                    'b list ->
                      (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                        stk_frame *
                        'b
  val unsplit_node :
    ('a list * 'b list) * (('a list * 'b list) * ('b list * 'a list)) ->
      'b list * 'a list
end = struct

type ('a, 'b, 'c, 'd) stk_frame = Frm of ('a * ('b * ('c * 'd))) [@@deriving yojson];;

let rec dest_Frm (Frm (a, (b, (c, d)))) = (a, (b, (c, d)));;

let rec make_frame
  k_cmp k r_parent ks rs =
    A_start_here.rev_apply
      (A_start_here.iter_step
        (fun (a, b) ->
          (let (rsa, ksa) = a in
            (fun (ksaa, rsaa) ->
              (match ksaa with [] -> None
                | ka :: ksab ->
                  (match Key_value.key_lt k_cmp k ka with true -> None
                    | false ->
                      (let (r, rsab) = (Lista.hd rsaa, Lista.tl rsaa) in
                        Some ((r :: rsa, ka :: ksa), (ksab, rsab)))))))
            b)
        (([], []), (ks, rs)))
      (fun (a, b) ->
        (let (rsa, ksa) = a in
          (fun (ksaa, rsaa) ->
            (let r = Lista.hd rsaa in
              (Frm ((rsa, ksa), (r, ((ksaa, Lista.tl rsaa), r_parent))), r))))
          b);;

let rec unsplit_node
  x = (let a = x in
       let (aa, b) = a in
        (let (rs1, ks1) = aa in
          (fun (ab, ba) ->
            (let (rs2, ks2) = ab in
              (fun (ks3, rs3) ->
                (Lista.rev ks1 @ ks2 @ ks3, Lista.rev rs1 @ rs2 @ rs3)))
              ba))
          b);;

end;; (*struct Stacks_and_frames*)

module Disk_node : sig
  type ('a, 'b, 'c, 'd) dnode = Disk_node of ('a list * 'b list) |
    Disk_leaf of 'c  [@@deriving yojson]
  type ('a, 'b, 'c) leaf_ops =
    Make_leaf_ops of
      ('a -> 'b -> 'c -> 'c) * ('c -> Arith.nat) * ('c -> ('a * 'b) list) *
        (('a * 'b) list -> 'c)
  val dest_Disk_leaf : ('a, 'b, 'c, unit) dnode -> 'c
  val dest_Disk_node : ('a, 'b, 'c, unit) dnode -> 'a list * 'b list
  val mk_leaf : ('a, 'b, 'c) leaf_ops -> ('a * 'b) list -> 'c
  val leaf_kvs : ('a, 'b, 'c) leaf_ops -> 'c -> ('a * 'b) list
  val leaf_insert : ('a, 'b, 'c) leaf_ops -> 'a -> 'b -> 'c -> 'c
  val leaf_length : ('a, 'b, 'c) leaf_ops -> 'c -> Arith.nat
end = struct

type ('a, 'b, 'c, 'd) dnode = Disk_node of ('a list * 'b list) |
  Disk_leaf of 'c  [@@deriving yojson];;

type ('a, 'b, 'c) leaf_ops =
  Make_leaf_ops of
    ('a -> 'b -> 'c -> 'c) * ('c -> Arith.nat) * ('c -> ('a * 'b) list) *
      (('a * 'b) list -> 'c);;

let rec dest_Disk_leaf
  f = (match f with Disk_node _ -> A_start_here.failwitha "dest_Disk_leaf"
        | Disk_leaf x -> x);;

let rec dest_Disk_node
  f = (match f with Disk_node x -> x
        | Disk_leaf _ -> A_start_here.failwitha "dest_Disk_node");;

let rec mk_leaf (Make_leaf_ops (x1, x2, x3, x4)) = x4;;

let rec leaf_kvs (Make_leaf_ops (x1, x2, x3, x4)) = x3;;

let rec leaf_insert (Make_leaf_ops (x1, x2, x3, x4)) = x1;;

let rec leaf_length (Make_leaf_ops (x1, x2, x3, x4)) = x2;;

end;; (*struct Disk_node*)

module Find_state : sig
  type ('a, 'b, 'c, 'd) find_state =
    F_down of
      ('b * ('a * ('b * (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                          Stacks_and_frames.stk_frame list)))
    | F_finished of
        ('b * ('a * ('b * ('c * (('b list * 'a list), 'b, ('a list * 'b list),
                                  'b)
                                  Stacks_and_frames.stk_frame list))))  [@@deriving yojson]
  val dest_F_finished :
    ('a, 'b, 'c, unit) find_state ->
      ('b * ('a * ('b * ('c * (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                                Stacks_and_frames.stk_frame list)))) option
  val make_initial_find_state : 'a -> 'b -> ('a, 'b, 'c, unit) find_state
end = struct

type ('a, 'b, 'c, 'd) find_state =
  F_down of
    ('b * ('a * ('b * (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                        Stacks_and_frames.stk_frame list)))
  | F_finished of
      ('b * ('a * ('b * ('c * (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                                Stacks_and_frames.stk_frame list))))  [@@deriving yojson];;

let rec dest_F_finished
  fs = (match fs with F_down _ -> None
         | F_finished (r0, (k, (r, (kvs, stk)))) ->
           Some (r0, (k, (r, (kvs, stk)))));;

let rec make_initial_find_state k r = F_down (r, (k, (r, [])));;

end;; (*struct Find_state*)

module Insert_state : sig
  type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c)) [@@deriving yojson]
  type ('a, 'b, 'c, 'd) insert_state =
    I_down of (('a, 'c, 'd, unit) Find_state.find_state * 'b) |
    I_up of
      (('a, 'b, 'c) i12_t *
        (('c list * 'a list), 'c, ('a list * 'c list), 'c)
          Stacks_and_frames.stk_frame list)
    | I_finished of 'c | I_finished_with_mutate  [@@deriving yojson]
  val split_leaf :
    Constants_and_size_types.constants ->
      ('a * 'b) list -> ('a * 'b) list * ('a * ('a * 'b) list)
  val split_node :
    Constants_and_size_types.constants ->
      'a list * 'b list -> ('a list * 'b list) * ('a * ('a list * 'b list))
  val make_initial_insert_state :
    'a -> 'b -> 'c -> ('b, 'c, 'a, 'd) insert_state
end = struct

type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c)) [@@deriving yojson];;

type ('a, 'b, 'c, 'd) insert_state =
  I_down of (('a, 'c, 'd, unit) Find_state.find_state * 'b) |
  I_up of
    (('a, 'b, 'c) i12_t *
      (('c list * 'a list), 'c, ('a list * 'c list), 'c)
        Stacks_and_frames.stk_frame list)
  | I_finished of 'c | I_finished_with_mutate [@@deriving yojson];;

let rec split_leaf
  cs kvs =
    (let _ = A_start_here.assert_true true in
     let min = A_start_here.rev_apply cs Constants_and_size_types.min_leaf_size
       in
      A_start_here.rev_apply
        (A_start_here.iter_step
          (fun (kvsb, (kvsa, len_kvs)) ->
            (match Arith.less_eq_nat len_kvs min with true -> None
              | false ->
                (match kvsa with [] -> A_start_here.impossible1 "split_leaf"
                  | (k, v) :: kvsaa ->
                    Some ((k, v) :: kvsb,
                           (kvsaa, Arith.minus_nat len_kvs Arith.one_nat)))))
          ([], (kvs, Lista.size_list kvs)))
        (fun (kvsb, (kvsa, _)) ->
          (Lista.rev kvsb,
            (A_start_here.rev_apply (Lista.hd kvsa) Product_Type.fst, kvsa))));;

let rec split_node
  cs n =
    (let (ks, rs) = n in
     let l =
       Arith.divide_nat (Lista.size_list ks)
         (Arith.nat_of_integer (Big_int.big_int_of_int 2))
       in
     let la =
       Orderings.max Arith.ord_nat
         (A_start_here.rev_apply cs Constants_and_size_types.min_node_keys) l
       in
      A_start_here.rev_apply
        (A_start_here.iter_step
          (fun (ksb, (rsb, (ksa, rsa))) ->
            (match (ksa, rsa)
              with ([], _) -> A_start_here.impossible1 "split_node"
              | (_ :: _, []) -> A_start_here.impossible1 "split_node"
              | (k :: ksaa, r :: rsaa) ->
                (match Arith.less_nat (Lista.size_list ksb) la
                  with true -> Some (k :: ksb, (r :: rsb, (ksaa, rsaa)))
                  | false -> None)))
          ([], ([], (ks, rs))))
        (fun (ksb, (rsb, (ksa, rsa))) ->
          (let (k :: ksaa, r :: rsaa) = (ksa, rsa) in
            ((Lista.rev ksb, Lista.rev (r :: rsb)), (k, (ksaa, rsaa))))));;

let rec make_initial_insert_state
  r k v = (let f = Find_state.make_initial_find_state k r in I_down (f, v));;

end;; (*struct Insert_state*)

module Delete_state : sig
  type ('a, 'b, 'c) del_t = D_small_leaf of ('a * 'b) list |
    D_small_node of ('a list * 'c list) | D_updated_subtree of 'c  [@@deriving yojson]
  type ('a, 'b, 'c, 'd) delete_state =
    D_down of (('a, 'c, 'd, unit) Find_state.find_state * 'c) |
    D_up of
      (('a, 'b, 'c) del_t *
        ((('c list * 'a list), 'c, ('a list * 'c list), 'c)
           Stacks_and_frames.stk_frame list *
          'c))
    | D_finished of 'c  [@@deriving yojson]
  val dest_D_finished : ('a, 'b, 'c, 'd) delete_state -> 'c option
  val make_initial_delete_state : 'a -> 'b -> ('b, 'c, 'a, 'd) delete_state
end = struct

type ('a, 'b, 'c) del_t = D_small_leaf of ('a * 'b) list |
  D_small_node of ('a list * 'c list) | D_updated_subtree of 'c  [@@deriving yojson];;

type ('a, 'b, 'c, 'd) delete_state =
  D_down of (('a, 'c, 'd, unit) Find_state.find_state * 'c) |
  D_up of
    (('a, 'b, 'c) del_t *
      ((('c list * 'a list), 'c, ('a list * 'c list), 'c)
         Stacks_and_frames.stk_frame list *
        'c))
  | D_finished of 'c [@@deriving yojson];;

let rec dest_D_finished
  x = (match x with D_down _ -> None | D_up _ -> None
        | D_finished a -> Some a);;

let rec make_initial_delete_state
  r k = D_down (Find_state.make_initial_find_state k r, r);;

end;; (*struct Delete_state*)

module Sum_Type : sig
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

end;; (*struct Sum_Type*)

module Tree : sig
  type ('a, 'b) tree = Node of ('a list * ('a, 'b) tree list) |
    Leaf of ('a * 'b) list [@@deriving yojson]
  val wf_tree :
    Constants_and_size_types.constants ->
      Constants_and_size_types.min_size_t option ->
        ('a -> 'a -> Arith.int) -> ('a, 'b) tree -> bool
  val dest_Node : ('a, 'b) tree -> 'a list * ('a, 'b) tree list
  val tree_to_leaves : ('a, 'b) tree -> (('a * 'b) list) list
end = struct

type ('a, 'b) tree = Node of ('a list * ('a, 'b) tree list) |
  Leaf of ('a * 'b) list [@@deriving yojson];;

let rec tree_to_subtrees
  t0 = (match t0
         with Node (_, cs) ->
           t0 :: A_start_here.rev_apply (Lista.map tree_to_subtrees cs)
                   Lista.concat
         | Leaf _ -> [t0]);;

let rec keys_1
  t0 = (match t0 with Node (l, _) -> l
         | Leaf a -> Lista.map Product_Type.fst a);;

let rec keys
  t0 = A_start_here.rev_apply
         (A_start_here.rev_apply (A_start_here.rev_apply t0 tree_to_subtrees)
           (Lista.map keys_1))
         Lista.concat;;

let rec height
  t0 = (match t0
         with Node (_, cs) ->
           Arith.plus_nat Arith.one_nat
             (A_start_here.max_of_list (Lista.map height cs))
         | Leaf _ -> Arith.one_nat);;

let rec forall_subtrees
  p t = Lista.list_all p (A_start_here.rev_apply t tree_to_subtrees);;

let rec get_min_size
  c mt =
    (let min_leaf_size =
       A_start_here.rev_apply c Constants_and_size_types.min_leaf_size in
     let min_node_keys =
       A_start_here.rev_apply c Constants_and_size_types.min_node_keys in
      (match mt
        with (Constants_and_size_types.Small_root_node_or_leaf, Node _) ->
          Arith.one_nat
        | (Constants_and_size_types.Small_root_node_or_leaf, Leaf _) ->
          Arith.zero_nat
        | (Constants_and_size_types.Small_node, Node _) ->
          Arith.minus_nat min_node_keys Arith.one_nat
        | (Constants_and_size_types.Small_node, Leaf _) ->
          A_start_here.failwitha "get_min_size"
        | (Constants_and_size_types.Small_leaf, Node _) ->
          A_start_here.failwitha "get_min_size"
        | (Constants_and_size_types.Small_leaf, Leaf _) ->
          Arith.minus_nat min_leaf_size Arith.one_nat));;

let rec wf_size_1
  c t1 =
    (match t1
      with Node (l, _) ->
        (let n = Lista.size_list l in
          Arith.less_eq_nat Arith.one_nat n &&
            (Arith.less_eq_nat
               (A_start_here.rev_apply c Constants_and_size_types.min_node_keys)
               n &&
              Arith.less_eq_nat n
                (A_start_here.rev_apply c
                  Constants_and_size_types.max_node_keys)))
      | Leaf xs ->
        (let n = Lista.size_list xs in
          Arith.less_eq_nat
            (A_start_here.rev_apply c Constants_and_size_types.min_leaf_size)
            n &&
            Arith.less_eq_nat n
              (A_start_here.rev_apply c
                Constants_and_size_types.max_leaf_size)));;

let rec wf_size
  c ms t0 =
    A_start_here.assert_true
      (match ms with None -> forall_subtrees (wf_size_1 c) t0
        | Some m ->
          (let min = get_min_size c (m, t0) in
            (match t0
              with Node (l, cs) ->
                (let n = Lista.size_list l in
                  Arith.less_eq_nat min n &&
                    (Arith.less_eq_nat n
                       (A_start_here.rev_apply c
                         Constants_and_size_types.max_node_keys) &&
                      Lista.list_all (forall_subtrees (wf_size_1 c)) cs))
              | Leaf xs ->
                (let n = Lista.size_list xs in
                  Arith.less_eq_nat min n &&
                    Arith.less_eq_nat n
                      (A_start_here.rev_apply c
                        Constants_and_size_types.max_leaf_size)))));;

let rec ks_to_max_child_index ks = Lista.size_list ks;;

let min_child_index : Arith.nat = Arith.zero_nat;;

let rec subtree_indexes
  node =
    (let (ks, _) = node in
      A_start_here.from_to min_child_index (ks_to_max_child_index ks));;

let rec index_to_bound
  ks i =
    (let l =
       (if Arith.equal_nata i min_child_index then None
         else Some (Lista.nth ks (Arith.minus_nat i Arith.one_nat)))
       in
     let a =
       (if Arith.less_eq_nat (ks_to_max_child_index ks) i then None
         else Some (Lista.nth ks i))
       in
      (l, a));;

let rec keys_consistent_1
  cmp t0 =
    (match t0
      with Node (ks, rs) ->
        Lista.list_all
          (fun i ->
            (let a = index_to_bound ks i in
             let (l, aa) = a in
              Key_value.check_keys cmp l (Set.Set (keys (Lista.nth rs i))) aa))
          (subtree_indexes (ks, rs))
      | Leaf _ -> true);;

let rec keys_consistent
  cmp t = A_start_here.assert_true (forall_subtrees (keys_consistent_1 cmp) t);;

let rec keys_ordered_1
  cmp t0 =
    A_start_here.rev_apply (A_start_here.rev_apply t0 keys_1)
      (Key_value.ordered_key_list cmp);;

let rec keys_ordered
  cmp t = A_start_here.assert_true (forall_subtrees (keys_ordered_1 cmp) t);;

let rec wf_ks_rs_1
  t0 = (match t0
         with Node (l, cs) ->
           Arith.equal_nata (Arith.plus_nat Arith.one_nat (Lista.size_list l))
             (Lista.size_list cs)
         | Leaf _ -> true);;

let rec wf_ks_rs t0 = A_start_here.assert_true (forall_subtrees wf_ks_rs_1 t0);;

let rec balanced_1
  t0 = (match t0
         with Node (_, cs) ->
           not (Lista.null cs) &&
             Lista.list_all
               (fun c ->
                 Arith.equal_nata (height c)
                   (height (Lista.nth cs Arith.zero_nat)))
               cs
         | Leaf _ -> true);;

let rec balanced t = A_start_here.assert_true (forall_subtrees balanced_1 t);;

let rec wf_tree
  c ms cmp t0 =
    A_start_here.assert_true (let b1 = wf_size c ms t0 in
                              let b2 = wf_ks_rs t0 in
                              let b3 = balanced t0 in
                              let b4 = keys_consistent cmp t0 in
                              let b5 = keys_ordered cmp t0 in
                              let wf = b1 && (b2 && (b3 && (b4 && b5))) in
                               wf);;

let rec dest_Node = function Node (ks, rs) -> (ks, rs)
                    | Leaf uu -> A_start_here.failwitha "dest_Node";;

let rec tree_to_leaves
  t0 = (match t0
         with Node (_, cs) ->
           A_start_here.rev_apply (Lista.map tree_to_leaves cs) Lista.concat
         | Leaf l -> [l]);;

end;; (*struct Tree*)

module Pre_monad : sig
  val dummy : unit
end = struct

let dummy : unit = (let _ = (fun x -> x) in
                    let _ = (fun x -> x) in
                    let _ = (fun x -> x) in
                    let _ = (fun x -> x) in
                    let _ = (fun x -> x) in
                    let _ = (fun x -> x) in
                     ());;

end;; (*struct Pre_monad*)

module Monad : sig
  type ('a, 'b) mm
  val bind : ('a -> ('b, 'c) mm) -> ('a, 'c) mm -> ('b, 'c) mm
  val fmap : ('a -> 'b) -> ('a, 'c) mm -> ('b, 'c) mm
  val return : 'a -> ('a, 'b) mm
end = struct

type ('a, 'b) mm = EMPTY__;;

let rec bind b a = failwith "undefined";;

let rec fmap x y = (let _ = Pre_monad.dummy in A_start_here.failwitha "FIXME");;

let rec return x = failwith "undefined";;

end;; (*struct Monad*)

module Make(Monad:MONAD) = struct
module Post_monad : sig
  type ('a, 'b, 'c) store_ops =
    Make_store_ops of
      ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
        ('a -> 'b -> (('a option), 'c) Monad.mm) *
        ('a list -> (unit, 'c) Monad.mm)
  val iter_m : ('a -> (('a option), 'b) Monad.mm) -> 'a -> ('a, 'b) Monad.mm
  val read : ('a, 'b, 'c) store_ops -> 'a -> ('b, 'c) Monad.mm
  val make_store_ops :
    ('a -> ('b, 'c) Monad.mm) ->
      ('b -> ('a, 'c) Monad.mm) ->
        ('a -> 'b -> (('a option), 'c) Monad.mm) ->
          ('a list -> (unit, 'c) Monad.mm) -> ('a, 'b, 'c) store_ops
  val free : ('a, 'b, 'c) store_ops -> 'a list -> (unit, 'c) Monad.mm
  val wrte : ('a, 'b, 'c) store_ops -> 'b -> ('a, 'c) Monad.mm
  val check_tree_at_r :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) store_ops ->
            'd -> (unit, 'e) Monad.mm
  val rewrite : ('a, 'b, 'c) store_ops -> 'a -> 'b -> (('a option), 'c) Monad.mm
end = struct

type ('a, 'b, 'c) store_ops =
  Make_store_ops of
    ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
      ('a -> 'b -> (('a option), 'c) Monad.mm) *
      ('a list -> (unit, 'c) Monad.mm);;

let rec iter_m
  f x = A_start_here.rev_apply (f x)
          (Monad.bind
            (fun a ->
              (match a with None -> Monad.return x | Some aa -> iter_m f aa)));;

let rec read (Make_store_ops (x1, x2, x3, x4)) = x1;;

let rec get_tree
  leaf_ops store_ops r =
    A_start_here.rev_apply
      (A_start_here.rev_apply r (A_start_here.rev_apply store_ops read))
      (Monad.bind
        (fun a ->
          (match a
            with Disk_node.Disk_node (ks, rs) ->
              A_start_here.rev_apply
                (iter_m
                  (fun aa ->
                    (match aa with (_, []) -> Monad.return None
                      | (ts, ra :: rsa) ->
                        A_start_here.rev_apply (get_tree leaf_ops store_ops ra)
                          (Monad.bind
                            (fun t -> Monad.return (Some (t :: ts, rsa))))))
                  ([], rs))
                (Monad.bind
                  (fun (ts, _) -> Monad.return (Tree.Node (ks, Lista.rev ts))))
            | Disk_node.Disk_leaf kvs ->
              Monad.return
                (Tree.Leaf
                  (A_start_here.rev_apply leaf_ops Disk_node.leaf_kvs kvs)))));;

let rec make_store_ops r w rw f = Make_store_ops (r, w, rw, f);;

let rec free (Make_store_ops (x1, x2, x3, x4)) = x4;;

let rec wrte (Make_store_ops (x1, x2, x3, x4)) = x2;;

let rec check_tree_at_r
  cs k_cmp leaf_ops store_ops r =
    (match A_start_here.get_check_flag ()
      with true ->
        A_start_here.rev_apply (get_tree leaf_ops store_ops r)
          (Monad.bind
            (fun t ->
              (let _ =
                 A_start_here.check_true
                   (fun _ ->
                     Tree.wf_tree cs
                       (Some Constants_and_size_types.Small_root_node_or_leaf)
                       k_cmp t)
                 in
                Monad.return ())))
      | false -> Monad.return ());;

let rec rewrite (Make_store_ops (x1, x2, x3, x4)) = x3;;

end;; (*struct Post_monad*)

module Find : sig
  val find_step :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            ('a, 'd, 'c, unit) Find_state.find_state ->
              (('a, 'd, 'c, unit) Find_state.find_state, 'e) Monad.mm
  val find :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            'd -> 'a -> (('d * ('c * (('d list * 'a list), 'd,
                                       ('a list * 'd list), 'd)
                                       Stacks_and_frames.stk_frame list)),
                          'e)
                          Monad.mm
end = struct

let rec find_step
  cs k_cmp leaf_ops store_ops =
    (let read = A_start_here.rev_apply store_ops Post_monad.read in
      (fun a ->
        (match a
          with Find_state.F_down (r0, (k, (r, stk))) ->
            A_start_here.rev_apply (read r)
              (Monad.fmap
                (fun aa ->
                  (match aa
                    with Disk_node.Disk_node (ks, rs) ->
                      (let (frm, ra) =
                         Stacks_and_frames.make_frame k_cmp k r ks rs in
                        Find_state.F_down (r0, (k, (ra, frm :: stk))))
                    | Disk_node.Disk_leaf leaf ->
                      Find_state.F_finished (r0, (k, (r, (leaf, stk)))))))
          | Find_state.F_finished _ -> A_start_here.failwitha "find_step 1")));;

let rec find_big_step
  cs k_cmp leaf_ops store_ops =
    (let step = find_step cs k_cmp leaf_ops store_ops in
      Post_monad.iter_m
        (fun i ->
          (match i
            with Find_state.F_down _ ->
              A_start_here.rev_apply (step i) (Monad.fmap (fun a -> Some a))
            | Find_state.F_finished _ -> Monad.return None)));;

let rec find
  cs k_cmp leaf_ops store_ops r k =
    (let s = Find_state.make_initial_find_state k r in
      A_start_here.rev_apply (find_big_step cs k_cmp leaf_ops store_ops s)
        (Monad.bind
          (fun a ->
            (match a with Find_state.F_down _ -> A_start_here.failwitha "find 1"
              | Find_state.F_finished (_, (_, (ra, (kvs, stk)))) ->
                Monad.return (ra, (kvs, stk))))));;

end;; (*struct Find*)

module Delete : sig
  val delete_step :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            ('a, 'b, 'd, 'c) Delete_state.delete_state ->
              (('a, 'b, 'd, 'c) Delete_state.delete_state, 'e) Monad.mm
  val delete :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            'd -> 'a -> ('d, 'e) Monad.mm
end = struct

let rec node_steal_right
  store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
      (fun c1 k0 c2 ->
        (let (rs1, ks1) = c1 in
         let (r1 :: rs2, k1 :: ks2) = c2 in
          A_start_here.rev_apply
            (A_start_here.rev_apply
              (Disk_node.Disk_node (ks1 @ [k0], rs1 @ [r1])) write)
            (Monad.bind
              (fun left ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply (Disk_node.Disk_node (ks2, rs2))
                    write)
                  (Monad.bind
                    (fun right -> Monad.return (left, (k1, right)))))))));;

let rec node_merge_right
  store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
      (fun c1 k0 c2 ->
        (let (ks1, rs1) = c1 in
         let (ks2, rs2) = c2 in
          A_start_here.rev_apply
            (Disk_node.Disk_node (ks1 @ [k0] @ ks2, rs1 @ rs2)) write)));;

let rec leaf_steal_right
  leaf_ops store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
     let disk_leaf =
       (fun kvs ->
         Disk_node.Disk_leaf
           (A_start_here.rev_apply leaf_ops Disk_node.mk_leaf kvs))
       in
      (fun c1 (kv1 :: kv2 :: rest) ->
        A_start_here.rev_apply
          (A_start_here.rev_apply (disk_leaf (c1 @ [kv1])) write)
          (Monad.bind
            (fun left ->
              A_start_here.rev_apply
                (A_start_here.rev_apply (disk_leaf (kv2 :: rest)) write)
                (Monad.bind
                  (fun right ->
                    Monad.return (left, (Product_Type.fst kv2, right))))))));;

let rec leaf_merge_right
  leaf_ops store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
     let disk_leaf =
       (fun kvs ->
         Disk_node.Disk_leaf
           (A_start_here.rev_apply leaf_ops Disk_node.mk_leaf kvs))
       in
      (fun c1 c2 ->
        (let kvs = c1 @ c2 in A_start_here.rev_apply (disk_leaf kvs) write)));;

let rec node_steal_left
  store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
      (fun c1 k1 c2 ->
        (let (r1 :: rs1, k0 :: ks0) =
           A_start_here.rev_apply c1 (fun (x, y) -> (Lista.rev x, Lista.rev y))
           in
         let (rs2, ks2) = c2 in
          A_start_here.rev_apply
            (A_start_here.rev_apply
              (Disk_node.Disk_node (Lista.rev ks0, Lista.rev rs1)) write)
            (Monad.bind
              (fun left ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply
                    (Disk_node.Disk_node (k1 :: ks2, r1 :: rs2)) write)
                  (Monad.bind
                    (fun right -> Monad.return (left, (k0, right)))))))));;

let rec node_merge_left store_ops = node_merge_right store_ops;;

let rec leaf_steal_left
  leaf_ops store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
     let disk_leaf =
       (fun kvs ->
         Disk_node.Disk_leaf
           (A_start_here.rev_apply leaf_ops Disk_node.mk_leaf kvs))
       in
      (fun c1 c2 ->
        (let kv1 :: rest = Lista.rev c1 in
          A_start_here.rev_apply
            (A_start_here.rev_apply (disk_leaf (Lista.rev rest)) write)
            (Monad.bind
              (fun left ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply (disk_leaf (kv1 :: c2)) write)
                  (Monad.bind
                    (fun right ->
                      Monad.return
                        (left, (Product_Type.fst kv1, right)))))))));;

let rec leaf_merge_left
  leaf_ops store_ops = leaf_merge_right leaf_ops store_ops;;

let rec post_merge
  cs store_ops krs =
    (let (ks, rs) = krs in
      (match
        Arith.less_nat (Lista.size_list ks)
          (A_start_here.rev_apply cs Constants_and_size_types.min_node_keys)
        with true -> Monad.return (Delete_state.D_small_node (ks, rs))
        | false ->
          A_start_here.rev_apply
            (A_start_here.rev_apply (Disk_node.Disk_node (ks, rs))
              (A_start_here.rev_apply store_ops Post_monad.wrte))
            (Monad.bind
              (fun r -> Monad.return (Delete_state.D_updated_subtree r)))));;

let rec step_up
  cs leaf_ops store_ops du =
    (let (f, stk) = du in
     let (read, write) =
       (A_start_here.rev_apply store_ops Post_monad.read,
         A_start_here.rev_apply store_ops Post_monad.wrte)
       in
     let (leaf_kvs, (leaf_length, _)) =
       (A_start_here.rev_apply leaf_ops Disk_node.leaf_kvs,
         (A_start_here.rev_apply leaf_ops Disk_node.leaf_length,
           A_start_here.rev_apply leaf_ops Disk_node.mk_leaf))
       in
     let post_mergea = post_merge cs store_ops in
      (match stk with [] -> A_start_here.failwitha "delete, step_up"
        | p :: stka ->
          A_start_here.rev_apply
            (match f
              with Delete_state.D_small_leaf kvs ->
                (let (rks, (_, (krs, _))) = Stacks_and_frames.dest_Frm p in
                  (match A_start_here.is_Nil (Product_Type.fst krs)
                    with true ->
                      (let _ =
                         A_start_here.check_true
                           (fun _ ->
                             (match Product_Type.snd rks with [] -> false
                               | _ :: _ -> true))
                         in
                       let (r1 :: rs1, _ :: ks1) = rks in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (A_start_here.rev_apply r1 read)
                            (Monad.fmap Disk_node.dest_Disk_leaf))
                          (Monad.bind
                            (fun left_kvs ->
                              (match
                                Arith.equal_nata (leaf_length left_kvs)
                                  (A_start_here.rev_apply cs
                                    Constants_and_size_types.min_leaf_size)
                                with true ->
                                  A_start_here.rev_apply
                                    (leaf_merge_left leaf_ops store_ops
                                      (leaf_kvs left_kvs) kvs)
                                    (Monad.bind
                                      (fun r ->
A_start_here.rev_apply
  (Stacks_and_frames.unsplit_node ((rs1, ks1), (([r], []), krs))) post_mergea))
                                | false ->
                                  A_start_here.rev_apply
                                    (leaf_steal_left leaf_ops store_ops
                                      (leaf_kvs left_kvs) kvs)
                                    (Monad.bind
                                      (fun (r1a, (k1, r2)) ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (Stacks_and_frames.unsplit_node ((rs1, ks1), (([r1a; r2], [k1]), krs)))
      (fun a -> Disk_node.Disk_node a))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))))))
                    | false ->
                      (let _ =
                         A_start_here.check_true
                           (fun _ ->
                             (match Product_Type.fst krs with [] -> false
                               | _ :: _ -> true))
                         in
                       let (_ :: ks1, r1 :: rs1) = krs in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (A_start_here.rev_apply r1 read)
                            (Monad.fmap Disk_node.dest_Disk_leaf))
                          (Monad.bind
                            (fun right_kvs ->
                              (match
                                Arith.equal_nata (leaf_length right_kvs)
                                  (A_start_here.rev_apply cs
                                    Constants_and_size_types.min_leaf_size)
                                with true ->
                                  A_start_here.rev_apply
                                    (leaf_merge_right leaf_ops store_ops kvs
                                      (leaf_kvs right_kvs))
                                    (Monad.bind
                                      (fun r ->
A_start_here.rev_apply
  (Stacks_and_frames.unsplit_node (rks, (([r], []), (ks1, rs1)))) post_mergea))
                                | false ->
                                  A_start_here.rev_apply
                                    (leaf_steal_right leaf_ops store_ops kvs
                                      (leaf_kvs right_kvs))
                                    (Monad.bind
                                      (fun (r1a, (k1, r2)) ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (Stacks_and_frames.unsplit_node (rks, (([r1a; r2], [k1]), (ks1, rs1))))
      (fun a -> Disk_node.Disk_node a))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))))))))
              | Delete_state.D_small_node (ks, rs) ->
                (let (rks, (_, (krs, _))) = Stacks_and_frames.dest_Frm p in
                  (match A_start_here.is_Nil (Product_Type.fst krs)
                    with true ->
                      (let _ =
                         A_start_here.check_true
                           (fun _ ->
                             (match Product_Type.snd rks with [] -> false
                               | _ :: _ -> true))
                         in
                       let (r1 :: rs1, k1 :: ks1) = rks in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (A_start_here.rev_apply r1 read)
                            (Monad.fmap Disk_node.dest_Disk_node))
                          (Monad.bind
                            (fun (l_ks, l_rs) ->
                              (match
                                Arith.equal_nata (Lista.size_list l_ks)
                                  (A_start_here.rev_apply cs
                                    Constants_and_size_types.min_node_keys)
                                with true ->
                                  A_start_here.rev_apply
                                    (node_merge_left store_ops (l_ks, l_rs) k1
                                      (ks, rs))
                                    (Monad.bind
                                      (fun r ->
A_start_here.rev_apply
  (Stacks_and_frames.unsplit_node ((rs1, ks1), (([r], []), krs))) post_mergea))
                                | false ->
                                  A_start_here.rev_apply
                                    (node_steal_left store_ops (l_rs, l_ks) k1
                                      (rs, ks))
                                    (Monad.bind
                                      (fun (r1a, (k1a, r2)) ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (Stacks_and_frames.unsplit_node ((rs1, ks1), (([r1a; r2], [k1a]), krs)))
      (fun a -> Disk_node.Disk_node a))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))))))
                    | false ->
                      (let (k1 :: ks1, r1 :: rs1) = krs in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (A_start_here.rev_apply r1 read)
                            (Monad.fmap Disk_node.dest_Disk_node))
                          (Monad.bind
                            (fun (r_ks, r_rs) ->
                              (match
                                Arith.equal_nata (Lista.size_list r_ks)
                                  (A_start_here.rev_apply cs
                                    Constants_and_size_types.min_node_keys)
                                with true ->
                                  A_start_here.rev_apply
                                    (node_merge_right store_ops (ks, rs) k1
                                      (r_ks, r_rs))
                                    (Monad.bind
                                      (fun r ->
A_start_here.rev_apply
  (Stacks_and_frames.unsplit_node (rks, (([r], []), (ks1, rs1)))) post_mergea))
                                | false ->
                                  A_start_here.rev_apply
                                    (node_steal_right store_ops (rs, ks) k1
                                      (r_rs, r_ks))
                                    (Monad.bind
                                      (fun (r1a, (k1a, r2)) ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (Stacks_and_frames.unsplit_node (rks, (([r1a; r2], [k1a]), (ks1, rs1))))
      (fun (ksa, rsa) -> Disk_node.Disk_node (ksa, rsa)))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))))))))
              | Delete_state.D_updated_subtree r ->
                (let (rks, (_, (krs, _))) = Stacks_and_frames.dest_Frm p in
                  A_start_here.rev_apply
                    (A_start_here.rev_apply
                      (A_start_here.rev_apply
                        (Stacks_and_frames.unsplit_node (rks, (([r], []), krs)))
                        (fun a -> Disk_node.Disk_node a))
                      write)
                    (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))
            (Monad.fmap (fun y -> (y, stka)))));;

let rec delete_step
  cs k_cmp leaf_ops store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
     let disk_leaf =
       (fun kvs ->
         Disk_node.Disk_leaf
           (A_start_here.rev_apply leaf_ops Disk_node.mk_leaf kvs))
       in
      (fun a ->
        (match a
          with Delete_state.D_down (f, r0) ->
            (match Find_state.dest_F_finished f
              with None ->
                A_start_here.rev_apply
                  (Find.find_step cs k_cmp leaf_ops store_ops f)
                  (Monad.fmap (fun fa -> Delete_state.D_down (fa, r0)))
              | Some (r0a, (k, (_, (leaf, stk)))) ->
                (let kvs =
                   A_start_here.rev_apply leaf_ops Disk_node.leaf_kvs leaf in
                  (match
                    Lista.list_ex (fun x -> Key_value.key_eq k_cmp x k)
                      (A_start_here.rev_apply kvs (Lista.map Product_Type.fst))
                    with true ->
                      (let kvsa =
                         A_start_here.rev_apply kvs
                           (Lista.filter
                             (fun x ->
                               not (Key_value.key_eq k_cmp (Product_Type.fst x)
                                     k)))
                         in
                        (match
                          Arith.less_nat (Lista.size_list kvsa)
                            (A_start_here.rev_apply cs
                              Constants_and_size_types.min_leaf_size)
                          with true ->
                            Monad.return
                              (Delete_state.D_up
                                (Delete_state.D_small_leaf kvsa, (stk, r0a)))
                          | false ->
                            A_start_here.rev_apply
                              (A_start_here.rev_apply (disk_leaf kvsa) write)
                              (Monad.fmap
                                (fun r ->
                                  Delete_state.D_up
                                    (Delete_state.D_updated_subtree r,
                                      (stk, r0a))))))
                    | false -> Monad.return (Delete_state.D_finished r0a))))
          | Delete_state.D_up (f, (stk, r0)) ->
            (match A_start_here.is_Nil stk
              with true ->
                (match f
                  with Delete_state.D_small_leaf kvs ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply (disk_leaf kvs) write)
                      (Monad.fmap (fun aa -> Delete_state.D_finished aa))
                  | Delete_state.D_small_node (ks, rs) ->
                    (match Arith.equal_nata (Lista.size_list ks) Arith.zero_nat
                      with true ->
                        Monad.return (Delete_state.D_finished (Lista.hd rs))
                      | false ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply (Disk_node.Disk_node (ks, rs))
                            write)
                          (Monad.fmap (fun aa -> Delete_state.D_finished aa)))
                  | Delete_state.D_updated_subtree r ->
                    Monad.return (Delete_state.D_finished r))
              | false ->
                A_start_here.rev_apply (step_up cs leaf_ops store_ops (f, stk))
                  (Monad.fmap
                    (fun (fa, stka) -> Delete_state.D_up (fa, (stka, r0)))))
          | Delete_state.D_finished _ ->
            A_start_here.failwitha "delete_step 1")));;

let rec delete_big_step
  cs k_cmp leaf_ops store_ops =
    (let delete_stepa = delete_step cs k_cmp leaf_ops store_ops in
      Post_monad.iter_m
        (fun d ->
          (match d
            with Delete_state.D_down _ ->
              A_start_here.rev_apply (delete_stepa d)
                (Monad.fmap (fun a -> Some a))
            | Delete_state.D_up _ ->
              A_start_here.rev_apply (delete_stepa d)
                (Monad.fmap (fun a -> Some a))
            | Delete_state.D_finished _ -> Monad.return None)));;

let rec delete
  cs k_cmp leaf_ops store_ops r k =
    (let check_tree_at_r =
       Post_monad.check_tree_at_r cs k_cmp leaf_ops store_ops in
     let d = Delete_state.make_initial_delete_state r k in
      A_start_here.rev_apply (delete_big_step cs k_cmp leaf_ops store_ops d)
        (Monad.bind
          (fun a ->
            (match a
              with Delete_state.D_down _ ->
                A_start_here.failwitha "delete, impossible"
              | Delete_state.D_up _ ->
                A_start_here.failwitha "delete, impossible"
              | Delete_state.D_finished ra ->
                A_start_here.rev_apply (check_tree_at_r ra)
                  (Monad.bind (fun _ -> Monad.return ra))))));;

end;; (*struct Delete*)

module Insert : sig
  val insert_step :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            ('a, 'b, 'd, 'c) Insert_state.insert_state ->
              (('a, 'b, 'd, 'c) Insert_state.insert_state, 'e) Monad.mm
  val insert :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('d, ('a, 'd, 'c, unit) Disk_node.dnode, 'e) Post_monad.store_ops ->
            'd -> 'a -> 'b -> (('d option), 'e) Monad.mm
end = struct

let rec step_bottom
  cs k_cmp leaf_ops store_ops d =
    (let (write, rewrite) =
       (A_start_here.rev_apply store_ops Post_monad.wrte,
         A_start_here.rev_apply store_ops Post_monad.rewrite)
       in
     let (fs, v) = d in
      (match Find_state.dest_F_finished fs
        with None -> A_start_here.failwitha "insert, step_bottom, 1"
        | Some (_, (k, (r, (leaf, stk)))) ->
          (let leafa =
             A_start_here.rev_apply leaf_ops Disk_node.leaf_insert k v leaf in
            (match
              Arith.less_eq_nat
                (A_start_here.rev_apply leaf_ops Disk_node.leaf_length leafa)
                (A_start_here.rev_apply cs
                  Constants_and_size_types.max_leaf_size)
              with true ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply (Disk_node.Disk_leaf leafa)
                    (rewrite r))
                  (Monad.bind
                    (fun a ->
                      (match a with None -> Monad.return (Sum_Type.Inr ())
                        | Some ra ->
                          Monad.return
                            (Sum_Type.Inl (Insert_state.I1 ra, stk)))))
              | false ->
                (let mk_leaf = A_start_here.rev_apply leaf_ops Disk_node.mk_leaf
                   in
                 let kvs =
                   A_start_here.rev_apply leaf_ops Disk_node.leaf_kvs leafa in
                 let (kvs1, (ka, kvs2)) = Insert_state.split_leaf cs kvs in
                  A_start_here.rev_apply
                    (A_start_here.rev_apply (Disk_node.Disk_leaf (mk_leaf kvs1))
                      write)
                    (Monad.bind
                      (fun r1 ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (Disk_node.Disk_leaf (mk_leaf kvs2)) write)
                          (Monad.bind
                            (fun r2 ->
                              Monad.return
                                (Sum_Type.Inl
                                  (Insert_state.I2 (r1, (ka, r2)),
                                    stk)))))))))));;

let rec step_down
  cs k_cmp leaf_ops store_ops =
    (let find_step = Find.find_step cs k_cmp leaf_ops store_ops in
      (fun (fs, v) ->
        A_start_here.rev_apply (find_step fs) (Monad.fmap (fun d -> (d, v)))));;

let rec step_up
  cs k_cmp store_ops u =
    (let (write, rewrite) =
       (A_start_here.rev_apply store_ops Post_monad.wrte,
         A_start_here.rev_apply store_ops Post_monad.rewrite)
       in
      (match u with (_, []) -> A_start_here.failwitha "insert, step_up,1"
        | (fo, frm :: stk) ->
          (let a = Stacks_and_frames.dest_Frm frm in
           let (aa, b) = a in
            (let (rs1, ks1) = aa in
              (fun (_, ab) ->
                (let (ac, ba) = ab in
                  (let (ks2, rs2) = ac in
                    (fun r_parent ->
                      (match fo
                        with Insert_state.I1 r ->
                          (let (ks, rs) =
                             Stacks_and_frames.unsplit_node
                               ((rs1, ks1), (([r], []), (ks2, rs2)))
                             in
                            A_start_here.rev_apply
                              (A_start_here.rev_apply
                                (Disk_node.Disk_node (ks, rs))
                                (rewrite r_parent))
                              (Monad.bind
                                (fun ad ->
                                  (match ad
                                    with None -> Monad.return (Sum_Type.Inr ())
                                    | Some r2 ->
                                      Monad.return
(Sum_Type.Inl (Insert_state.I1 r2, stk))))))
                        | Insert_state.I2 (r1, (k, r2)) ->
                          (let (ks, rs) =
                             Stacks_and_frames.unsplit_node
                               ((rs1, ks1), (([r1; r2], [k]), (ks2, rs2)))
                             in
                            (match
                              Arith.less_eq_nat (Lista.size_list ks)
                                (A_start_here.rev_apply cs
                                  Constants_and_size_types.max_node_keys)
                              with true ->
                                A_start_here.rev_apply
                                  (A_start_here.rev_apply
                                    (Disk_node.Disk_node (ks, rs))
                                    (rewrite r_parent))
                                  (Monad.bind
                                    (fun ad ->
                                      (match ad
with None -> Monad.return (Sum_Type.Inr ())
| Some r2a -> Monad.return (Sum_Type.Inl (Insert_state.I1 r2a, stk)))))
                              | false ->
                                (let (ks_rs1, (ka, ks_rs2)) =
                                   Insert_state.split_node cs (ks, rs) in
                                  A_start_here.rev_apply
                                    (A_start_here.rev_apply
                                      (Disk_node.Disk_node ks_rs1) write)
                                    (Monad.bind
                                      (fun r1a ->
A_start_here.rev_apply
  (A_start_here.rev_apply (Disk_node.Disk_node ks_rs2) write)
  (Monad.bind
    (fun r2a ->
      Monad.return
        (Sum_Type.Inl (Insert_state.I2 (r1a, (ka, r2a)), stk))))))))))))
                    ba)))
              b)));;

let rec insert_step
  cs k_cmp leaf_ops store_ops =
    (let step_downa = step_down cs k_cmp leaf_ops store_ops in
     let step_bottoma = step_bottom cs k_cmp leaf_ops store_ops in
     let step_upa = step_up cs k_cmp store_ops in
     let write = A_start_here.rev_apply store_ops Post_monad.wrte in
      (fun a ->
        (match a
          with Insert_state.I_down d ->
            (let (fs, _) = d in
              (match Find_state.dest_F_finished fs
                with None ->
                  A_start_here.rev_apply (step_downa d)
                    (Monad.fmap (fun aa -> Insert_state.I_down aa))
                | Some _ ->
                  A_start_here.rev_apply (step_bottoma d)
                    (Monad.bind
                      (fun aa ->
                        (match aa
                          with Sum_Type.Inl u ->
                            Monad.return (Insert_state.I_up u)
                          | Sum_Type.Inr () ->
                            Monad.return
                              Insert_state.I_finished_with_mutate)))))
          | Insert_state.I_up u ->
            (match u
              with (Insert_state.I1 r, []) ->
                Monad.return (Insert_state.I_finished r)
              | (Insert_state.I2 (r1, (k, r2)), []) ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply (Disk_node.Disk_node ([k], [r1; r2]))
                    write)
                  (Monad.bind
                    (fun r -> Monad.return (Insert_state.I_finished r)))
              | (_, _ :: _) ->
                A_start_here.rev_apply (step_upa u)
                  (Monad.bind
                    (fun aa ->
                      (match aa
                        with Sum_Type.Inl ua ->
                          Monad.return (Insert_state.I_up ua)
                        | Sum_Type.Inr () ->
                          Monad.return Insert_state.I_finished_with_mutate))))
          | Insert_state.I_finished _ -> A_start_here.failwitha "insert_step 1"
          | Insert_state.I_finished_with_mutate ->
            A_start_here.failwitha "insert_step 2")));;

let rec insert_big_step
  cs k_cmp leaf_ops store_ops =
    (let insert_stepa = insert_step cs k_cmp leaf_ops store_ops in
      Post_monad.iter_m
        (fun i ->
          (match i
            with Insert_state.I_down _ ->
              A_start_here.rev_apply (insert_stepa i)
                (Monad.fmap (fun a -> Some a))
            | Insert_state.I_up _ ->
              A_start_here.rev_apply (insert_stepa i)
                (Monad.fmap (fun a -> Some a))
            | Insert_state.I_finished _ -> Monad.return None
            | Insert_state.I_finished_with_mutate -> Monad.return None)));;

let rec insert
  cs k_cmp leaf_ops store_ops r k v =
    (let check_tree_at_r =
       Post_monad.check_tree_at_r cs k_cmp leaf_ops store_ops in
     let i = Insert_state.make_initial_insert_state r k v in
      A_start_here.rev_apply (insert_big_step cs k_cmp leaf_ops store_ops i)
        (Monad.bind
          (fun a ->
            (match a
              with Insert_state.I_down _ -> A_start_here.failwitha "insert 1"
              | Insert_state.I_up _ -> A_start_here.failwitha "insert 1"
              | Insert_state.I_finished ra ->
                A_start_here.rev_apply (check_tree_at_r ra)
                  (Monad.bind (fun _ -> Monad.return (Some ra)))
              | Insert_state.I_finished_with_mutate ->
                A_start_here.rev_apply (check_tree_at_r r)
                  (Monad.bind (fun _ -> Monad.return None))))));;

end;; (*struct Insert*)


end (* Make *)