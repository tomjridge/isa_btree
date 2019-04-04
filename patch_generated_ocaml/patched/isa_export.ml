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
  val apfst : ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

let rec equal_proda _A _B
  (x1, x2) (y1, y2) = HOL.eq _A x1 y1 && HOL.eq _B x2 y2;;

let rec equal_prod _A _B =
  ({HOL.equal = equal_proda _A _B} : ('a * 'b) HOL.equal);;

let rec apfst f (x, y) = (f x, y);;

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

end;; (*struct Product_Type*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

let rec max _A a b = (if less_eq _A a b then b else a);;

end;; (*struct Orderings*)

module Arith : sig
  type nat = Nat of Big_int.big_int
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
  val divmod_nat : nat -> nat -> nat * nat
  val less_int : int -> int -> bool
  val int_of_nat : nat -> int
  val zero_int : int
  val zero_nat : nat
  val nat_of_integer : Big_int.big_int -> nat
  val equal_int : int -> int -> bool
  val minus_int : int -> int -> int
  val less_eq_int : int -> int -> bool
  val minus_nat : nat -> nat -> nat
  val times_nat : nat -> nat -> nat
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

let rec modulo_integer k l = Product_Type.snd (divmod_integer k l);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_integer k l = Product_Type.fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec divmod_nat m n = (divide_nat m n, modulo_nat m n);;

let rec integer_of_int (Int_of_integer k) = k;;

let rec less_int
  k l = Big_int.lt_big_int (integer_of_int k) (integer_of_int l);;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let zero_int : int = Int_of_integer Big_int.zero_big_int;;

let zero_nat : nat = Nat Big_int.zero_big_int;;

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

let rec times_nat
  m n = Nat (Big_int.mult_big_int (integer_of_nat m) (integer_of_nat n));;

end;; (*struct Arith*)

module Lista : sig
  val nth : 'a list -> Arith.nat -> 'a
  val rev : 'a list -> 'a list
  val upt : Arith.nat -> Arith.nat -> Arith.nat list
  val null : 'a list -> bool
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val hd : 'a list -> 'a
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

let rec hd (x21 :: x22) = x21;;

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

module RBT_Impl : sig
  type color
  type ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val entries : ('a, 'b) rbt -> ('a * 'b) list
  val rbtreeify : ('a * 'b) list -> ('a, 'b) rbt
  val rbt_union :
    'a Orderings.ord -> ('a, 'b) rbt -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_delete : 'a Orderings.ord -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insert : 'a Orderings.ord -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_lookup : 'a Orderings.ord -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

type compare = LT | GT | EQ;;

let rec fold
  f xa1 x = match f, xa1, x with
    f, Branch (c, lt, k, v, rt), x -> fold f rt (f k v (fold f lt x))
    | f, Empty, x -> x;;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec gen_entries
  kvts x1 = match kvts, x1 with
    kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | [], Empty -> [];;

let rec entries x = gen_entries [] x;;

let rec skip_red = function Branch (R, l, k, v, r) -> l
                   | Empty -> Empty
                   | Branch (B, va, vb, vc, vd) -> Branch (B, va, vb, vc, vd);;

let rec rbtreeify_g
  n kvs =
    (if Arith.equal_nata n Arith.zero_nat || Arith.equal_nata n Arith.one_nat
      then (Empty, kvs)
      else (let (na, r) =
              Arith.divmod_nat n
                (Arith.nat_of_integer (Big_int.big_int_of_int 2))
              in
             (if Arith.equal_nata r Arith.zero_nat
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      Product_Type.apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      Product_Type.apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if Arith.equal_nata n Arith.zero_nat then (Empty, kvs)
      else (if Arith.equal_nata n Arith.one_nat
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) =
                     Arith.divmod_nat n
                       (Arith.nat_of_integer (Big_int.big_int_of_int 2))
                     in
                    (if Arith.equal_nata r Arith.zero_nat
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             Product_Type.apfst
                               (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             Product_Type.apfst
                               (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify
  kvs = Product_Type.fst (rbtreeify_g (Arith.suc (Lista.size_list kvs)) kvs);;

let rec skip_black
  t = (let ta = skip_red t in
        (match ta with Empty -> ta | Branch (R, _, _, _, _) -> ta
          | Branch (B, l, _, _, _) -> l));;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec compare_height
  sx s t tx =
    (match (skip_red sx, (skip_red s, (skip_red t, skip_red tx)))
      with (Empty, (Empty, (_, Empty))) -> EQ
      | (Empty, (Empty, (_, Branch (_, _, _, _, _)))) -> LT
      | (Empty, (Branch (_, _, _, _, _), (Empty, _))) -> EQ
      | (Empty, (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), Empty))) -> EQ
      | (Empty,
          (Branch (_, sa, _, _, _),
            (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
        -> compare_height Empty sa ta (skip_black txa)
      | (Branch (_, _, _, _, _), (Empty, (Empty, Empty))) -> GT
      | (Branch (_, _, _, _, _), (Empty, (Empty, Branch (_, _, _, _, _)))) -> LT
      | (Branch (_, _, _, _, _), (Empty, (Branch (_, _, _, _, _), Empty))) -> EQ
      | (Branch (_, _, _, _, _),
          (Empty, (Branch (_, _, _, _, _), Branch (_, _, _, _, _))))
        -> LT
      | (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), (Empty, _))) -> GT
      | (Branch (_, sxa, _, _, _),
          (Branch (_, sa, _, _, _), (Branch (_, ta, _, _, _), Empty)))
        -> compare_height (skip_black sxa) sa ta Empty
      | (Branch (_, sxa, _, _, _),
          (Branch (_, sa, _, _, _),
            (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
        -> compare_height (skip_black sxa) sa ta (skip_black txa));;

let rec rbt_del _A
  x xa1 = match x, xa1 with x, Empty -> Empty
    | x, Branch (c, a, y, s, b) ->
        (if Orderings.less _A x y then rbt_del_from_left _A x a y s b
          else (if Orderings.less _A y x then rbt_del_from_right _A x a y s b
                 else combine a b))
and rbt_del_from_left _A
  x xa1 y s b = match x, xa1, y, s, b with
    x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_del _A x (Branch (B, lt, z, v, rt))) y s b
    | x, Empty, y, s, b -> Branch (R, rbt_del _A x Empty, y, s, b)
    | x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_del _A x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_del_from_right _A
  x a y s xa4 = match x, a, y, s, xa4 with
    x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_del _A x (Branch (B, lt, z, v, rt)))
    | x, a, y, s, Empty -> Branch (R, a, y, s, rbt_del _A x Empty)
    | x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_del _A x (Branch (R, va, vb, vc, vd)));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if Orderings.less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if Orderings.less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if Orderings.less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if Orderings.less _A x k
                 then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec sunion_with _A
  f asa bs = match f, asa, bs with
    f, (ka, va) :: asa, (k, v) :: bs ->
      (if Orderings.less _A k ka
        then (k, v) :: sunion_with _A f ((ka, va) :: asa) bs
        else (if Orderings.less _A ka k
               then (ka, va) :: sunion_with _A f asa ((k, v) :: bs)
               else (ka, f ka va v) :: sunion_with _A f asa bs))
    | f, [], bs -> bs
    | f, asa, [] -> asa;;

let rec rbt_union_with_key _A
  f t1 t2 =
    (match compare_height t1 t1 t2 t2
      with LT -> fold (rbt_insert_with_key _A (fun k v w -> f k w v)) t1 t2
      | GT -> fold (rbt_insert_with_key _A f) t2 t1
      | EQ -> rbtreeify (sunion_with _A f (entries t1) (entries t2)));;

let rec rbt_union _A = rbt_union_with_key _A (fun _ _ rv -> rv);;

let rec rbt_delete _A k t = paint B (rbt_del _A k t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if Orderings.less _A k x then rbt_lookup _A l k
          else (if Orderings.less _A x k then rbt_lookup _A r k else Some y));;

end;; (*struct RBT_Impl*)

module Option : sig
  val is_none : 'a option -> bool
end = struct

let rec is_none = function Some x -> false
                  | None -> true;;

end;; (*struct Option*)

module A_start_here : sig
  type error = String_error of string
  val from_to : Arith.nat -> Arith.nat -> Arith.nat list
  val is_Nil : 'a list -> bool
  val is_None : 'a option -> bool
  val rbt_max : ('a, 'b) RBT_Impl.rbt -> ('a * 'b) option
  val rbt_min : ('a, 'b) RBT_Impl.rbt -> ('a * 'b) option
  val rev_apply : 'a -> ('a -> 'b) -> 'b
  val failwitha : string -> 'a
  val dest_Some : 'a option -> 'a
  val iter_step : ('a -> 'a option) -> 'a -> 'a
  val check_true : (unit -> bool) -> bool
  val assert_true : bool -> bool
  val impossible1 : string -> 'a
  val max_of_list : Arith.nat list -> Arith.nat
  val from_to_tests : bool
end = struct

type error = String_error of string;;

let rec from_to x y = Lista.upt x (Arith.suc y);;

let rec is_Nil x = (match x with [] -> true | _ :: _ -> false);;

let rec is_None x = Option.is_none x;;

let rec rbt_maxa
  x sofar =
    (match x with RBT_Impl.Empty -> sofar
      | RBT_Impl.Branch (_, _, k, v, r) -> rbt_maxa r (Some (k, v)));;

let rec rbt_max x = rbt_maxa x None;;

let rec rbt_mina
  x sofar =
    (match x with RBT_Impl.Empty -> sofar
      | RBT_Impl.Branch (_, l, k, v, _) -> rbt_mina l (Some (k, v)));;

let rec rbt_min x = rbt_mina x None;;

let rec rev_apply x f = f x;;

let rec failwitha x = failwith x

let rec dest_Some = function Some x -> x
                    | None -> failwith "undefined";;

let rec iter_step
  f x = (let a = f x in (match a with None -> x | Some aa -> iter_step f aa));;

let rec check_true f = let r = f() in assert r; r

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

end;; (*struct A_start_here*)

module Stacks_and_frames : sig
  type ('a, 'b, 'c, 'd) frame_ops =
    Make_frame_ops of
      ('b -> 'a -> 'd -> 'c) * ('c -> 'b) *
        ('c -> 'a option * ('b * 'a option)) *
        ('c -> ('a option * ('b * ('a * ('b * 'a option)))) option) *
        ('c -> ('a option * ('b * ('a * ('b * 'a option)))) option) *
        ('a option * ('b * (('a * 'b) list * 'a option)) ->
          'a option * ('b * (('a * 'b) list * 'a option)) -> 'c -> 'c) *
        ('c -> 'd) * ('c -> 'a option * 'a option) * ('c -> 'b) * ('d -> 'c) *
        ('c -> 'c option)
  val get_bounds :
    ('a, 'b, 'c, 'd) frame_ops -> 'c list -> 'a option * 'a option
  val replace :
    ('a, 'b, 'c, 'd) frame_ops ->
      'a option * ('b * (('a * 'b) list * 'a option)) ->
        'a option * ('b * (('a * 'b) list * 'a option)) -> 'c -> 'c
  val midpoint : ('a, 'b, 'c, 'd) frame_ops -> 'c -> 'b
  val get_focus :
    ('a, 'b, 'c, 'd) frame_ops -> 'c -> 'a option * ('b * 'a option)
  val frame_to_node : ('a, 'b, 'c, 'd) frame_ops -> 'c -> 'd
  val split_node_on_key : ('a, 'b, 'c, 'd) frame_ops -> 'b -> 'a -> 'd -> 'c
  val step_frame_for_ls : ('a, 'b, 'c, 'd) frame_ops -> 'c -> 'c option
  val backing_node_blk_ref : ('a, 'b, 'c, 'd) frame_ops -> 'c -> 'b
  val split_node_on_first_key : ('a, 'b, 'c, 'd) frame_ops -> 'd -> 'c
  val get_left_sibling_and_focus :
    ('a, 'b, 'c, 'd) frame_ops ->
      'c -> ('a option * ('b * ('a * ('b * 'a option)))) option
  val get_focus_and_right_sibling :
    ('a, 'b, 'c, 'd) frame_ops ->
      'c -> ('a option * ('b * ('a * ('b * 'a option)))) option
end = struct

type ('a, 'b, 'c, 'd) frame_ops =
  Make_frame_ops of
    ('b -> 'a -> 'd -> 'c) * ('c -> 'b) * ('c -> 'a option * ('b * 'a option)) *
      ('c -> ('a option * ('b * ('a * ('b * 'a option)))) option) *
      ('c -> ('a option * ('b * ('a * ('b * 'a option)))) option) *
      ('a option * ('b * (('a * 'b) list * 'a option)) ->
        'a option * ('b * (('a * 'b) list * 'a option)) -> 'c -> 'c) *
      ('c -> 'd) * ('c -> 'a option * 'a option) * ('c -> 'b) * ('d -> 'c) *
      ('c -> 'c option);;

let rec get_midpoint_bounds
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x8;;

let rec get_bounds
  frame_ops stk =
    A_start_here.rev_apply
      (A_start_here.iter_step
        (fun a ->
          (match a with (_, (_, [])) -> None
            | (l, (u, frm :: stka)) ->
              (match (l, u)
                with (None, _) ->
                  (let (la, ua) =
                     A_start_here.rev_apply frame_ops get_midpoint_bounds frm in
                   let lb = (match l with None -> la | Some _ -> l) in
                   let ub = (match u with None -> ua | Some _ -> u) in
                    Some (lb, (ub, stka)))
                | (Some _, None) ->
                  (let (la, ua) =
                     A_start_here.rev_apply frame_ops get_midpoint_bounds frm in
                   let lb = (match l with None -> la | Some _ -> l) in
                   let ub = (match u with None -> ua | Some _ -> u) in
                    Some (lb, (ub, stka)))
                | (Some _, Some _) -> None)))
        (None, (None, stk)))
      (fun (l, (u, _)) -> (l, u));;

let rec replace
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x6;;

let rec midpoint
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x2;;

let rec get_focus
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x3;;

let rec frame_to_node
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x7;;

let rec split_node_on_key
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x1;;

let rec step_frame_for_ls
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x11;;

let rec backing_node_blk_ref
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x9;;

let rec split_node_on_first_key
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x10;;

let rec get_left_sibling_and_focus
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x5;;

let rec get_focus_and_right_sibling
  (Make_frame_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11)) = x4;;

end;; (*struct Stacks_and_frames*)

module Find_state : sig
  type ('a, 'b, 'c, 'd) find_state = F_down of ('b * ('a * ('b * 'd list))) |
    F_finished of ('b * ('a * ('b * ('c * 'd list))))
  val dest_F_finished :
    ('a, 'b, 'c, 'd) find_state -> ('b * ('a * ('b * ('c * 'd list)))) option
  val make_initial_find_state : 'a -> 'b -> ('a, 'b, 'c, 'd) find_state
end = struct

type ('a, 'b, 'c, 'd) find_state = F_down of ('b * ('a * ('b * 'd list))) |
  F_finished of ('b * ('a * ('b * ('c * 'd list))));;

let rec dest_F_finished
  fs = (match fs with F_down _ -> None
         | F_finished (r0, (k, (r, (kvs, stk)))) ->
           Some (r0, (k, (r, (kvs, stk)))));;

let rec make_initial_find_state k r = F_down (r, (k, (r, [])));;

end;; (*struct Find_state*)

module Insert_state : sig
  type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c))
  type ('a, 'b, 'c, 'd, 'e) insert_state =
    I_down of (('a, 'c, 'd, 'e) Find_state.find_state * 'b) |
    I_up of (('a, 'b, 'c) i12_t * 'e list) | I_finished of 'c |
    I_finished_with_mutate
  val make_initial_insert_state :
    'a -> 'b -> 'c -> ('b, 'c, 'a, 'd, 'e) insert_state
end = struct

type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c));;

type ('a, 'b, 'c, 'd, 'e) insert_state =
  I_down of (('a, 'c, 'd, 'e) Find_state.find_state * 'b) |
  I_up of (('a, 'b, 'c) i12_t * 'e list) | I_finished of 'c |
  I_finished_with_mutate;;

let rec make_initial_insert_state
  r k v = (let f = Find_state.make_initial_find_state k r in I_down (f, v));;

end;; (*struct Insert_state*)

module Delete_state : sig
  type ('a, 'b, 'c) del_t = D_small_leaf of 'c | D_small_node of 'b |
    D_updated_subtree of 'a
  type ('a, 'b, 'c, 'd, 'e, 'f) delete_state =
    D_down of (('a, 'c, 'd, 'f) Find_state.find_state * 'c) |
    D_up of (('c, 'e, 'd) del_t * ('f list * 'c)) | D_finished of 'c
  val dest_D_finished : ('a, 'b, 'c, 'd, 'e, 'f) delete_state -> 'c option
  val make_initial_delete_state :
    'a -> 'b -> ('b, 'c, 'a, 'd, 'e, 'f) delete_state
end = struct

type ('a, 'b, 'c) del_t = D_small_leaf of 'c | D_small_node of 'b |
  D_updated_subtree of 'a;;

type ('a, 'b, 'c, 'd, 'e, 'f) delete_state =
  D_down of (('a, 'c, 'd, 'f) Find_state.find_state * 'c) |
  D_up of (('c, 'e, 'd) del_t * ('f list * 'c)) | D_finished of 'c;;

let rec dest_D_finished
  x = (match x with D_down _ -> None | D_up _ -> None
        | D_finished a -> Some a);;

let rec make_initial_delete_state
  r k = D_down (Find_state.make_initial_find_state k r, r);;

end;; (*struct Delete_state*)

module Disk_node : sig
  type ('a, 'b) dnode = Disk_node of 'a | Disk_leaf of 'b
  type ('a, 'b, 'c) leaf_ops =
    Make_leaf_ops of
      ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c * 'b option) *
        ('a -> 'c -> 'c) * ('c -> Arith.nat) * ('c -> ('a * 'b) list) *
        ('c * 'c -> 'c * ('a * 'c)) * ('c * 'c -> 'c * ('a * 'c)) *
        ('c * 'c -> 'c) * (Arith.nat -> 'c -> 'c * ('a * 'c))
  type ('a, 'b, 'c) node_ops =
    Make_node_ops of
      (Arith.nat -> 'c -> 'c * ('a * 'c)) * ('c * ('a * 'c) -> 'c) *
        ('c * ('a * 'c) -> 'c * ('a * 'c)) *
        ('c * ('a * 'c) -> 'c * ('a * 'c)) * ('c -> Arith.nat) *
        ('b * ('a * 'b) -> 'c) * ('c -> 'b)
  val dest_Disk_leaf : ('a, 'b) dnode -> 'b
  val dest_Disk_node : ('a, 'b) dnode -> 'a
  val rbt_as_leaf_ops :
    'a Orderings.linorder -> ('a, 'b, ('a, 'b) RBT_Impl.rbt) leaf_ops
  val leaf_merge : ('a, 'b, 'c) leaf_ops -> 'c * 'c -> 'c
  val node_merge : ('a, 'b, 'c) node_ops -> 'c * ('a * 'c) -> 'c
  val leaf_insert : ('a, 'b, 'c) leaf_ops -> 'a -> 'b -> 'c -> 'c * 'b option
  val leaf_length : ('a, 'b, 'c) leaf_ops -> 'c -> Arith.nat
  val leaf_lookup : ('a, 'b, 'c) leaf_ops -> 'a -> 'c -> 'b option
  val leaf_remove : ('a, 'b, 'c) leaf_ops -> 'a -> 'c -> 'c
  val leaf_steal_left : ('a, 'b, 'c) leaf_ops -> 'c * 'c -> 'c * ('a * 'c)
  val node_steal_left :
    ('a, 'b, 'c) node_ops -> 'c * ('a * 'c) -> 'c * ('a * 'c)
  val leaf_steal_right : ('a, 'b, 'c) leaf_ops -> 'c * 'c -> 'c * ('a * 'c)
  val split_large_leaf :
    ('a, 'b, 'c) leaf_ops -> Arith.nat -> 'c -> 'c * ('a * 'c)
  val node_keys_length : ('a, 'b, 'c) node_ops -> 'c -> Arith.nat
  val node_steal_right :
    ('a, 'b, 'c) node_ops -> 'c * ('a * 'c) -> 'c * ('a * 'c)
  val node_get_single_r : ('a, 'b, 'c) node_ops -> 'c -> 'b
  val node_make_small_root : ('a, 'b, 'c) node_ops -> 'b * ('a * 'b) -> 'c
  val split_node_at_k_index :
    ('a, 'b, 'c) node_ops -> Arith.nat -> 'c -> 'c * ('a * 'c)
end = struct

type ('a, 'b) dnode = Disk_node of 'a | Disk_leaf of 'b;;

type ('a, 'b, 'c) leaf_ops =
  Make_leaf_ops of
    ('a -> 'c -> 'b option) * ('a -> 'b -> 'c -> 'c * 'b option) *
      ('a -> 'c -> 'c) * ('c -> Arith.nat) * ('c -> ('a * 'b) list) *
      ('c * 'c -> 'c * ('a * 'c)) * ('c * 'c -> 'c * ('a * 'c)) *
      ('c * 'c -> 'c) * (Arith.nat -> 'c -> 'c * ('a * 'c));;

type ('a, 'b, 'c) node_ops =
  Make_node_ops of
    (Arith.nat -> 'c -> 'c * ('a * 'c)) * ('c * ('a * 'c) -> 'c) *
      ('c * ('a * 'c) -> 'c * ('a * 'c)) * ('c * ('a * 'c) -> 'c * ('a * 'c)) *
      ('c -> Arith.nat) * ('b * ('a * 'b) -> 'c) * ('c -> 'b);;

let rec split_list
  n kvs =
    A_start_here.rev_apply
      (A_start_here.iter_step
        (fun (m, (kvs1, kvs2)) ->
          (match Arith.less_nat n m with true -> None
            | false ->
              (match kvs2 with [] -> None
                | (k, v) :: kvs2a ->
                  Some (Arith.plus_nat m Arith.one_nat,
                         ((k, v) :: kvs1, kvs2a)))))
        (Arith.zero_nat, ([], kvs)))
      (fun (_, a) -> (let (xs, aa) = a in (Lista.rev xs, aa)));;

let rec dest_Disk_leaf
  f = (match f with Disk_node _ -> A_start_here.failwitha "dest_Disk_leaf"
        | Disk_leaf x -> x);;

let rec dest_Disk_node
  f = (match f with Disk_node x -> x
        | Disk_leaf _ -> A_start_here.failwitha "dest_Disk_node");;

let rec rbt_as_leaf_ops _A
  = Make_leaf_ops
      ((fun k l ->
         RBT_Impl.rbt_lookup
           _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
           l k),
        (fun k v l ->
          (let a =
             RBT_Impl.rbt_lookup
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               l k
             in
            (RBT_Impl.rbt_insert
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               k v l,
              a))),
        RBT_Impl.rbt_delete
          _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder,
        (fun l -> Lista.size_list (RBT_Impl.entries l)), RBT_Impl.entries,
        (fun (l1, l2) ->
          (let (k, v) =
             A_start_here.rev_apply (A_start_here.rbt_min l2)
               A_start_here.dest_Some
             in
           let l2a =
             RBT_Impl.rbt_delete
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               k l2
             in
           let (ka, _) =
             A_start_here.rev_apply (A_start_here.rbt_min l2a)
               A_start_here.dest_Some
             in
           let l1a =
             RBT_Impl.rbt_insert
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               k v l1
             in
            (l1a, (ka, l2a)))),
        (fun (l1, l2) ->
          (let (k, v) =
             A_start_here.rev_apply (A_start_here.rbt_max l1)
               A_start_here.dest_Some
             in
           let l1a =
             RBT_Impl.rbt_delete
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               k l1
             in
           let l2a =
             RBT_Impl.rbt_insert
               _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
               k v l2
             in
            (l1a, (k, l2a)))),
        (fun (a, b) ->
          RBT_Impl.rbt_union
            _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
            a b),
        (fun n l ->
          (let kvs = RBT_Impl.entries l in
           let (l1, l2) = split_list n kvs in
           let (k, _) = Lista.hd l2 in
            (RBT_Impl.rbtreeify l1, (k, RBT_Impl.rbtreeify l2)))));;

let rec leaf_merge (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x8;;

let rec node_merge (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x2;;

let rec leaf_insert (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x2;;

let rec leaf_length (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x4;;

let rec leaf_lookup (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x1;;

let rec leaf_remove (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x3;;

let rec leaf_steal_left
  (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x7;;

let rec node_steal_left (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x4;;

let rec leaf_steal_right
  (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x6;;

let rec split_large_leaf
  (Make_leaf_ops (x1, x2, x3, x4, x5, x6, x7, x8, x9)) = x9;;

let rec node_keys_length (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x5;;

let rec node_steal_right (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x3;;

let rec node_get_single_r (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x7;;

let rec node_make_small_root (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x6;;

let rec split_node_at_k_index
  (Make_node_ops (x1, x2, x3, x4, x5, x6, x7)) = x1;;

end;; (*struct Disk_node*)

module Sum_Type : sig
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

end;; (*struct Sum_Type*)

module Constants_and_size_types : sig
  type constants =
    Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat
  type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf
  val make_constants :
    Arith.nat -> Arith.nat -> Arith.nat -> Arith.nat -> constants
  val max_leaf_size : constants -> Arith.nat
  val max_node_keys : constants -> Arith.nat
  val min_leaf_size : constants -> Arith.nat
  val min_node_keys : constants -> Arith.nat
end = struct

type constants =
  Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat;;

type min_size_t = Small_root_node_or_leaf | Small_node | Small_leaf;;

let rec make_constants a b c d = Make_constants (a, b, c, d);;

let rec max_leaf_size (Make_constants (x1, x2, x3, x4)) = x2;;

let rec max_node_keys (Make_constants (x1, x2, x3, x4)) = x4;;

let rec min_leaf_size (Make_constants (x1, x2, x3, x4)) = x1;;

let rec min_node_keys (Make_constants (x1, x2, x3, x4)) = x3;;

end;; (*struct Constants_and_size_types*)

module Key_value : sig
  type compare_t = LT | EQ | GT
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

type compare_t = LT | EQ | GT;;

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

module Tree : sig
  type ('a, 'b) tree
  val wf_tree :
    Constants_and_size_types.constants ->
      Constants_and_size_types.min_size_t option ->
        ('a -> 'a -> Arith.int) -> ('a, 'b) tree -> bool
  val dest_Node : ('a, 'b) tree -> 'a list * ('a, 'b) tree list
  val tree_to_leaves : ('a, 'b) tree -> (('a * 'b) list) list
end = struct

type ('a, 'b) tree = Node of ('a list * ('a, 'b) tree list) |
  Leaf of ('a * 'b) list;;

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
  val make_store_ops :
    ('a -> ('b, 'c) Monad.mm) ->
      ('b -> ('a, 'c) Monad.mm) ->
        ('a -> 'b -> (('a option), 'c) Monad.mm) ->
          ('a list -> (unit, 'c) Monad.mm) -> ('a, 'b, 'c) store_ops
  val free : ('a, 'b, 'c) store_ops -> 'a list -> (unit, 'c) Monad.mm
  val read : ('a, 'b, 'c) store_ops -> 'a -> ('b, 'c) Monad.mm
  val wrte : ('a, 'b, 'c) store_ops -> 'b -> ('a, 'c) Monad.mm
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

let rec make_store_ops r w rw f = Make_store_ops (r, w, rw, f);;

let rec free (Make_store_ops (x1, x2, x3, x4)) = x4;;

let rec read (Make_store_ops (x1, x2, x3, x4)) = x1;;

let rec wrte (Make_store_ops (x1, x2, x3, x4)) = x2;;

let rec rewrite (Make_store_ops (x1, x2, x3, x4)) = x3;;

end;; (*struct Post_monad*)

module Find : sig
  val find_step :
    ('a, 'b, 'c, 'd) Stacks_and_frames.frame_ops ->
      ('b, ('d, 'e) Disk_node.dnode, 'f) Post_monad.store_ops ->
        ('a, 'b, 'e, 'c) Find_state.find_state ->
          (('a, 'b, 'e, 'c) Find_state.find_state, 'f) Monad.mm
  val find :
    ('a, 'b, 'c, 'd) Stacks_and_frames.frame_ops ->
      ('b, ('d, 'e) Disk_node.dnode, 'f) Post_monad.store_ops ->
        'b -> 'a -> (('b * ('e * 'c list)), 'f) Monad.mm
end = struct

let rec find_step
  frame_ops store_ops =
    (let read = A_start_here.rev_apply store_ops Post_monad.read in
      (fun a ->
        (match a
          with Find_state.F_down (r0, (k, (r, stk))) ->
            A_start_here.rev_apply (read r)
              (Monad.fmap
                (fun aa ->
                  (match aa
                    with Disk_node.Disk_node n ->
                      (let frm =
                         A_start_here.rev_apply frame_ops
                           Stacks_and_frames.split_node_on_key r k n
                         in
                       let ra =
                         A_start_here.rev_apply frame_ops
                           Stacks_and_frames.midpoint frm
                         in
                        Find_state.F_down (r0, (k, (ra, frm :: stk))))
                    | Disk_node.Disk_leaf leaf ->
                      Find_state.F_finished (r0, (k, (r, (leaf, stk)))))))
          | Find_state.F_finished _ -> A_start_here.failwitha "find_step 1")));;

let rec find_big_step
  frame_ops store_ops =
    (let step = find_step frame_ops store_ops in
      Post_monad.iter_m
        (fun i ->
          (match i
            with Find_state.F_down _ ->
              A_start_here.rev_apply (step i) (Monad.fmap (fun a -> Some a))
            | Find_state.F_finished _ -> Monad.return None)));;

let rec find
  frame_ops store_ops r k =
    (let s = Find_state.make_initial_find_state k r in
      A_start_here.rev_apply (find_big_step frame_ops store_ops s)
        (Monad.bind
          (fun a ->
            (match a with Find_state.F_down _ -> A_start_here.failwitha "find 1"
              | Find_state.F_finished (_, (_, (ra, (kvs, stk)))) ->
                Monad.return (ra, (kvs, stk))))));;

end;; (*struct Find*)

module Delete : sig
  val delete_step :
    Constants_and_size_types.constants ->
      ('a, 'b, 'c) Disk_node.leaf_ops ->
        ('a, 'd, 'e) Disk_node.node_ops ->
          ('a, 'd, 'f, 'e) Stacks_and_frames.frame_ops ->
            ('d, ('e, 'c) Disk_node.dnode, 'g) Post_monad.store_ops ->
              ('a, 'b, 'd, 'c, 'e, 'f) Delete_state.delete_state ->
                (('a, 'b, 'd, 'c, 'e, 'f) Delete_state.delete_state, 'g)
                  Monad.mm
  val delete :
    Constants_and_size_types.constants ->
      ('a, 'b, 'c) Disk_node.leaf_ops ->
        ('a, 'd, 'e) Disk_node.node_ops ->
          ('a, 'd, 'f, 'e) Stacks_and_frames.frame_ops ->
            ('d, ('e, 'c) Disk_node.dnode, 'g) Post_monad.store_ops ->
              ('d -> (bool, 'g) Monad.mm) -> 'd -> 'a -> ('d, 'g) Monad.mm
end = struct

let rec post_merge
  cs node_ops store_ops n =
    (match
      Arith.less_nat
        (A_start_here.rev_apply node_ops Disk_node.node_keys_length n)
        (A_start_here.rev_apply cs Constants_and_size_types.min_node_keys)
      with true -> Monad.return (Delete_state.D_small_node n)
      | false ->
        A_start_here.rev_apply
          (A_start_here.rev_apply (Disk_node.Disk_node n)
            (A_start_here.rev_apply store_ops Post_monad.wrte))
          (Monad.bind
            (fun r -> Monad.return (Delete_state.D_updated_subtree r))));;

let rec step_up_small_node
  cs leaf_ops node_ops frame_ops store_ops frm n =
    (let (read, write) =
       (A_start_here.rev_apply store_ops Post_monad.read,
         A_start_here.rev_apply store_ops Post_monad.wrte)
       in
     let post_mergea = post_merge cs node_ops store_ops in
      (match
        A_start_here.rev_apply frame_ops
          Stacks_and_frames.get_focus_and_right_sibling frm
        with None ->
          (match
            A_start_here.rev_apply frame_ops
              Stacks_and_frames.get_left_sibling_and_focus frm
            with None -> A_start_here.failwitha "impossible"
            | Some (k1, (r1, (k2, (r2, k3)))) ->
              A_start_here.rev_apply
                (A_start_here.rev_apply (A_start_here.rev_apply r1 read)
                  (Monad.fmap Disk_node.dest_Disk_node))
                (Monad.bind
                  (fun left_sibling ->
                    (match
                      Arith.equal_nata
                        (A_start_here.rev_apply node_ops
                          Disk_node.node_keys_length left_sibling)
                        (A_start_here.rev_apply cs
                          Constants_and_size_types.min_node_keys)
                      with true ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply node_ops Disk_node.node_merge
                            (left_sibling, (k2, n)))
                          (fun na ->
                            A_start_here.rev_apply
                              (write (Disk_node.Disk_node na))
                              (Monad.bind
                                (fun r ->
                                  A_start_here.rev_apply
                                    (A_start_here.rev_apply
                                      (A_start_here.rev_apply frm
(A_start_here.rev_apply frame_ops Stacks_and_frames.replace
  (k1, (r1, ([(k2, r2)], k3))) (k1, (r, ([], k3)))))
                                      (A_start_here.rev_apply frame_ops
Stacks_and_frames.frame_to_node))
                                    post_mergea)))
                      | false ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply node_ops
                            Disk_node.node_steal_left (left_sibling, (k2, n)))
                          (fun (left_siblinga, (k2a, na)) ->
                            A_start_here.rev_apply
                              (write (Disk_node.Disk_node left_siblinga))
                              (Monad.bind
                                (fun r1a ->
                                  A_start_here.rev_apply
                                    (write (Disk_node.Disk_node na))
                                    (Monad.bind
                                      (fun r2a ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (A_start_here.rev_apply
        (A_start_here.rev_apply frm
          (A_start_here.rev_apply frame_ops Stacks_and_frames.replace
            (k1, (r1, ([(k2, r2)], k3))) (k1, (r1a, ([(k2a, r2a)], k3)))))
        (A_start_here.rev_apply frame_ops Stacks_and_frames.frame_to_node))
      (fun a -> Disk_node.Disk_node a))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a)))))))))))
        | Some (k1, (r1, (k2, (r2, k3)))) ->
          A_start_here.rev_apply
            (A_start_here.rev_apply (A_start_here.rev_apply r2 read)
              (Monad.fmap Disk_node.dest_Disk_node))
            (Monad.bind
              (fun right_sibling ->
                (match
                  Arith.equal_nata
                    (A_start_here.rev_apply node_ops Disk_node.node_keys_length
                      right_sibling)
                    (A_start_here.rev_apply cs
                      Constants_and_size_types.min_node_keys)
                  with true ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply node_ops Disk_node.node_merge
                        (n, (k2, right_sibling)))
                      (fun na ->
                        A_start_here.rev_apply (write (Disk_node.Disk_node na))
                          (Monad.bind
                            (fun r ->
                              A_start_here.rev_apply
                                (A_start_here.rev_apply
                                  (A_start_here.rev_apply frm
                                    (A_start_here.rev_apply frame_ops
                                      Stacks_and_frames.replace
                                      (k1, (r1, ([(k2, r2)], k3)))
                                      (k1, (r, ([], k3)))))
                                  (A_start_here.rev_apply frame_ops
                                    Stacks_and_frames.frame_to_node))
                                post_mergea)))
                  | false ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply node_ops
                        Disk_node.node_steal_right (n, (k2, right_sibling)))
                      (fun (na, (k2a, right_siblinga)) ->
                        A_start_here.rev_apply (write (Disk_node.Disk_node na))
                          (Monad.bind
                            (fun r1a ->
                              A_start_here.rev_apply
                                (write (Disk_node.Disk_node right_siblinga))
                                (Monad.bind
                                  (fun r2a ->
                                    A_start_here.rev_apply
                                      (A_start_here.rev_apply
(A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply frm
      (A_start_here.rev_apply frame_ops Stacks_and_frames.replace
        (k1, (r1, ([(k2, r2)], k3))) (k1, (r1a, ([(k2a, r2a)], k3)))))
    (A_start_here.rev_apply frame_ops Stacks_and_frames.frame_to_node))
  (fun a -> Disk_node.Disk_node a))
write)
                                      (Monad.fmap
(fun a -> Delete_state.D_updated_subtree a))))))))))));;

let rec step_up_small_leaf
  cs leaf_ops node_ops frame_ops store_ops frm leaf =
    (let (read, write) =
       (A_start_here.rev_apply store_ops Post_monad.read,
         A_start_here.rev_apply store_ops Post_monad.wrte)
       in
     let post_mergea = post_merge cs node_ops store_ops in
      (match
        A_start_here.rev_apply frame_ops
          Stacks_and_frames.get_focus_and_right_sibling frm
        with None ->
          (match
            A_start_here.rev_apply frame_ops
              Stacks_and_frames.get_left_sibling_and_focus frm
            with None -> A_start_here.failwitha "impossible"
            | Some (k1, (r1, (k2, (r2, k3)))) ->
              A_start_here.rev_apply
                (A_start_here.rev_apply (A_start_here.rev_apply r1 read)
                  (Monad.fmap Disk_node.dest_Disk_leaf))
                (Monad.bind
                  (fun left_leaf ->
                    (match
                      Arith.equal_nata
                        (A_start_here.rev_apply leaf_ops Disk_node.leaf_length
                          left_leaf)
                        (A_start_here.rev_apply cs
                          Constants_and_size_types.min_leaf_size)
                      with true ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply leaf_ops Disk_node.leaf_merge
                            (left_leaf, leaf))
                          (fun leafa ->
                            A_start_here.rev_apply
                              (write (Disk_node.Disk_leaf leafa))
                              (Monad.bind
                                (fun r ->
                                  A_start_here.rev_apply
                                    (A_start_here.rev_apply
                                      (A_start_here.rev_apply frm
(A_start_here.rev_apply frame_ops Stacks_and_frames.replace
  (k1, (r1, ([(k2, r2)], k3))) (k1, (r, ([], k3)))))
                                      (A_start_here.rev_apply frame_ops
Stacks_and_frames.frame_to_node))
                                    post_mergea)))
                      | false ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply leaf_ops
                            Disk_node.leaf_steal_left (left_leaf, leaf))
                          (fun (left_leafa, (k, leafa)) ->
                            A_start_here.rev_apply
                              (write (Disk_node.Disk_leaf left_leafa))
                              (Monad.bind
                                (fun r1a ->
                                  A_start_here.rev_apply
                                    (write (Disk_node.Disk_leaf leafa))
                                    (Monad.bind
                                      (fun r2a ->
A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply
      (A_start_here.rev_apply
        (A_start_here.rev_apply frm
          (A_start_here.rev_apply frame_ops Stacks_and_frames.replace
            (k1, (r1, ([(k2, r2)], k3))) (k1, (r1a, ([(k, r2a)], k3)))))
        (A_start_here.rev_apply frame_ops Stacks_and_frames.frame_to_node))
      (fun a -> Disk_node.Disk_node a))
    write)
  (Monad.fmap (fun a -> Delete_state.D_updated_subtree a)))))))))))
        | Some (k1, (r1, (k2, (r2, k3)))) ->
          A_start_here.rev_apply
            (A_start_here.rev_apply (A_start_here.rev_apply r2 read)
              (Monad.fmap Disk_node.dest_Disk_leaf))
            (Monad.bind
              (fun right_leaf ->
                (match
                  Arith.equal_nata
                    (A_start_here.rev_apply leaf_ops Disk_node.leaf_length
                      right_leaf)
                    (A_start_here.rev_apply cs
                      Constants_and_size_types.min_leaf_size)
                  with true ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply leaf_ops Disk_node.leaf_merge
                        (leaf, right_leaf))
                      (fun leafa ->
                        A_start_here.rev_apply
                          (write (Disk_node.Disk_leaf leafa))
                          (Monad.bind
                            (fun r ->
                              A_start_here.rev_apply
                                (A_start_here.rev_apply
                                  (A_start_here.rev_apply frm
                                    (A_start_here.rev_apply frame_ops
                                      Stacks_and_frames.replace
                                      (k1, (r1, ([(k2, r2)], k3)))
                                      (k1, (r, ([], k3)))))
                                  (A_start_here.rev_apply frame_ops
                                    Stacks_and_frames.frame_to_node))
                                post_mergea)))
                  | false ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply leaf_ops
                        Disk_node.leaf_steal_right (leaf, right_leaf))
                      (fun (leafa, (k, right_leafa)) ->
                        A_start_here.rev_apply
                          (write (Disk_node.Disk_leaf leafa))
                          (Monad.bind
                            (fun r1a ->
                              A_start_here.rev_apply
                                (write (Disk_node.Disk_leaf right_leafa))
                                (Monad.bind
                                  (fun r2a ->
                                    A_start_here.rev_apply
                                      (A_start_here.rev_apply
(A_start_here.rev_apply
  (A_start_here.rev_apply
    (A_start_here.rev_apply frm
      (A_start_here.rev_apply frame_ops Stacks_and_frames.replace
        (k1, (r1, ([(k2, r2)], k3))) (k1, (r1a, ([(k, r2a)], k3)))))
    (A_start_here.rev_apply frame_ops Stacks_and_frames.frame_to_node))
  (fun a -> Disk_node.Disk_node a))
write)
                                      (Monad.fmap
(fun a -> Delete_state.D_updated_subtree a))))))))))));;

let rec step_up
  cs leaf_ops node_ops frame_ops store_ops du =
    (let (f, stk) = du in
     let (_, write) =
       (A_start_here.rev_apply store_ops Post_monad.read,
         A_start_here.rev_apply store_ops Post_monad.wrte)
       in
     let _ = post_merge cs node_ops store_ops in
      (match stk with [] -> A_start_here.failwitha "delete, step_up"
        | frm :: stka ->
          A_start_here.rev_apply
            (match f
              with Delete_state.D_small_leaf a ->
                step_up_small_leaf cs leaf_ops node_ops frame_ops store_ops frm
                  a
              | Delete_state.D_small_node a ->
                step_up_small_node cs leaf_ops node_ops frame_ops store_ops frm
                  a
              | Delete_state.D_updated_subtree r ->
                A_start_here.rev_apply
                  (A_start_here.rev_apply frm
                    (A_start_here.rev_apply frame_ops
                      Stacks_and_frames.get_focus))
                  (fun (k1, (r1, k2)) ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply
                        (A_start_here.rev_apply
                          (A_start_here.rev_apply
                            (A_start_here.rev_apply frm
                              (A_start_here.rev_apply frame_ops
                                Stacks_and_frames.replace (k1, (r1, ([], k2)))
                                (k1, (r, ([], k2)))))
                            (A_start_here.rev_apply frame_ops
                              Stacks_and_frames.frame_to_node))
                          (fun a -> Disk_node.Disk_node a))
                        write)
                      (Monad.fmap (fun a -> Delete_state.D_updated_subtree a))))
            (Monad.fmap (fun y -> (y, stka)))));;

let rec delete_step
  cs leaf_ops node_ops frame_ops store_ops =
    (let write = A_start_here.rev_apply store_ops Post_monad.wrte in
      (fun a ->
        (match a
          with Delete_state.D_down (f, r0) ->
            (match Find_state.dest_F_finished f
              with None ->
                A_start_here.rev_apply (Find.find_step frame_ops store_ops f)
                  (Monad.fmap (fun fa -> Delete_state.D_down (fa, r0)))
              | Some (r0a, (k, (_, (leaf, stk)))) ->
                (match
                  A_start_here.rev_apply leaf_ops Disk_node.leaf_lookup k leaf
                  with None -> Monad.return (Delete_state.D_finished r0a)
                  | Some _ ->
                    (let leafa =
                       A_start_here.rev_apply leaf_ops Disk_node.leaf_remove k
                         leaf
                       in
                      (match
                        Arith.less_nat
                          (A_start_here.rev_apply leaf_ops Disk_node.leaf_length
                            leafa)
                          (A_start_here.rev_apply cs
                            Constants_and_size_types.min_leaf_size)
                        with true ->
                          Monad.return
                            (Delete_state.D_up
                              (Delete_state.D_small_leaf leafa, (stk, r0a)))
                        | false ->
                          A_start_here.rev_apply
                            (A_start_here.rev_apply (Disk_node.Disk_leaf leafa)
                              write)
                            (Monad.fmap
                              (fun r ->
                                Delete_state.D_up
                                  (Delete_state.D_updated_subtree r,
                                    (stk, r0a))))))))
          | Delete_state.D_up (f, (stk, r0)) ->
            (match A_start_here.is_Nil stk
              with true ->
                (match f
                  with Delete_state.D_small_leaf leaf ->
                    A_start_here.rev_apply
                      (A_start_here.rev_apply (Disk_node.Disk_leaf leaf) write)
                      (Monad.fmap (fun aa -> Delete_state.D_finished aa))
                  | Delete_state.D_small_node n ->
                    (match
                      Arith.equal_nata
                        (A_start_here.rev_apply node_ops
                          Disk_node.node_keys_length n)
                        Arith.zero_nat
                      with true ->
                        Monad.return
                          (Delete_state.D_finished
                            (A_start_here.rev_apply node_ops
                              Disk_node.node_get_single_r n))
                      | false ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply (Disk_node.Disk_node n) write)
                          (Monad.fmap (fun aa -> Delete_state.D_finished aa)))
                  | Delete_state.D_updated_subtree r ->
                    Monad.return (Delete_state.D_finished r))
              | false ->
                A_start_here.rev_apply
                  (step_up cs leaf_ops node_ops frame_ops store_ops (f, stk))
                  (Monad.fmap
                    (fun (fa, stka) -> Delete_state.D_up (fa, (stka, r0)))))
          | Delete_state.D_finished _ ->
            A_start_here.failwitha "delete_step 1")));;

let rec delete_big_step
  cs leaf_ops node_ops frame_ops store_ops =
    (let delete_stepa = delete_step cs leaf_ops node_ops frame_ops store_ops in
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
  cs leaf_ops node_ops frame_ops store_ops check_tree_at_r =
    (fun r k ->
      (let d = Delete_state.make_initial_delete_state r k in
        A_start_here.rev_apply
          (delete_big_step cs leaf_ops node_ops frame_ops store_ops d)
          (Monad.bind
            (fun a ->
              (match a
                with Delete_state.D_down _ ->
                  A_start_here.failwitha "delete, impossible"
                | Delete_state.D_up _ ->
                  A_start_here.failwitha "delete, impossible"
                | Delete_state.D_finished ra ->
                  A_start_here.rev_apply (check_tree_at_r ra)
                    (Monad.bind (fun _ -> Monad.return ra)))))));;

end;; (*struct Delete*)

module Insert : sig
  val insert_step :
    Constants_and_size_types.constants ->
      ('a, 'b, 'c) Disk_node.leaf_ops ->
        ('a, 'd, 'e) Disk_node.node_ops ->
          ('a, 'd, 'f, 'e) Stacks_and_frames.frame_ops ->
            ('d, ('e, 'c) Disk_node.dnode, 'g) Post_monad.store_ops ->
              ('a, 'b, 'd, 'c, 'f) Insert_state.insert_state ->
                (('a, 'b, 'd, 'c, 'f) Insert_state.insert_state, 'g) Monad.mm
  val insert :
    Constants_and_size_types.constants ->
      ('a, 'b, 'c) Disk_node.leaf_ops ->
        ('a, 'd, 'e) Disk_node.node_ops ->
          ('a, 'd, 'f, 'e) Stacks_and_frames.frame_ops ->
            ('d, ('e, 'c) Disk_node.dnode, 'g) Post_monad.store_ops ->
              ('d -> (bool, 'g) Monad.mm) ->
                'd -> 'a -> 'b -> (('d option), 'g) Monad.mm
end = struct

let rec step_bottom
  cs leaf_ops node_ops store_ops d =
    (let (write, rewrite) =
       (A_start_here.rev_apply store_ops Post_monad.wrte,
         A_start_here.rev_apply store_ops Post_monad.rewrite)
       in
     let (fs, v) = d in
      (match Find_state.dest_F_finished fs
        with None -> A_start_here.failwitha "insert, step_bottom, 1"
        | Some (_, (k, (r, (leaf, stk)))) ->
          (let (leafa, _) =
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
                (let (leaf1, (ka, leaf2)) =
                   A_start_here.rev_apply leaf_ops Disk_node.split_large_leaf
                     (A_start_here.rev_apply cs
                       Constants_and_size_types.max_leaf_size)
                     leafa
                   in
                  A_start_here.rev_apply
                    (A_start_here.rev_apply (Disk_node.Disk_leaf leaf1) write)
                    (Monad.bind
                      (fun r1 ->
                        A_start_here.rev_apply
                          (A_start_here.rev_apply (Disk_node.Disk_leaf leaf2)
                            write)
                          (Monad.bind
                            (fun r2 ->
                              Monad.return
                                (Sum_Type.Inl
                                  (Insert_state.I2 (r1, (ka, r2)),
                                    stk)))))))))));;

let rec step_down
  frame_ops store_ops =
    (let find_step = Find.find_step frame_ops store_ops in
      (fun (fs, v) ->
        A_start_here.rev_apply (find_step fs) (Monad.fmap (fun d -> (d, v)))));;

let rec step_up
  cs node_ops frame_ops store_ops u =
    (let (write, rewrite) =
       (A_start_here.rev_apply store_ops Post_monad.wrte,
         A_start_here.rev_apply store_ops Post_monad.rewrite)
       in
      (match u with (_, []) -> A_start_here.failwitha "insert, step_up,1"
        | (fo, frm :: stk) ->
          (let backing_r =
             A_start_here.rev_apply frame_ops
               Stacks_and_frames.backing_node_blk_ref frm
             in
            (match fo
              with Insert_state.I1 r ->
                (let (k1, (r1, k2)) =
                   A_start_here.rev_apply frame_ops Stacks_and_frames.get_focus
                     frm
                   in
                  A_start_here.rev_apply
                    (A_start_here.rev_apply
                      (A_start_here.rev_apply
                        (A_start_here.rev_apply
                          (A_start_here.rev_apply frm
                            (A_start_here.rev_apply frame_ops
                              Stacks_and_frames.replace (k1, (r1, ([], k2)))
                              (k1, (r, ([], k2)))))
                          (A_start_here.rev_apply frame_ops
                            Stacks_and_frames.frame_to_node))
                        (fun a -> Disk_node.Disk_node a))
                      (rewrite backing_r))
                    (Monad.bind
                      (fun a ->
                        (match a with None -> Monad.return (Sum_Type.Inr ())
                          | Some r2 ->
                            Monad.return
                              (Sum_Type.Inl (Insert_state.I1 r2, stk))))))
              | Insert_state.I2 (r, (k, ra)) ->
                (let (k1, (r1, k2)) =
                   A_start_here.rev_apply frame_ops Stacks_and_frames.get_focus
                     frm
                   in
                 let n =
                   A_start_here.rev_apply
                     (A_start_here.rev_apply frm
                       (A_start_here.rev_apply frame_ops
                         Stacks_and_frames.replace (k1, (r1, ([], k2)))
                         (k1, (r, ([(k, ra)], k2)))))
                     (A_start_here.rev_apply frame_ops
                       Stacks_and_frames.frame_to_node)
                   in
                  (match
                    Arith.less_eq_nat
                      (A_start_here.rev_apply node_ops
                        Disk_node.node_keys_length n)
                      (A_start_here.rev_apply cs
                        Constants_and_size_types.max_node_keys)
                    with true ->
                      A_start_here.rev_apply
                        (A_start_here.rev_apply (Disk_node.Disk_node n)
                          (rewrite backing_r))
                        (Monad.bind
                          (fun a ->
                            (match a with None -> Monad.return (Sum_Type.Inr ())
                              | Some r2 ->
                                Monad.return
                                  (Sum_Type.Inl (Insert_state.I1 r2, stk)))))
                    | false ->
                      (let index =
                         A_start_here.rev_apply cs
                           Constants_and_size_types.max_node_keys
                         in
                       let (n1, (ka, n2)) =
                         A_start_here.rev_apply node_ops
                           Disk_node.split_node_at_k_index index n
                         in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply (Disk_node.Disk_node n1)
                            write)
                          (Monad.bind
                            (fun r1a ->
                              A_start_here.rev_apply
                                (A_start_here.rev_apply (Disk_node.Disk_node n2)
                                  write)
                                (Monad.bind
                                  (fun r2 ->
                                    Monad.return
                                      (Sum_Type.Inl
(Insert_state.I2 (r1a, (ka, r2)), stk)))))))))))));;

let rec insert_step
  cs leaf_ops node_ops frame_ops store_ops =
    (let step_downa = step_down frame_ops store_ops in
     let step_bottoma = step_bottom cs leaf_ops node_ops store_ops in
     let step_upa = step_up cs node_ops frame_ops store_ops in
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
                  (A_start_here.rev_apply
                    (Disk_node.Disk_node
                      (A_start_here.rev_apply node_ops
                        Disk_node.node_make_small_root (r1, (k, r2))))
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
  cs leaf_ops node_ops frame_ops store_ops =
    (let insert_stepa = insert_step cs leaf_ops node_ops frame_ops store_ops in
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
  cs leaf_ops node_ops frame_ops store_ops check_tree_at_r =
    (fun r k v ->
      (let i = Insert_state.make_initial_insert_state r k v in
        A_start_here.rev_apply
          (insert_big_step cs leaf_ops node_ops frame_ops store_ops i)
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
                    (Monad.bind (fun _ -> Monad.return None)))))));;

end;; (*struct Insert*)

module Insert_many : sig
  val im_step :
    Constants_and_size_types.constants ->
      ('a -> 'a -> Arith.int) ->
        ('a, 'b, 'c) Disk_node.leaf_ops ->
          ('a, 'd, 'e) Disk_node.node_ops ->
            ('a, 'd, 'f, 'e) Stacks_and_frames.frame_ops ->
              ('d, ('e, 'c) Disk_node.dnode, 'g) Post_monad.store_ops ->
                ('a, 'b, 'd, 'c, 'f) Insert_state.insert_state *
                  ('a * 'b) list ->
                  ((('a, 'b, 'd, 'c, 'f) Insert_state.insert_state *
                     ('a * 'b) list),
                    'g)
                    Monad.mm
end = struct

let rec im_step_bottom
  cs k_cmp leaf_ops node_ops frame_ops store_ops =
    (fun d kvs0 ->
      (let (fs, _) = d in
        (match Find_state.dest_F_finished fs
          with None -> A_start_here.impossible1 "insert, step_bottom"
          | Some (_, (_, (_, (leaf, stk)))) ->
            (let (_, u) = Stacks_and_frames.get_bounds frame_ops stk in
             let step =
               (fun s ->
                 (match s with (_, (_, [])) -> None
                   | (leafa, (len_leaf, (k, v) :: kvs)) ->
                     (let _ =
                        A_start_here.check_true
                          (fun _ ->
                            Arith.less_eq_nat len_leaf
                              (Arith.times_nat
                                (A_start_here.rev_apply cs
                                  Constants_and_size_types.max_leaf_size)
                                (Arith.nat_of_integer
                                  (Big_int.big_int_of_int 2))))
                        in
                      let test1 =
                        Arith.equal_nata len_leaf
                          (Arith.times_nat
                            (A_start_here.rev_apply cs
                              Constants_and_size_types.max_leaf_size)
                            (Arith.nat_of_integer (Big_int.big_int_of_int 2)))
                        in
                      let test2 =
                        (match u with None -> false
                          | Some ua -> Key_value.key_le k_cmp ua k)
                        in
                       (match test1 || test2 with true -> None
                         | false ->
                           (let (leafb, old_v) =
                              A_start_here.rev_apply leaf_ops
                                Disk_node.leaf_insert k v leafa
                              in
                            let len_leafa =
                              (if A_start_here.is_None old_v
                                then Arith.plus_nat len_leaf Arith.one_nat
                                else len_leaf)
                              in
                             Some (leafb, (len_leafa, kvs)))))))
               in
              A_start_here.rev_apply
                (A_start_here.iter_step step
                  (leaf,
                    (A_start_here.rev_apply leaf_ops Disk_node.leaf_length leaf,
                      kvs0)))
                (fun (leafa, (len_leaf, kvs)) ->
                  (match
                    Arith.less_eq_nat len_leaf
                      (A_start_here.rev_apply cs
                        Constants_and_size_types.max_leaf_size)
                    with true ->
                      A_start_here.rev_apply
                        (A_start_here.rev_apply (Disk_node.Disk_leaf leafa)
                          (A_start_here.rev_apply store_ops Post_monad.wrte))
                        (Monad.fmap (fun r -> ((Insert_state.I1 r, stk), kvs)))
                    | false ->
                      (let (leaf1, (k, leaf2)) =
                         A_start_here.rev_apply leaf_ops
                           Disk_node.split_large_leaf
                           (A_start_here.rev_apply cs
                             Constants_and_size_types.max_leaf_size)
                           leafa
                         in
                        A_start_here.rev_apply
                          (A_start_here.rev_apply (Disk_node.Disk_leaf leaf1)
                            (A_start_here.rev_apply store_ops Post_monad.wrte))
                          (Monad.bind
                            (fun r1 ->
                              A_start_here.rev_apply
                                (A_start_here.rev_apply
                                  (Disk_node.Disk_leaf leaf2)
                                  (A_start_here.rev_apply store_ops
                                    Post_monad.wrte))
                                (Monad.fmap
                                  (fun r2 ->
                                    ((Insert_state.I2 (r1, (k, r2)), stk),
                                      kvs))))))))))));;

let rec im_step
  cs k_cmp leaf_ops node_ops frame_ops store_ops im =
    (let (i, kvs) = im in
      (match i
        with Insert_state.I_down d ->
          (let (fs, _) = d in
            (match Find_state.dest_F_finished fs
              with None ->
                A_start_here.rev_apply
                  (Insert.insert_step cs leaf_ops node_ops frame_ops store_ops
                    i)
                  (Monad.fmap (fun da -> (da, kvs)))
              | Some _ ->
                A_start_here.rev_apply
                  (im_step_bottom cs k_cmp leaf_ops node_ops frame_ops store_ops
                    d kvs)
                  (Monad.fmap (fun (u, a) -> (Insert_state.I_up u, a)))))
        | Insert_state.I_up _ ->
          A_start_here.rev_apply
            (Insert.insert_step cs leaf_ops node_ops frame_ops store_ops i)
            (Monad.fmap (fun u -> (u, kvs)))
        | Insert_state.I_finished _ -> A_start_here.failwitha "im_step 1"
        | Insert_state.I_finished_with_mutate ->
          A_start_here.failwitha " im_step 2"));;

end;; (*struct Insert_many*)

module Leaf_stream_state : sig
  type ('a, 'b, 'c) ls_state = LS_down of ('a * 'c list) |
    LS_leaf of ('b * 'c list) | LS_up of 'c list
  val dest_LS_leaf : ('a, 'b, 'c) ls_state -> 'b option
  val ls_is_finished : ('a, 'b, 'c) ls_state -> bool
  val make_initial_ls_state : 'a -> ('a, 'b, 'c) ls_state
end = struct

type ('a, 'b, 'c) ls_state = LS_down of ('a * 'c list) |
  LS_leaf of ('b * 'c list) | LS_up of 'c list;;

let rec dest_LS_leaf
  x = (match x with LS_down _ -> None | LS_leaf (leaf, _) -> Some leaf
        | LS_up _ -> None);;

let rec ls_is_finished
  lss = (match lss with LS_down _ -> false | LS_leaf _ -> false
          | LS_up [] -> true | LS_up (_ :: _) -> false);;

let rec make_initial_ls_state r = LS_down (r, []);;

end;; (*struct Leaf_stream_state*)

module Leaf_stream : sig
  val ls_step_to_next_leaf :
    ('a, 'b, 'c, 'd) Stacks_and_frames.frame_ops ->
      ('b, ('d, 'e) Disk_node.dnode, 'f) Post_monad.store_ops ->
        ('b, 'e, 'c) Leaf_stream_state.ls_state ->
          ((('b, 'e, 'c) Leaf_stream_state.ls_state option), 'f) Monad.mm
end = struct

let rec step_leaf r = (let a = r in
                       let (_, aa) = a in
                        Leaf_stream_state.LS_up aa);;

let rec step_down
  frame_ops store_ops r_fs =
    (let (r, fs) = r_fs in
      A_start_here.rev_apply
        (A_start_here.rev_apply store_ops Post_monad.read r)
        (Monad.fmap
          (fun a ->
            (match a
              with Disk_node.Disk_node n ->
                (let frm =
                   A_start_here.rev_apply frame_ops
                     Stacks_and_frames.split_node_on_first_key n
                   in
                 let ra =
                   A_start_here.rev_apply frame_ops Stacks_and_frames.midpoint
                     frm
                   in
                  Leaf_stream_state.LS_down (ra, frm :: fs))
              | Disk_node.Disk_leaf leaf ->
                Leaf_stream_state.LS_leaf (leaf, fs)))));;

let rec step_up
  frame_ops fs =
    (match fs with [] -> A_start_here.failwitha "Leaf_stream, step_up"
      | frm :: fsa ->
        (match
          A_start_here.rev_apply frame_ops Stacks_and_frames.step_frame_for_ls
            frm
          with None -> Leaf_stream_state.LS_up fsa
          | Some frma ->
            (let r =
               A_start_here.rev_apply frame_ops Stacks_and_frames.midpoint frma
               in
              Leaf_stream_state.LS_down (r, frma :: fsa))));;

let rec ls_step
  frame_ops store_ops lss =
    (match lss
      with Leaf_stream_state.LS_down a -> step_down frame_ops store_ops a
      | Leaf_stream_state.LS_leaf x -> Monad.return (step_leaf x)
      | Leaf_stream_state.LS_up x -> Monad.return (step_up frame_ops x));;

let rec ls_step_to_next_leaf
  frame_ops store_ops lss =
    (match Leaf_stream_state.ls_is_finished lss with true -> Monad.return None
      | false ->
        A_start_here.rev_apply
          (A_start_here.rev_apply (ls_step frame_ops store_ops lss)
            (Monad.bind
              (fun lssa ->
                A_start_here.rev_apply (lssa, false)
                  (Post_monad.iter_m
                    (fun s ->
                      (match s with (_, true) -> Monad.return None
                        | (lssb, false) ->
                          (match Leaf_stream_state.ls_is_finished lssb
                            with true -> Monad.return (Some (lssb, true))
                            | false ->
                              (match Leaf_stream_state.dest_LS_leaf lssb
                                with None ->
                                  A_start_here.rev_apply
                                    (ls_step frame_ops store_ops lssb)
                                    (Monad.fmap
                                      (fun lssc -> Some (lssc, false)))
                                | Some _ -> Monad.return None))))))))
          (Monad.fmap
            (fun a ->
              (match a with (_, true) -> None | (lssa, false) -> Some lssa))));;

end;; (*struct Leaf_stream*)

module Insert_many_state : sig
  val make_initial_im_state :
    'a -> 'b -> 'c -> ('b * 'c) list ->
                        ('b, 'c, 'a, 'd, 'e) Insert_state.insert_state *
                          ('b * 'c) list
end = struct

let rec make_initial_im_state
  r k v kvs =
    (let i = Insert_state.make_initial_insert_state r k v in (i, kvs));;

end;; (*struct Insert_many_state*)

end (* Make *)
