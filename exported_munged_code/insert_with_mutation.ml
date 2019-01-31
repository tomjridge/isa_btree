module Fun : sig
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module Product_Type : sig
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
end = struct

let rec apsnd f (x, y) = (x, f y);;

let rec fst (x1, x2) = x1;;

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
  type nat = Zero_nat | Suc of nat
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat Orderings.ord
  type num = One | Bit0 of num | Bit1 of num
  type int = Zero_int | Pos of num | Neg of num
  val nat_of_num : num -> nat
  val less_int : int -> int -> bool
  val int_of_integer : Big_int.big_int -> int
  val divide_nat : nat -> nat -> nat
end = struct

type nat = Zero_nat | Suc of nat;;

let rec less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                      | Zero_nat, n -> true
and less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
               | n, Zero_nat -> false;;

let ord_nat =
  ({Orderings.less_eq = less_eq_nat; Orderings.less = less_nat} :
    nat Orderings.ord);;

type num = One | Bit0 of num | Bit1 of num;;

type int = Zero_int | Pos of num | Neg of num;;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec uminus_int = function Neg m -> Pos m
                     | Pos m -> Neg m
                     | Zero_int -> Zero_int;;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let one_int : int = Pos One;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_int
    | Bit1 m, Bit0 n -> plus_int (dup (sub m n)) one_int
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and plus_int k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
               | Neg m, Pos n -> sub n m
               | Pos m, Neg n -> sub m n
               | Pos m, Pos n -> Pos (plus_num m n)
               | Zero_int, l -> l
               | k, Zero_int -> k
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_int l
                | k, Zero_int -> k;;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nat m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nat m m)
    | One -> one_nat;;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec equal_nat x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                    | Suc x2, Zero_nat -> false
                    | Suc x2, Suc y2 -> equal_nat x2 y2
                    | Zero_nat, Zero_nat -> true;;

let rec divmod_nat
  m n = (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let a = divmod_nat (minus_nat m n) n in
                let (q, aa) = a in
                 (Suc q, aa)));;

let rec less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
                   | Bit1 m, Bit1 n -> less_num m n
                   | Bit0 m, Bit1 n -> less_eq_num m n
                   | Bit0 m, Bit0 n -> less_num m n
                   | One, Bit1 n -> true
                   | One, Bit0 n -> true
                   | m, One -> false
and less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                  | Bit1 m, Bit1 n -> less_eq_num m n
                  | Bit0 m, Bit1 n -> less_eq_num m n
                  | Bit0 m, Bit0 n -> less_eq_num m n
                  | Bit1 m, One -> false
                  | Bit0 m, One -> false
                  | One, n -> true;;

let rec less_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
                   | Neg k, Pos l -> true
                   | Neg k, Zero_int -> true
                   | Pos k, Neg l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Neg l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

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

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_int k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                    | Neg m, Pos n -> Neg (times_num m n)
                    | Pos m, Neg n -> Neg (times_num m n)
                    | Pos m, Pos n -> Pos (times_num m n)
                    | Zero_int, l -> Zero_int
                    | k, Zero_int -> Zero_int;;

let rec int_of_integer
  k = (if Big_int.lt_big_int k Big_int.zero_big_int
        then uminus_int (int_of_integer (Big_int.minus_big_int k))
        else (if Big_int.eq_big_int k Big_int.zero_big_int then Zero_int
               else (let (l, j) = divmod_integer k (Big_int.big_int_of_int 2) in
                     let la = times_int (Pos (Bit0 One)) (int_of_integer l) in
                      (if Big_int.eq_big_int j Big_int.zero_big_int then la
                        else plus_int la one_int))));;

let rec divide_nat m n = Product_Type.fst (divmod_nat m n);;

end;; (*struct Arith*)

module Lista : sig
  val rev : 'a list -> 'a list
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val size_list : 'a list -> Arith.nat
end = struct

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec hd (x21 :: x22) = x21;;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec gen_length
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.Suc n) xs
    | n, [] -> n;;

let rec size_list x = gen_length Arith.Zero_nat x;;

end;; (*struct Lista*)

module Monad : sig
  type ('a, 'b) mm
  val bind : ('a -> ('b, 'c) mm) -> ('a, 'c) mm -> ('b, 'c) mm
  val fmap : ('a -> 'b) -> ('a, 'c) mm -> ('b, 'c) mm
  val return : 'a -> ('a, 'b) mm
end = struct

type ('a, 'b) mm = EMPTY__;;

let rec bind b a = failwith "undefined";;

let rec fmap x y = failwith "undefined";;

let rec return x = failwith "undefined";;

end;; (*struct Monad*)

module Sum_Type : sig
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
end = struct

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

end;; (*struct Sum_Type*)

module Insert_with_mutation(Monad: module type of Monad) : sig
  type ('a, 'b, 'c) dnode = Disk_node of ('a list * 'c list) |
    Disk_leaf of ('a * 'b) list
  type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c))
  type ('a, 'b, 'c) blk_ops =
    Make_blk_ops of
      ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
        ('a -> 'b -> (('a option), 'c) Monad.mm)
  type ('a, 'b) alloc_ops =
    Make_alloc_ops of
      (unit -> ('a, 'b) Monad.mm) * ('a list -> (unit, 'b) Monad.mm)
  type constants =
    Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat
  type ('a, 'b, 'c) stk_frame
  type ('a, 'b, 'c) find_state
  type ('a, 'b, 'c, 'd) marshal_ops =
    Make_marshal_ops of ('a -> ('b, 'c, 'd) dnode) * (('b, 'c, 'd) dnode -> 'a)
  type ('a, 'b, 'c) insert_state = I_down of (('a, 'b, 'c) find_state * 'b) |
    I_up of
      (('a, 'b, 'c) i12_t *
        (('c list * 'a list), 'c, ('a list * 'c list)) stk_frame list)
    | I_finished of 'c | I_finished_with_mutate
  val insert_step :
    constants ->
      ('a -> 'a -> Arith.int) ->
        ('b, 'c, 'd) blk_ops ->
          ('c, 'a, 'e, 'b) marshal_ops ->
            ('b, 'd) alloc_ops ->
              ('a, 'e, 'b) insert_state ->
                (('a, 'e, 'b) insert_state, 'd) Monad.mm
  val make_initial_find_state : 'a -> 'b -> ('a, 'c, 'b) find_state
end = struct

type ('a, 'b, 'c) dnode = Disk_node of ('a list * 'c list) |
  Disk_leaf of ('a * 'b) list;;

type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c));;

type ('a, 'b, 'c) blk_ops =
  Make_blk_ops of
    ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
      ('a -> 'b -> (('a option), 'c) Monad.mm);;

type ('a, 'b) alloc_ops =
  Make_alloc_ops of
    (unit -> ('a, 'b) Monad.mm) * ('a list -> (unit, 'b) Monad.mm);;

type constants =
  Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat;;

type ('a, 'b, 'c) stk_frame = Frm of ('a * ('b * 'c));;

type ('a, 'b, 'c) find_state =
  F_down of
    ('c * ('a * ('c * (('c list * 'a list), 'c, ('a list * 'c list))
                        stk_frame list)))
  | F_finished of
      ('c * ('a * ('c * (('a * 'b) list *
                          (('c list * 'a list), 'c, ('a list * 'c list))
                            stk_frame list))));;

type ('a, 'b, 'c, 'd) marshal_ops =
  Make_marshal_ops of ('a -> ('b, 'c, 'd) dnode) * (('b, 'c, 'd) dnode -> 'a);;

type ('a, 'b, 'c) insert_state = I_down of (('a, 'b, 'c) find_state * 'b) |
  I_up of
    (('a, 'b, 'c) i12_t *
      (('c list * 'a list), 'c, ('a list * 'c list)) stk_frame list)
  | I_finished of 'c | I_finished_with_mutate;;

let rec key_lt ord k1 k2 = Arith.less_int (ord k1 k2) Arith.Zero_int;;

let rec max_node_keys (Make_constants (x1, x2, x3, x4)) = x4;;

let rec dnode2blk (Make_marshal_ops (x1, x2)) = x2;;

let rec rewrite (Make_blk_ops (x1, x2, x3)) = x3;;

let rec alloc (Make_alloc_ops (x1, x2)) = x1;;

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

let rec wrte (Make_blk_ops (x1, x2, x3)) = x2;;

let rec rev_apply x f = f x;;

let rec failwitha x = rev_apply "FIXME patch" (fun _ -> failwith "undefined");;

let rec impossible1 x = failwitha x;;

let rec min_node_keys (Make_constants (x1, x2, x3, x4)) = x3;;

let rec iter_step
  f x = (let a = f x in (match a with None -> x | Some aa -> iter_step f aa));;

let rec split_node
  cs n =
    (let (ks, rs) = n in
     let l =
       Arith.divide_nat (Lista.size_list ks)
         (Arith.nat_of_num (Arith.Bit0 Arith.One))
       in
     let la = Orderings.max Arith.ord_nat (rev_apply cs min_node_keys) l in
      rev_apply
        (iter_step
          (fun (ksb, (rsb, (ksa, rsa))) ->
            (match (ksa, rsa) with ([], _) -> impossible1 "split_node"
              | (_ :: _, []) -> impossible1 "split_node"
              | (k :: ksaa, r :: rsaa) ->
                (match Arith.less_nat (Lista.size_list ksb) la
                  with true -> Some (k :: ksb, (r :: rsb, (ksaa, rsaa)))
                  | false -> None)))
          ([], ([], (ks, rs))))
        (fun (ksb, (rsb, (ksa, rsa))) ->
          (let (k :: ksaa, r :: rsaa) = (ksa, rsa) in
            ((Lista.rev ksb, Lista.rev (r :: rsb)), (k, (ksaa, rsaa))))));;

let rec dest_Frm (Frm (a, (b, c))) = (a, (b, c));;

let rec step_up
  cs k_cmp blk_ops marshal_ops alloc_ops u =
    (let (write, _) = (rev_apply blk_ops wrte, rev_apply blk_ops rewrite) in
     let dnode2blka = rev_apply marshal_ops dnode2blk in
     let _ = rev_apply alloc_ops alloc in
      (match u with (_, []) -> impossible1 "insert, step_up"
        | (fo, frm :: stk) ->
          (let a = dest_Frm frm in
           let (aa, b) = a in
            (let (rs1, ks1) = aa in
              (fun (_, (ks2, rs2)) ->
                (match fo
                  with I1 r ->
                    (let (ks, rs) =
                       unsplit_node ((rs1, ks1), (([r], []), (ks2, rs2))) in
                      rev_apply (rev_apply (Disk_node (ks, rs)) dnode2blka)
                        (fun blk ->
                          rev_apply (write blk)
                            (Monad.bind (fun ra -> Monad.return (I1 ra, stk)))))
                  | I2 (r1, (k, r2)) ->
                    (let (ks, rs) =
                       unsplit_node ((rs1, ks1), (([r1; r2], [k]), (ks2, rs2)))
                       in
                      (match
                        Arith.less_eq_nat (Lista.size_list ks)
                          (rev_apply cs max_node_keys)
                        with true ->
                          rev_apply (rev_apply (Disk_node (ks, rs)) dnode2blka)
                            (fun blk ->
                              rev_apply (write blk)
                                (Monad.bind
                                  (fun r -> Monad.return (I1 r, stk))))
                        | false ->
                          (let (ks_rs1, (ka, ks_rs2)) = split_node cs (ks, rs)
                             in
                            rev_apply (rev_apply (Disk_node ks_rs1) dnode2blka)
                              (fun blk ->
                                rev_apply (write blk)
                                  (Monad.bind
                                    (fun r1a ->
                                      rev_apply
(rev_apply (Disk_node ks_rs2) dnode2blka)
(fun blka ->
  rev_apply (write blka)
    (Monad.bind (fun r2a -> Monad.return (I2 (r1a, (ka, r2a)), stk)))))))))))))
              b)));;

let rec blk2dnode (Make_marshal_ops (x1, x2)) = x1;;

let rec read (Make_blk_ops (x1, x2, x3)) = x1;;

let rec make_frame
  k_cmp k ks rs =
    rev_apply
      (iter_step
        (fun (a, b) ->
          (let (rsa, ksa) = a in
            (fun (ksaa, rsaa) ->
              (match ksaa with [] -> None
                | ka :: ksab ->
                  (match key_lt k_cmp k ka with true -> None
                    | false ->
                      (let (r, rsab) = (Lista.hd rsaa, Lista.tl rsaa) in
                        Some ((r :: rsa, ka :: ksa), (ksab, rsab)))))))
            b)
        (([], []), (ks, rs)))
      (fun (a, b) ->
        (let (rsa, ksa) = a in
          (fun (ksaa, rsaa) ->
            (let r = Lista.hd rsaa in
              (Frm ((rsa, ksa), (r, (ksaa, Lista.tl rsaa))), r))))
          b);;

let rec find_step
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let reada = rev_apply blk_ops read in
     let blk2dnodea = rev_apply marshal_ops blk2dnode in
      (fun fs ->
        (match fs
          with F_down (r0, (k, (r, stk))) ->
            rev_apply (rev_apply (reada r) (Monad.fmap blk2dnodea))
              (Monad.fmap
                (fun a ->
                  (match a
                    with Disk_node (ks, rs) ->
                      (let (frm, ra) = make_frame k_cmp k ks rs in
                        F_down (r0, (k, (ra, frm :: stk))))
                    | Disk_leaf kvs -> F_finished (r0, (k, (r, (kvs, stk)))))))
          | F_finished _ -> Monad.return fs)));;

let rec step_down
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let find_stepa = find_step cs k_cmp blk_ops marshal_ops alloc_ops in
      (fun (fs, v) ->
        rev_apply (find_stepa fs) (Monad.fmap (fun d -> (d, v)))));;

let rec kvs_insert
  k_cmp k v kvs =
    rev_apply
      (iter_step
        (fun a ->
          (match a with (_, []) -> None
            | (kvsb, (ka, va) :: kvsa) ->
              (match key_lt k_cmp k ka with true -> None
                | false -> Some ((ka, va) :: kvsb, kvsa))))
        ([], kvs))
      (fun (kvsa, a) -> Lista.rev ((k, v) :: kvsa) @ a);;

let rec min_leaf_size (Make_constants (x1, x2, x3, x4)) = x1;;

let rec assert_true b = (if b then b else failwitha "assert_true");;

let rec split_leaf
  cs kvs =
    (let _ = assert_true true in
      rev_apply
        (iter_step
          (fun (kvsb, kvsa) ->
            (match
              Arith.less_eq_nat (Lista.size_list kvsa)
                (rev_apply cs min_leaf_size)
              with true -> None
              | false ->
                (match kvsa with [] -> impossible1 "split_leaf"
                  | (k, v) :: kvsaa -> Some ((k, v) :: kvsb, kvsaa))))
          ([], kvs))
        (fun (kvsb, kvsa) ->
          (Lista.rev kvsb,
            (rev_apply (Lista.hd kvsa) Product_Type.fst, kvsa))));;

let rec dest_F_finished
  fs = (match fs with F_down _ -> None
         | F_finished (r0, (k, (r, (kvs, stk)))) ->
           Some (r0, (k, (r, (kvs, stk)))));;

let rec max_leaf_size (Make_constants (x1, x2, x3, x4)) = x2;;

let rec step_bottom
  cs k_cmp blk_ops marshal_ops alloc_ops d =
    (let (write, rewritea) = (rev_apply blk_ops wrte, rev_apply blk_ops rewrite)
       in
     let dnode2blka = rev_apply marshal_ops dnode2blk in
     let _ = rev_apply alloc_ops alloc in
     let (fs, v) = d in
      (match dest_F_finished fs with None -> impossible1 "insert, step_bottom"
        | Some (_, (k, (r, (kvs, stk)))) ->
          (let kvsa = rev_apply kvs (kvs_insert k_cmp k v) in
            (match
              Arith.less_eq_nat (Lista.size_list kvsa)
                (rev_apply cs max_leaf_size)
              with true ->
                rev_apply (rev_apply (Disk_leaf kvsa) dnode2blka)
                  (fun blk ->
                    rev_apply (rewritea r blk)
                      (Monad.bind
                        (fun a ->
                          (match a with None -> Monad.return (Sum_Type.Inr ())
                            | Some ra ->
                              Monad.return (Sum_Type.Inl (I1 ra, stk))))))
              | false ->
                (let (kvs1, (ka, kvs2)) = split_leaf cs kvsa in
                  rev_apply (rev_apply (Disk_leaf kvs1) dnode2blka)
                    (fun blk ->
                      rev_apply (write blk)
                        (Monad.bind
                          (fun r1 ->
                            rev_apply (rev_apply (Disk_leaf kvs2) dnode2blka)
                              (fun blka ->
                                rev_apply (write blka)
                                  (Monad.bind
                                    (fun r2 ->
                                      Monad.return
(Sum_Type.Inl (I2 (r1, (ka, r2)), stk)))))))))))));;

let rec insert_step
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let step_downa = step_down cs k_cmp blk_ops marshal_ops alloc_ops in
     let step_bottoma = step_bottom cs k_cmp blk_ops marshal_ops alloc_ops in
     let step_upa = step_up cs k_cmp blk_ops marshal_ops alloc_ops in
     let write = rev_apply blk_ops wrte in
     let dnode2blka = rev_apply marshal_ops dnode2blk in
     let _ = rev_apply alloc_ops alloc in
      (fun s ->
        (match s
          with I_down d ->
            (let (fs, _) = d in
              (match dest_F_finished fs
                with None ->
                  rev_apply (step_downa d) (Monad.fmap (fun a -> I_down a))
                | Some _ ->
                  rev_apply (step_bottoma d)
                    (Monad.bind
                      (fun a ->
                        (match a with Sum_Type.Inl u -> Monad.return (I_up u)
                          | Sum_Type.Inr () ->
                            Monad.return I_finished_with_mutate)))))
          | I_up u ->
            (match u with (I1 r, []) -> Monad.return (I_finished r)
              | (I2 (r1, (k, r2)), []) ->
                rev_apply (rev_apply (Disk_node ([k], [r1; r2])) dnode2blka)
                  (fun blk ->
                    rev_apply (write blk)
                      (Monad.bind (fun r -> Monad.return (I_finished r))))
              | (_, _ :: _) ->
                rev_apply (step_upa u) (Monad.fmap (fun a -> I_up a)))
          | I_finished _ -> Monad.return s
          | I_finished_with_mutate -> Monad.return s)));;

let rec make_initial_find_state k r = F_down (r, (k, (r, [])));;

end;; (*struct Insert_with_mutation*)
