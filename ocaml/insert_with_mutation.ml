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
  type nat
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat Orderings.ord
  type int = Int_of_integer of Big_int.big_int
  type num = One | Bit0 of num | Bit1 of num
  val suc : nat -> nat
  val less_int : int -> int -> bool
  val zero_int : int
  val zero_nat : nat
  val nat_of_integer : Big_int.big_int -> nat
  val equal_int : int -> int -> bool
  val divide_nat : nat -> nat -> nat
end = struct

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

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

let rec divide_integer k l = Product_Type.fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

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
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.suc n) xs
    | n, [] -> n;;

let rec size_list x = gen_length Arith.zero_nat x;;

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

module Pre_monad : sig
  type ('a, 'b, 'c) dnode = Disk_node of ('a list * 'c list) |
    Disk_leaf of ('a * 'b) list
  type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c))
  type constants =
    Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat
  type ('a, 'b, 'c, 'd) stk_frame
  type ('a, 'b, 'c) find_state =
    F_down of
      ('c * ('a * ('c * (('c list * 'a list), 'c, ('a list * 'c list), 'c)
                          stk_frame list)))
    | F_finished of
        ('c * ('a * ('c * (('a * 'b) list *
                            (('c list * 'a list), 'c, ('a list * 'c list), 'c)
                              stk_frame list))))
  type ('a, 'b, 'c) insert_state = I_down of (('a, 'b, 'c) find_state * 'b) |
    I_up of
      (('a, 'b, 'c) i12_t *
        (('c list * 'a list), 'c, ('a list * 'c list), 'c) stk_frame list)
    | I_finished of 'c | I_finished_with_mutate
  val dest_Frm : ('a, 'b, 'c, 'd) stk_frame -> 'a * ('b * ('c * 'd))
  val rev_apply : 'a -> ('a -> 'b) -> 'b
  val kvs_insert :
    ('a -> 'a -> Arith.int) -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
  val make_frame :
    ('a -> 'a -> Arith.int) ->
      'a -> 'b -> 'a list ->
                    'b list ->
                      (('b list * 'a list), 'b, ('a list * 'b list), 'b)
                        stk_frame *
                        'b
  val impossible1 : string -> 'a
  val split_leaf :
    constants -> ('a * 'b) list -> ('a * 'b) list * ('a * ('a * 'b) list)
  val split_node :
    constants ->
      'a list * 'b list -> ('a list * 'b list) * ('a * ('a list * 'b list))
  val unsplit_node :
    ('a list * 'b list) * (('a list * 'b list) * ('b list * 'a list)) ->
      'b list * 'a list
  val dest_F_finished :
    ('a, 'b, 'c) find_state ->
      ('c * ('a * ('c * (('a * 'b) list *
                          (('c list * 'a list), 'c, ('a list * 'c list), 'c)
                            stk_frame list)))) option
  val max_leaf_size : constants -> Arith.nat
  val max_node_keys : constants -> Arith.nat
  val make_initial_find_state : 'a -> 'b -> ('a, 'c, 'b) find_state
end = struct

type ('a, 'b, 'c) dnode = Disk_node of ('a list * 'c list) |
  Disk_leaf of ('a * 'b) list;;

type ('a, 'b, 'c) i12_t = I1 of 'c | I2 of ('c * ('a * 'c));;

type constants =
  Make_constants of Arith.nat * Arith.nat * Arith.nat * Arith.nat;;

type ('a, 'b, 'c, 'd) stk_frame = Frm of ('a * ('b * ('c * 'd)));;

type ('a, 'b, 'c) find_state =
  F_down of
    ('c * ('a * ('c * (('c list * 'a list), 'c, ('a list * 'c list), 'c)
                        stk_frame list)))
  | F_finished of
      ('c * ('a * ('c * (('a * 'b) list *
                          (('c list * 'a list), 'c, ('a list * 'c list), 'c)
                            stk_frame list))));;

type ('a, 'b, 'c) insert_state = I_down of (('a, 'b, 'c) find_state * 'b) |
  I_up of
    (('a, 'b, 'c) i12_t *
      (('c list * 'a list), 'c, ('a list * 'c list), 'c) stk_frame list)
  | I_finished of 'c | I_finished_with_mutate;;

let rec key_eq ord k1 k2 = Arith.equal_int (ord k1 k2) Arith.zero_int;;

let rec key_lt ord k1 k2 = Arith.less_int (ord k1 k2) Arith.zero_int;;

let rec dest_Frm (Frm (a, (b, (c, d)))) = (a, (b, (c, d)));;

let rec rev_apply x f = f x;;

let rec failwitha x = rev_apply "FIXME patch" (fun _ -> failwith "undefined");;

let rec iter_step
  f x = (let a = f x in (match a with None -> x | Some aa -> iter_step f aa));;

let rec kvs_insert
  k_cmp k v kvs =
    rev_apply
      (iter_step
        (fun a ->
          (match a with (_, []) -> None
            | (kvsb, (ka, va) :: kvsa) ->
              (match key_lt k_cmp k ka with true -> None
                | false ->
                  (match key_eq k_cmp k ka with true -> Some (kvsb, kvsa)
                    | false -> Some ((ka, va) :: kvsb, kvsa)))))
        ([], kvs))
      (fun (kvsa, a) -> Lista.rev ((k, v) :: kvsa) @ a);;

let rec make_frame
  k_cmp k r_parent ks rs =
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
              (Frm ((rsa, ksa), (r, ((ksaa, Lista.tl rsaa), r_parent))), r))))
          b);;

let rec min_leaf_size (Make_constants (x1, x2, x3, x4)) = x1;;

let rec impossible1 x = failwitha x;;

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

let rec min_node_keys (Make_constants (x1, x2, x3, x4)) = x3;;

let rec split_node
  cs n =
    (let (ks, rs) = n in
     let l =
       Arith.divide_nat (Lista.size_list ks)
         (Arith.nat_of_integer (Big_int.big_int_of_int 2))
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

let rec dest_F_finished
  fs = (match fs with F_down _ -> None
         | F_finished (r0, (k, (r, (kvs, stk)))) ->
           Some (r0, (k, (r, (kvs, stk)))));;

let rec max_leaf_size (Make_constants (x1, x2, x3, x4)) = x2;;

let rec max_node_keys (Make_constants (x1, x2, x3, x4)) = x4;;

let rec make_initial_find_state k r = F_down (r, (k, (r, [])));;

end;; (*struct Pre_monad*)

module type MONAD = sig
  type t
  type ('a,'t) mm = ('a,t) Tjr_monad.Types.m
  val bind : ('a -> ('b, 'c) mm) -> ('a, 'c) mm -> ('b, 'c) mm
  val fmap : ('a -> 'b) -> ('a, 'c) mm -> ('b, 'c) mm
  val return : 'a -> ('a, 'b) mm
end

module Insert_with_mutation(Monad:MONAD) : sig
  type ('a, 'b, 'c) blk_ops =
    Make_blk_ops of
      ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
        ('a -> 'b -> (('a option), 'c) Monad.mm)
  type ('a, 'b) alloc_ops =
    Make_alloc_ops of
      (unit -> ('a, 'b) Monad.mm) * ('a list -> (unit, 'b) Monad.mm)
  type ('a, 'b, 'c, 'd) marshal_ops =
    Make_marshal_ops of
      ('a -> ('b, 'c, 'd) Pre_monad.dnode) *
        (('b, 'c, 'd) Pre_monad.dnode -> 'a)
  val insert_step :
    Pre_monad.constants ->
      ('a -> 'a -> Arith.int) ->
        ('b, 'c, 'd) blk_ops ->
          ('c, 'a, 'e, 'b) marshal_ops ->
            ('b, 'd) alloc_ops ->
              ('a, 'e, 'b) Pre_monad.insert_state ->
                (('a, 'e, 'b) Pre_monad.insert_state, 'd) Monad.mm
end = struct

type ('a, 'b, 'c) blk_ops =
  Make_blk_ops of
    ('a -> ('b, 'c) Monad.mm) * ('b -> ('a, 'c) Monad.mm) *
      ('a -> 'b -> (('a option), 'c) Monad.mm);;

type ('a, 'b) alloc_ops =
  Make_alloc_ops of
    (unit -> ('a, 'b) Monad.mm) * ('a list -> (unit, 'b) Monad.mm);;

type ('a, 'b, 'c, 'd) marshal_ops =
  Make_marshal_ops of
    ('a -> ('b, 'c, 'd) Pre_monad.dnode) *
      (('b, 'c, 'd) Pre_monad.dnode -> 'a);;

let rec dnode2blk (Make_marshal_ops (x1, x2)) = x2;;

let rec rewrite (Make_blk_ops (x1, x2, x3)) = x3;;

let rec alloc (Make_alloc_ops (x1, x2)) = x1;;

let rec wrte (Make_blk_ops (x1, x2, x3)) = x2;;

let rec step_up
  cs k_cmp blk_ops marshal_ops alloc_ops u =
    (let (write, rewritea) =
       (Pre_monad.rev_apply blk_ops wrte, Pre_monad.rev_apply blk_ops rewrite)
       in
     let dnode2blka = Pre_monad.rev_apply marshal_ops dnode2blk in
     let _ = Pre_monad.rev_apply alloc_ops alloc in
      (match u with (_, []) -> Pre_monad.impossible1 "insert, step_up"
        | (fo, frm :: stk) ->
          (let a = Pre_monad.dest_Frm frm in
           let (aa, b) = a in
            (let (rs1, ks1) = aa in
              (fun (_, ab) ->
                (let (ac, ba) = ab in
                  (let (ks2, rs2) = ac in
                    (fun r_parent ->
                      (match fo
                        with Pre_monad.I1 r ->
                          (let (ks, rs) =
                             Pre_monad.unsplit_node
                               ((rs1, ks1), (([r], []), (ks2, rs2)))
                             in
                            Pre_monad.rev_apply
                              (Pre_monad.rev_apply
                                (Pre_monad.Disk_node (ks, rs)) dnode2blka)
                              (fun blk ->
                                Pre_monad.rev_apply (rewritea r_parent blk)
                                  (Monad.bind
                                    (fun ad ->
                                      (match ad
with None -> Monad.return (Sum_Type.Inr ())
| Some r2 -> Monad.return (Sum_Type.Inl (Pre_monad.I1 r2, stk)))))))
                        | Pre_monad.I2 (r1, (k, r2)) ->
                          (let (ks, rs) =
                             Pre_monad.unsplit_node
                               ((rs1, ks1), (([r1; r2], [k]), (ks2, rs2)))
                             in
                            (match
                              Arith.less_eq_nat (Lista.size_list ks)
                                (Pre_monad.rev_apply cs Pre_monad.max_node_keys)
                              with true ->
                                Pre_monad.rev_apply
                                  (Pre_monad.rev_apply
                                    (Pre_monad.Disk_node (ks, rs)) dnode2blka)
                                  (fun blk ->
                                    Pre_monad.rev_apply (rewritea r_parent blk)
                                      (Monad.bind
(fun ad ->
  (match ad with None -> Monad.return (Sum_Type.Inr ())
    | Some r2a -> Monad.return (Sum_Type.Inl (Pre_monad.I1 r2a, stk))))))
                              | false ->
                                (let (ks_rs1, (ka, ks_rs2)) =
                                   Pre_monad.split_node cs (ks, rs) in
                                  Pre_monad.rev_apply
                                    (Pre_monad.rev_apply
                                      (Pre_monad.Disk_node ks_rs1) dnode2blka)
                                    (fun blk ->
                                      Pre_monad.rev_apply (write blk)
(Monad.bind
  (fun r1a ->
    Pre_monad.rev_apply
      (Pre_monad.rev_apply (Pre_monad.Disk_node ks_rs2) dnode2blka)
      (fun blka ->
        Pre_monad.rev_apply (write blka)
          (Monad.bind
            (fun r2a ->
              Monad.return
                (Sum_Type.Inl (Pre_monad.I2 (r1a, (ka, r2a)), stk))))))))))))))
                    ba)))
              b)));;

let rec blk2dnode (Make_marshal_ops (x1, x2)) = x1;;

let rec read (Make_blk_ops (x1, x2, x3)) = x1;;

let rec find_step
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let reada = Pre_monad.rev_apply blk_ops read in
     let blk2dnodea = Pre_monad.rev_apply marshal_ops blk2dnode in
      (fun fs ->
        (match fs
          with Pre_monad.F_down (r0, (k, (r, stk))) ->
            Pre_monad.rev_apply
              (Pre_monad.rev_apply (reada r) (Monad.fmap blk2dnodea))
              (Monad.fmap
                (fun a ->
                  (match a
                    with Pre_monad.Disk_node (ks, rs) ->
                      (let (frm, ra) = Pre_monad.make_frame k_cmp k r ks rs in
                        Pre_monad.F_down (r0, (k, (ra, frm :: stk))))
                    | Pre_monad.Disk_leaf kvs ->
                      Pre_monad.F_finished (r0, (k, (r, (kvs, stk)))))))
          | Pre_monad.F_finished _ -> Monad.return fs)));;

let rec step_down
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let find_stepa = find_step cs k_cmp blk_ops marshal_ops alloc_ops in
      (fun (fs, v) ->
        Pre_monad.rev_apply (find_stepa fs) (Monad.fmap (fun d -> (d, v)))));;

let rec step_bottom
  cs k_cmp blk_ops marshal_ops alloc_ops d =
    (let (write, rewritea) =
       (Pre_monad.rev_apply blk_ops wrte, Pre_monad.rev_apply blk_ops rewrite)
       in
     let dnode2blka = Pre_monad.rev_apply marshal_ops dnode2blk in
     let _ = Pre_monad.rev_apply alloc_ops alloc in
     let (fs, v) = d in
      (match Pre_monad.dest_F_finished fs
        with None -> Pre_monad.impossible1 "insert, step_bottom"
        | Some (_, (k, (r, (kvs, stk)))) ->
          (let kvsa = Pre_monad.rev_apply kvs (Pre_monad.kvs_insert k_cmp k v)
             in
            (match
              Arith.less_eq_nat (Lista.size_list kvsa)
                (Pre_monad.rev_apply cs Pre_monad.max_leaf_size)
              with true ->
                Pre_monad.rev_apply
                  (Pre_monad.rev_apply (Pre_monad.Disk_leaf kvsa) dnode2blka)
                  (fun blk ->
                    Pre_monad.rev_apply (rewritea r blk)
                      (Monad.bind
                        (fun a ->
                          (match a with None -> Monad.return (Sum_Type.Inr ())
                            | Some ra ->
                              Monad.return
                                (Sum_Type.Inl (Pre_monad.I1 ra, stk))))))
              | false ->
                (let (kvs1, (ka, kvs2)) = Pre_monad.split_leaf cs kvsa in
                  Pre_monad.rev_apply
                    (Pre_monad.rev_apply (Pre_monad.Disk_leaf kvs1) dnode2blka)
                    (fun blk ->
                      Pre_monad.rev_apply (write blk)
                        (Monad.bind
                          (fun r1 ->
                            Pre_monad.rev_apply
                              (Pre_monad.rev_apply (Pre_monad.Disk_leaf kvs2)
                                dnode2blka)
                              (fun blka ->
                                Pre_monad.rev_apply (write blka)
                                  (Monad.bind
                                    (fun r2 ->
                                      Monad.return
(Sum_Type.Inl (Pre_monad.I2 (r1, (ka, r2)), stk)))))))))))));;

let rec insert_step
  cs k_cmp blk_ops marshal_ops alloc_ops =
    (let step_downa = step_down cs k_cmp blk_ops marshal_ops alloc_ops in
     let step_bottoma = step_bottom cs k_cmp blk_ops marshal_ops alloc_ops in
     let step_upa = step_up cs k_cmp blk_ops marshal_ops alloc_ops in
     let write = Pre_monad.rev_apply blk_ops wrte in
     let dnode2blka = Pre_monad.rev_apply marshal_ops dnode2blk in
     let _ = Pre_monad.rev_apply alloc_ops alloc in
      (fun s ->
        (match s
          with Pre_monad.I_down d ->
            (let (fs, _) = d in
              (match Pre_monad.dest_F_finished fs
                with None ->
                  Pre_monad.rev_apply (step_downa d)
                    (Monad.fmap (fun a -> Pre_monad.I_down a))
                | Some _ ->
                  Pre_monad.rev_apply (step_bottoma d)
                    (Monad.bind
                      (fun a ->
                        (match a
                          with Sum_Type.Inl u -> Monad.return (Pre_monad.I_up u)
                          | Sum_Type.Inr () ->
                            Monad.return Pre_monad.I_finished_with_mutate)))))
          | Pre_monad.I_up u ->
            (match u
              with (Pre_monad.I1 r, []) -> Monad.return (Pre_monad.I_finished r)
              | (Pre_monad.I2 (r1, (k, r2)), []) ->
                Pre_monad.rev_apply
                  (Pre_monad.rev_apply (Pre_monad.Disk_node ([k], [r1; r2]))
                    dnode2blka)
                  (fun blk ->
                    Pre_monad.rev_apply (write blk)
                      (Monad.bind
                        (fun r -> Monad.return (Pre_monad.I_finished r))))
              | (_, _ :: _) ->
                Pre_monad.rev_apply (step_upa u)
                  (Monad.bind
                    (fun a ->
                      (match a
                        with Sum_Type.Inl ua -> Monad.return (Pre_monad.I_up ua)
                        | Sum_Type.Inr () ->
                          Monad.return Pre_monad.I_finished_with_mutate))))
          | Pre_monad.I_finished _ -> Monad.return s
          | Pre_monad.I_finished_with_mutate -> Monad.return s)));;

end;; (*struct Insert_with_mutation*)
