theory Pre_monad_mutate 
  imports Util 
"~~/src/HOL/Library/Datatype_Records"
begin

lemma FIXME: "P" sorry

(*no termination proof for the following*)
(*begin iterator*)
function iter_step :: "('a => 'a option) => 'a => 'a" where
"iter_step f x = (
  let r = f x in
  case r of
    None => x
  | Some x => iter_step f x)"
(*end iterator*)
apply (force)+ done
termination iter_step
 by (force intro:FIXME)

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"

definition failwith :: "String.literal \<Rightarrow> 'b" where
"failwith x = (STR ''FIXME patch'') |> (% _. undefined)"


(* impossible1 marks cases that are impossible; the 1 suffix is needed
because impossible is reserved (FIXME in OCaml?) *)

definition impossible1 :: "String.literal \<Rightarrow> 'a" where
  "impossible1 x = failwith x"  


(* assert_true always evaluates argument; this is useful for debugging
OCaml code; FIXME replaced with simple assert in OCaml? *)

definition assert_true :: "bool \<Rightarrow> bool" where
"assert_true b = (if b then b else failwith (STR ''assert_true''))"


(* check_true is patched in OCaml; may evaluate its argument, but can
be disabled by setting a flag; used during debugging to check various
conditions; should be disabled in production *)

definition check_true :: "(unit \<Rightarrow> bool) \<Rightarrow> bool" where
"check_true f = (STR ''FIXME patch'') |> (% _. undefined)"

type_synonym 'k ord = "'k \<Rightarrow> 'k \<Rightarrow> int"

type_synonym 'a s = "'a list"


definition key_lt :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_lt ord k1 k2 = ( ord k1 k2 < 0)"

definition key_eq ::  "'k ord \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
"key_eq ord k1 k2 = ( ord k1 k2 = 0)"

definition kvs_insert :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k*'v) s \<Rightarrow> ('k * 'v) s" where "
kvs_insert k_cmp k v kvs = (
  iter_step (% (kvs,kvs').
    case kvs' of 
    [] \<Rightarrow> None
    | (k',v')#kvs' \<Rightarrow> (
      case key_lt k_cmp k k' of 
      True \<Rightarrow> None
      | False \<Rightarrow> (
        case key_eq k_cmp k k' of 
        True \<Rightarrow> Some(kvs,kvs') 
        | False \<Rightarrow> (Some((k',v')#kvs,kvs')))))
    ([],kvs)
  |> (% (kvs,kvs'). (List.rev ((k,v)#kvs))@kvs'))"

datatype ('k,'v,'r) dnode = 
  Disk_node "'k list * 'r list" 
  | Disk_leaf "('k*'v) list"

datatype_record constants = 
  min_leaf_size :: nat
  max_leaf_size :: nat
  min_node_keys :: nat
  max_node_keys :: nat


(* NOTE the 4th component is the parent root *)
datatype ('a,'b,'c,'d) stk_frame = Frm "'a * 'b * 'c * 'd"

fun dest_Frm :: "('a,'b,'c,'d) stk_frame \<Rightarrow> 'a * 'b * 'c * 'd" where "
dest_Frm (Frm (a,b,c,d)) = (a,b,c,d)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

type_synonym ('k,'r) frame = "( ('r list * 'k list), 'r, ('k list * 'r list), 'r) stk_frame"

type_synonym ('k,'r) stk = "('k,'r) frame list"


datatype ('k,'v,'r) find_state = 
  F_down "'r * 'k * 'r * ('k,'r) stk"  (* root, search key, current pointer, stack *) 
  | F_finished "'r * 'k * 'r * ('k*'v)s * ('k,'r)stk"

definition dest_F_finished :: "('k,'v,'r)find_state \<Rightarrow> ('r*'k*'r*('k*'v) s * ('k,'r)  stk) option" where
"dest_F_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk) )"

definition make_initial_find_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r) find_state" where "
make_initial_find_state k r = F_down (r,k,r,[])"

(* walk through ks and rs to find the point where ki \<le> k < k(i+1); |ks|+1=|rs|;
or: find first point where k < ki
 *)
definition make_frame :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'r \<Rightarrow> 'k s \<Rightarrow> 'r s \<Rightarrow> ('k,'r)frame * 'r" where
"make_frame k_cmp k r_parent ks rs = (
  iter_step (% ((rs,ks),(ks',rs')).
    case ks' of 
    [] \<Rightarrow> None
    | k'#ks' \<Rightarrow> (
      case key_lt k_cmp k k' of 
      True \<Rightarrow> None
      | False \<Rightarrow> 
        let (r',rs') = (List.hd rs', List.tl rs') in
        Some ( (r'#rs,k'#ks),(ks',rs'))))
    ( ([],[]),(ks,rs))
  |> (% ((rs,ks),(ks',rs')).
     let r' = List.hd rs' in
     (Frm((rs,ks),r',(ks',List.tl rs'),r_parent),  r')))"



datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r) d (* down_state *) = "('k,'v,'r)find_state*'v"
type_synonym ('k,'v,'r) u (* up_state *) = "('k,'v,'r)fo*('k,'r)stk"

datatype (dead 'k,dead 'v,dead 'r) insert_state = 
  I_down "('k,'v,'r) d"
  | I_up "('k,'v,'r) u"
  | I_finished 'r
  | I_finished_with_mutate

definition split_leaf :: "constants \<Rightarrow> ('k*'v) s \<Rightarrow> ('k*'v)s * 'k * ('k*'v) s" where "
split_leaf cs kvs = (
  let _ = assert_true True in
  iter_step (% (kvs,kvs').
    case List.length kvs' \<le> cs|>min_leaf_size of
    True \<Rightarrow> None
    | False \<Rightarrow> (
      case kvs' of 
      [] \<Rightarrow> impossible1 (STR ''split_leaf'')
      | (k,v)#kvs' \<Rightarrow> Some((k,v)#kvs,kvs')))
    ([],kvs)
  |> (% (kvs,kvs'). (List.rev kvs,List.hd kvs'|>fst, kvs')))
"

(* convert a rsplit_node to a disk node; rks has one more r than k *)
definition unsplit_node :: "('r s * 'k s) * ('r s * 'k s) * ('k s * 'r s) \<Rightarrow> ('k s * 'r s)" where
"unsplit_node x = (
  let ((rs1,ks1),(rs2,ks2),(ks3,rs3)) = x in
  ( (List.rev ks1)@ks2@ks3, (List.rev rs1)@rs2@rs3) )"

(* NOTE for both split_node and split_leaf, we may know the order is dense, and all keys have values; in which case we can split
with a full left leaf/node *)
definition split_node :: 
  "constants \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k list * 'a list) * 'k * ('k list * 'a list)" 
where
"split_node cs n = (
  let (ks,rs) = n in
  let l = List.length ks  div 2 in
  let l = max (cs|>min_node_keys) l in
  iter_step (% (ks,rs,ks',rs').
    case (ks',rs') of 
    (k'#ks',r'#rs') \<Rightarrow> (
      case List.length ks < l of
      True \<Rightarrow> Some(k'#ks,r'#rs,ks',rs')
      | False \<Rightarrow> None)
    | _ \<Rightarrow> (impossible1 (STR ''split_node'')))
    ([],[],ks,rs)
  |> (% (ks,rs,ks',rs').
    case (ks',rs') of
    (k'#ks',r'#rs') \<Rightarrow> (
      (List.rev ks,List.rev(r'#rs)),
      k',
      (ks',rs'))))"


end