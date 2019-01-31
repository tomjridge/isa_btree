theory Insert_with_mutation
  imports
"~~/src/HOL/Library/Datatype_Records"
Monad
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

definition kvs_insert :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k*'v) s \<Rightarrow> ('k * 'v) s" where "
kvs_insert k_cmp k v kvs = (
  iter_step (% (kvs,kvs').
    case kvs' of 
    [] \<Rightarrow> None
    | (k',v')#kvs' \<Rightarrow> (
      case key_lt k_cmp k k' of 
      True \<Rightarrow> None
      | False \<Rightarrow> Some((k',v')#kvs,kvs')))
    ([],kvs)
  |> (% (kvs,kvs'). (List.rev ((k,v)#kvs))@kvs'))"


(* ops types -------------------------------------------- *)

datatype ('k,'v,'r) dnode = 
  Disk_node "'k list * 'r list" 
  | Disk_leaf "('k*'v) list"


(* read, write, rewrite; rewrite may CoW to produce a new blk ptr *)
datatype_record ('r,'blk,'t) blk_ops = 
read :: "('r \<Rightarrow> ('blk,'t) MM)"
  wrte:: "('blk \<Rightarrow> ('r,'t) MM)"
  rewrite :: "('r \<Rightarrow> 'blk \<Rightarrow> ('r option,'t) MM)" 
(*
type_synonym ('r,'blk,'t) blk_ops = "(
('r \<Rightarrow> ('blk,'t) MM) * 
('blk \<Rightarrow> ('r,'t) MM) *
('r \<Rightarrow> 'blk \<Rightarrow> ('r option,'t) MM))" 
*)

(* blk \<Rightarrow> dnode ; dnode \<Rightarrow> 'blk;  *)
datatype_record ('blk,'k,'v,'r) marshal_ops = 
blk2dnode :: "'blk \<Rightarrow> ('k,'v,'r) dnode"
dnode2blk :: "('k,'v,'r) dnode \<Rightarrow> 'blk"

(*
type_synonym ('blk,'k,'v,'r) marshal_ops = "(
('blk \<Rightarrow> ('k,'v,'r) dnode) * 
(('k,'v,'r) dnode \<Rightarrow> 'blk))"
*)

(* alloc; free *) 
datatype_record ('r,'t) alloc_ops = 
alloc :: "unit \<Rightarrow> ('r,'t) MM"
free :: "'r s \<Rightarrow> (unit,'t) MM"

(*
type_synonym ('r,'t) alloc_ops = "(
(unit \<Rightarrow> ('r,'t) MM) *
('r s \<Rightarrow> (unit,'t) MM))"
*)



datatype_record constants = 
  min_leaf_size :: nat
  max_leaf_size :: nat
  min_node_keys :: nat
  max_node_keys :: nat



datatype ('a,'b,'c) stk_frame = Frm "'a * 'b * 'c"

fun dest_Frm :: "('a,'b,'c) stk_frame \<Rightarrow> 'a * 'b * 'c" where "
dest_Frm (Frm (a,b,c)) = (a,b,c)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

type_synonym ('k,'r) frame = "( ('r list * 'k list), 'r, ('k list * 'r list)) stk_frame"

type_synonym ('k,'r) stk = "('k,'r) frame list"


(* find ------------------------------- *)


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
definition make_frame :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k s \<Rightarrow> 'r s \<Rightarrow> ('k,'r)frame * 'r" where
"make_frame k_cmp k ks rs = (
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
     (Frm((rs,ks),r',(ks',List.tl rs')),  r')))"



definition find_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow>  
('k,'v,'r) find_state \<Rightarrow> (('k,'v,'r) find_state,'t) MM" where
"find_step cs k_cmp blk_ops marshal_ops alloc_ops = (
  let read = blk_ops|>read in
  let blk2dnode = marshal_ops|>blk2dnode in
  (% fs. 
  case fs of 
  F_finished _ \<Rightarrow> return fs \<comment> \<open> stutter; or fail? \<close>
  | F_down(r0,k,r,stk) \<Rightarrow> (
    read r |>fmap blk2dnode |>fmap (% f. 
    case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let (frm,r) = make_frame k_cmp k ks rs in      
      F_down(r0,k,r,frm#stk))
    | Disk_leaf kvs \<Rightarrow> F_finished(r0,k,r,kvs,stk)))))"




(* insert ------------------------------------------------------------ *)



datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r) d (* down_state *) = "('k,'v,'r)find_state*'v"
type_synonym ('k,'v,'r) u (* up_state *) = "('k,'v,'r)fo*('k,'r)stk"

datatype (dead 'k,dead 'v,dead 'r) insert_state = 
  I_down "('k,'v,'r) d"
  | I_up "('k,'v,'r) u"
  | I_finished 'r
  | I_finished_with_mutate

definition step_down :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down cs k_cmp blk_ops marshal_ops alloc_ops = (
  let find_step =  find_step cs k_cmp blk_ops marshal_ops alloc_ops in
  (% d.
  let (fs,v) = d in
  find_step fs |> fmap (% d'. (d',v)) ))"

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

definition step_bottom :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u + unit,'t) MM" where
"step_bottom cs k_cmp blk_ops marshal_ops alloc_ops d = (
  let (write,rewrite) = (blk_ops|>wrte,blk_ops|>rewrite) in
  let dnode2blk = marshal_ops|>dnode2blk in
  let alloc = alloc_ops|>alloc in
  let (fs,v) = d in
  case dest_F_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    \<comment> \<open> free here? FIXME \<close>
    let kvs' = kvs |> kvs_insert k_cmp k v in
    case length kvs' \<le> (cs|>max_leaf_size) of
    True \<Rightarrow> (
      \<comment> \<open> we want to update in place if possible \<close>
      Disk_leaf kvs' |> dnode2blk |> (% blk. 
      rewrite r blk |> bind (% r'. 
      case r' of 
      None \<Rightarrow> 
        \<comment> \<open> block was updated in place \<close>
        return (Inr ())
      | Some r' \<Rightarrow> return (Inl(I1 r',stk)))))
    | False \<Rightarrow> (
      let (kvs1,k',kvs2) = split_leaf cs kvs' in
      Disk_leaf kvs1 |> dnode2blk |> (% blk.
      write blk |> bind (% r1.
      Disk_leaf kvs2 |> dnode2blk |> (% blk. 
      write blk |> bind (% r2. 
      return (Inl(I2(r1,k',r2),stk)))))))))"

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


definition step_up :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_up  cs k_cmp blk_ops marshal_ops alloc_ops u = (
  let (write,rewrite) = (blk_ops|>wrte,blk_ops|>rewrite) in
  let dnode2blk = marshal_ops|>dnode2blk in
  let alloc = alloc_ops|>alloc in
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible1 (STR ''insert, step_up'') 
  | frm#stk' \<Rightarrow> (
    let ((rs1,ks1),_,(ks2,rs2)) = dest_Frm frm in
    case fo of
    I1 r \<Rightarrow> (
      let (ks,rs) = unsplit_node ((rs1,ks1),([r],[]),(ks2,rs2)) in
      Disk_node(ks,rs) |> dnode2blk |> (% blk.
      write blk |> bind (% r. 
      return (I1 r, stk'))))
    | I2 (r1,k,r2) \<Rightarrow> (
      let (ks',rs') = unsplit_node ((rs1,ks1), ([r1,r2],[k]), (ks2,rs2)) in
      case List.length ks' \<le> (cs|>max_node_keys) of
      True \<Rightarrow> (
        Disk_node(ks',rs') |> dnode2blk |> (% blk.
        write blk |> bind (% r. 
        return (I1 r, stk'))))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node cs (ks',rs') in  
        Disk_node(ks_rs1) |> dnode2blk |> (% blk.
        write blk |> bind (% r1. 
        Disk_node (ks_rs2) |> dnode2blk |> (% blk.
        write blk |> bind (% r2.
        return (I2(r1,k,r2),stk')))) )))))"


definition insert_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) insert_state \<Rightarrow> (('k,'v,'r) insert_state,'t) MM" where
"insert_step cs k_cmp  blk_ops marshal_ops alloc_ops = (
  let step_down = step_down cs k_cmp  blk_ops marshal_ops alloc_ops in
  let step_bottom = step_bottom cs k_cmp  blk_ops marshal_ops alloc_ops in
  let step_up = step_up  cs k_cmp blk_ops marshal_ops alloc_ops in
  let write = blk_ops|>wrte in
  let dnode2blk = marshal_ops|>dnode2blk in
  let alloc = alloc_ops|>alloc in
  (% s.
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case dest_F_finished fs of 
    None \<Rightarrow> (step_down d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom d |> bind (% bot.
      case bot of 
      Inr () \<Rightarrow> return I_finished_with_mutate
      | Inl u \<Rightarrow> return (I_up u)))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 r \<Rightarrow> return (I_finished r)
      | I2(r1,k,r2) \<Rightarrow> (
        (Disk_node([k],[r1,r2]) |> dnode2blk |> (% blk.
        write blk |> bind (% r.
        return (I_finished r))))))
    | _ \<Rightarrow> (step_up u |> fmap (% u. I_up u)))
  | I_finished _ \<Rightarrow> (return s)  \<comment> \<open> stutter \<close> 
  | I_finished_with_mutate \<Rightarrow> (return s)))"


export_code  
"Code_Numeral.int_of_integer"
fmap
Disk_node
make_constants
make_alloc_ops
make_blk_ops
make_marshal_ops
make_initial_find_state
I1
I_down
insert_step

in OCaml file "/tmp/insert_with_mutation.ml"
end