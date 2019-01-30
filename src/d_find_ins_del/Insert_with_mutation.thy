theory Insert_with_mutation
imports Find "$SRC/c_monad/Insert_state"
begin

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


(* read, write, rewrite; rewrite may CoW to produce a new blk ptr *)
type_synonym ('r,'blk,'t) blk_ops = "(
('r \<Rightarrow> ('blk,'t) MM) * 
('blk \<Rightarrow> ('r,'t) MM) *
('r \<Rightarrow> 'blk \<Rightarrow> ('r option,'t) MM))" 


(* blk \<Rightarrow> dnode ; dnode \<Rightarrow> 'blk;  *)
type_synonym ('blk,'k,'v,'r) marshal_ops = "(
('blk \<Rightarrow> ('k,'v,'r) dnode) * 
(('k,'v,'r) dnode \<Rightarrow> 'blk))"

(* alloc; free *) 
type_synonym ('r,'t) alloc_ops = "(
(unit \<Rightarrow> ('r,'t) MM) *
('r s \<Rightarrow> (unit,'t) MM))"


datatype ('a,'b,'c) stk_frame = Frm "'a * 'b * 'c"

fun dest_Frm :: "('a,'b,'c) stk_frame \<Rightarrow> 'a * 'b * 'c" where "
dest_Frm (Frm (a,b,c)) = (a,b,c)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

type_synonym ('k,'r) frame = "( ('r list * 'k list), 'r, ('k list * 'r list)) stk_frame"

type_synonym ('k,'r) stk = "('k,'r) frame list"


datatype ('k,'v,'r) find_state = 
  F_down "'r * 'k * 'r * ('k,'r) stk"  (* root, search key, current pointer, stack *) 
  | F_finished "'r * 'k * 'r * ('k*'v)s * ('k,'r)stk"

definition dest_F_finished :: "('k,'v,'r)find_state \<Rightarrow> ('r*'k*'r*('k*'v) s * ('k,'r)  stk) option" where
"dest_F_finished fs = (
  case fs of
  F_down _ \<Rightarrow> None
  | F_finished (r0,k,r,kvs,stk) \<Rightarrow> Some(r0,k,r,kvs,stk) )"

(* walk through ks and rs to find the point where ki \<le> k < k(i+1); |ks|+1=|rs|;
or: find first point where k < ki
 *)
definition find_split_node :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'k s \<Rightarrow> 'r s \<Rightarrow> ('k,'r)frame * 'r" where
"find_split_node k_cmp k ks rs = (
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


(* Some(Frm((ks,rs),List.hd rs',([],[]))) *)

(* find ------------------------------- *)

definition find_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow>  
('k,'v,'r) find_state \<Rightarrow> (('k,'v,'r) find_state,'t) MM" where
"find_step cs k_cmp blk_ops marshal_ops alloc_ops fs = (
  let (read,write,rewrite) = blk_ops in
  let (blk2frm,_) = marshal_ops in
  case fs of 
  F_finished _ \<Rightarrow> return fs \<comment> \<open> stutter; or fail? \<close>
  | F_down(r0,k,r,stk) \<Rightarrow> (
    read r |>fmap blk2frm |>fmap (% f. 
    case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let (frm,r) = find_split_node k_cmp k ks rs in      
      F_down(r0,k,r,frm#stk))
    | Disk_leaf kvs \<Rightarrow> F_finished(r0,k,r,kvs,stk))))"




(* insert ------------------------------------------------------------ *)



datatype ('k,'v,'r) i12_t = I1 'r | I2 "'r*'k*'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r)i12_t"

type_synonym ('k,'v,'r) d (* down_state *) = "('k,'v,'r)find_state*'v"
type_synonym ('k,'v,'r) u (* up_state *) = "('k,'v,'r)fo*('k,'r)stk"

datatype (dead 'k,dead 'v,dead 'r) insert_state = 
  I_down "('k,'v,'r) d"
  | I_up "('k,'v,'r) u"
  | I_finished 'r

definition step_down :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down cs k_cmp blk_ops marshal_ops alloc_ops d = (
  let (fs,v) = d in
  find_step cs k_cmp blk_ops marshal_ops alloc_ops fs |> fmap (% d'. (d',v)) )"

definition step_bottom :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u + unit,'t) MM" where
"step_bottom cs k_cmp blk_ops marshal_ops alloc_ops d = (
  let (read,write,rewrite) = blk_ops in
  let (_,dnode2blk) = marshal_ops in
  let (alloc,free) = alloc_ops in
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

definition step_up :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,'blk,'t) blk_ops \<Rightarrow>
('blk,'k,'v,'r) marshal_ops \<Rightarrow> 
('r,'t) alloc_ops \<Rightarrow> 
('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u,'t) MM" where
"step_up  cs k_cmp blk_ops marshal_ops alloc_ops u = (
  let (read,write,rewrite) = blk_ops in
  let (_,dnode2blk) = marshal_ops in
  let (alloc,free) = alloc_ops in
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

(*
definition insert_step :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) ist \<Rightarrow> (('k,'v,'r) ist,'t) MM" where
"insert_step ps1 store_ops s = (
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case (dest_f_finished fs) of 
    None \<Rightarrow> (step_down ps1 store_ops d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom ps1 store_ops d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> (
      case fo of 
      I1 r \<Rightarrow> return (I_finished r)
      | I2(r1,k,r2) \<Rightarrow> (
        (mk_Disk_node([k],[r1,r2]) |> (store_ops|>store_alloc) |> fmap (% r. I_finished r))))
    | _ \<Rightarrow> (step_up ps1 store_ops u |> fmap (% u. I_up u)))
  | I_finished f \<Rightarrow> (return s)  \<comment> \<open> stutter \<close> )"
*)


end