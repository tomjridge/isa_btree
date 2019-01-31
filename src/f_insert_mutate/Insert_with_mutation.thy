theory Insert_with_mutation
  imports
Monad
"~~/src/HOL/Library/Code_Target_Numeral"
begin


(* ops types -------------------------------------------- *)


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




(* find ------------------------------- *)


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