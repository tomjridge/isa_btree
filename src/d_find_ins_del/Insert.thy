theory Insert imports Find "$SRC/b_pre_monad/Insert_state" begin

(* insert ------------------------------------------------------------ *)


definition step_down :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) d,'t) MM" where
"step_down cs k_cmp store_ops = (
  let find_step =  find_step cs k_cmp store_ops in
  (% d.
  let (fs,v) = d in
  find_step fs |> fmap (% d'. (d',v)) ))"


definition step_bottom :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
('k,'v,'r) d \<Rightarrow> (('k,'v,'r) u + unit,'t) MM" where
"step_bottom cs k_cmp store_ops d = (
  let (write,rewrite) = (store_ops|>wrte,store_ops|>rewrite) in
  let (fs,v) = d in
  case dest_F_finished fs of 
  None \<Rightarrow> impossible1 (STR ''insert, step_bottom'')
  | Some(r0,k,r,kvs,stk) \<Rightarrow> (
    \<comment> \<open> free here? FIXME \<close>
    let kvs' = kvs |> kvs_insert k_cmp k v in
    case length kvs' \<le> (cs|>max_leaf_size) of
    True \<Rightarrow> (
      \<comment> \<open> we want to update in place if possible \<close>
      Disk_leaf kvs' |> rewrite r |> bind (% r'. 
      case r' of 
      None \<Rightarrow> 
        \<comment> \<open> block was updated in place \<close>
        return (Inr ())
      | Some r' \<Rightarrow> return (Inl(I1 r',stk))))
    | False \<Rightarrow> (
      let (kvs1,k',kvs2) = split_leaf cs kvs' in
      Disk_leaf kvs1 |> write |> bind (% r1.
      Disk_leaf kvs2 |> write |> bind (% r2. 
      return (Inl(I2(r1,k',r2),stk)))))))"



definition step_up :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
('k,'v,'r) u \<Rightarrow> (('k,'v,'r) u + unit,'t) MM" where
"step_up  cs k_cmp store_ops u = (
  let (write,rewrite) = (store_ops|>wrte,store_ops|>rewrite) in
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible1 (STR ''insert, step_up'') 
  | frm#stk' \<Rightarrow> (
    let ((rs1,ks1),_,(ks2,rs2),r_parent) = dest_Frm frm in
    case fo of
    I1 r \<Rightarrow> (
      let (ks,rs) = unsplit_node ((rs1,ks1),([r],[]),(ks2,rs2)) in
      Disk_node(ks,rs) |> rewrite r_parent |> bind (% r2. 
      case r2 of 
      None \<Rightarrow> return (Inr ())
      | Some r2 \<Rightarrow> return (Inl (I1 r2, stk'))))
    | I2 (r1,k,r2) \<Rightarrow> (
      let (ks',rs') = unsplit_node ((rs1,ks1), ([r1,r2],[k]), (ks2,rs2)) in
      case List.length ks' \<le> (cs|>max_node_keys) of
      True \<Rightarrow> (
        Disk_node(ks',rs') |> rewrite r_parent |> bind (% r2. 
        case r2 of 
        None \<Rightarrow> return (Inr ())
        | Some r2 \<Rightarrow> return (Inl (I1 r2, stk'))))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node cs (ks',rs') in  
        Disk_node(ks_rs1) |> write |> bind (% r1. 
        Disk_node (ks_rs2) |> write |> bind (% r2.
        return (Inl (I2(r1,k,r2),stk')))) ))))"


definition insert_step :: "
constants \<Rightarrow> 
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>
('k,'v,'r) insert_state \<Rightarrow> (('k,'v,'r) insert_state,'t) MM" where
"insert_step cs k_cmp store_ops = (
  let step_down = step_down cs k_cmp store_ops in
  let step_bottom = step_bottom cs k_cmp store_ops in
  let step_up = step_up  cs k_cmp store_ops in
  let write = store_ops|>wrte in
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
        (Disk_node([k],[r1,r2]) |> write |> bind (% r.
        return (I_finished r)))))
    | _ \<Rightarrow> (step_up u |> bind (% u. 
      case u of 
      Inr () \<Rightarrow> return I_finished_with_mutate
      | Inl u \<Rightarrow> return (I_up u))))
  | I_finished _ \<Rightarrow> (return s)  \<comment> \<open> stutter \<close> 
  | I_finished_with_mutate \<Rightarrow> (return s)))"

end





(*
export_code  
"Code_Numeral.int_of_integer"
fmap
Disk_node
make_constants
make_store_ops
make_initial_find_state
I1
I_down
insert_step

in OCaml file "/tmp/insert_with_mutation.ml"
*)