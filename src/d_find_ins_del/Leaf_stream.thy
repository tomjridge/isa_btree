theory Leaf_stream 
imports Find "$SRC/c_monad/Leaf_stream_state"
begin


definition step_down :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> 'r*('k,'r)rstk \<Rightarrow> (('k,'v,'r)lss,'t) MM" where
"step_down ps1 store_ops rfs = (
  let (r,fs) = rfs in
  (* let store_ops = ps1|>dot_store_ops in *)
  (store_ops|>store_read) r |> fmap 
  (% f. case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let r' = List.hd rs in
      let rs' = List.tl rs in
      let frm = \<lparr> r_ks1=[],r_ts1=[],r_t=r', r_ks2=ks,r_ts2=rs' \<rparr> in
      LS_down (r',frm#fs))  (* r' = f_t of frm *)
    | Disk_leaf (kvs) \<Rightarrow> LS_leaf (kvs,fs))
)"

(* don't have to access disk *)
definition step_leaf :: "('k,'v,'r) leaf_ref \<Rightarrow> ('k,'v,'r) lss" where
"step_leaf r = (
  let (kvs,fs) = r in
  LS_up fs
)"

(* assumes fs <> [] *)
definition step_up :: "('k,'r) rstk \<Rightarrow> ('k,'v,'r) lss" where
"step_up fs = (
  let _ = check_true (%_. fs \<noteq> []) in
  case fs of 
  [] \<Rightarrow> (failwith (STR ''impossible: Leaf_stream.step_up''))
  | f#fs' \<Rightarrow> (
    let (ks1,rs1,r,ks2,rs2) = f|>dest_rsplit_node in
    case rs2 of
    [] \<Rightarrow> (LS_up fs')
    | r'#rs' \<Rightarrow> (
      let f' = \<lparr> 
        (* NOTE r_ks1, r_ts1 stored in reverse *)
        r_ks1=(List.hd ks2)#ks1,
        r_ts1=r#rs1,
        r_t=r', 
        r_ks2=(List.tl ks2),
        r_ts2=rs' \<rparr> 
      in
      LS_down (r',f'#fs') )))"

(* detect when we are finished *)
definition lss_is_finished :: "('k,'v,'r) lss \<Rightarrow> bool" where
"lss_is_finished lss = (
  case lss of
  LS_up [] \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* detect when we are at the next leaf *)
definition dest_LS_leaf :: "('k,'v,'r) lss \<Rightarrow> ('k*'v)s option" where
"dest_LS_leaf x = (
  case x of 
  LS_leaf (kvs,_) \<Rightarrow> Some kvs
  | _ \<Rightarrow> None
)"
  
definition lss_step :: "'k ps1 \<Rightarrow> ('k,'v,'r,'t) store_ops \<Rightarrow> ('k,'v,'r) lss \<Rightarrow> (('k,'v,'r) lss,'t) MM" where
"lss_step ps1 store_ops lss = (
  case lss of 
  LS_down x \<Rightarrow> (step_down ps1 store_ops x)
  | LS_leaf x \<Rightarrow> (return (step_leaf x))
  | LS_up x \<Rightarrow> (return (step_up x)) 
)"

end