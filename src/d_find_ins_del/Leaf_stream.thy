theory Leaf_stream 
imports Find "$SRC/b_pre_monad/Leaf_stream_state"
begin


definition step_down :: "
'k ord \<Rightarrow> 
('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow>  
('r*('k,'r)stk) \<Rightarrow> (('k,'v,'r)lss,'t) MM" where
"step_down k_cmp store_ops r_fs = (
  let (r,fs) = r_fs in
  (store_ops|>read) r |> fmap 
  (% f. case f of 
    Disk_node (ks,rs) \<Rightarrow> (
      let _ = check_true (% _. ~ (is_Nil' rs)) in
      case rs of 
      r'#rs' \<Rightarrow>
      let frm = Frm (([],[]), r', (ks,rs'), r) in
      LS_down (r',frm#fs)) 
    | Disk_leaf (kvs) \<Rightarrow> LS_leaf (kvs,fs))
)"


(* don't have to access disk *)
definition step_leaf :: "('k,'v,'r) leaf_ref \<Rightarrow> ('k,'v,'r) lss" where
"step_leaf r = (
  let (kvs,fs) = r in
  LS_up fs)"


(* assumes fs <> [] *)
definition step_up :: "('k,'r)stk \<Rightarrow> ('k,'v,'r) lss" where
"step_up fs = (
  let _ = check_true (%_. ~ (is_Nil' fs)) in
  case fs of 
  [] \<Rightarrow> (failwith (STR ''impossible: Leaf_stream.step_up''))
  | f#fs' \<Rightarrow> (
    let (_,_,krs,r) = f|>dest_Frm in
    case krs of
    ([],[]) \<Rightarrow> (LS_up fs')
    | (k1#ks1,r1#rs1) \<Rightarrow> (      
      let f' = Frm( ([],[]), r1, (ks1,rs1), r) in
      LS_down (r1,f'#fs') )))"

  
definition lss_step :: "'k ord \<Rightarrow> ('r,('k,'v,'r)dnode,'t) store_ops \<Rightarrow> 
('k,'v,'r) lss \<Rightarrow> (('k,'v,'r) lss,'t) MM" where
"lss_step k_cmp store_ops lss = (
  case lss of 
  LS_down x \<Rightarrow> (step_down k_cmp store_ops x)
  | LS_leaf x \<Rightarrow> (return (step_leaf x))
  | LS_up x \<Rightarrow> (return (step_up x)))"

end