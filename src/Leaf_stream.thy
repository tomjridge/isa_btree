theory Leaf_stream 
imports Find
begin

(* working with a F_finished find state, enumerate the leaves *)

type_synonym leaf_ref = "kvs*stk"

datatype ls_state = LS_down "r*stk" | LS_leaf "leaf_ref" | LS_up "stk"
type_synonym lss = ls_state

definition mk_ls_state :: "r \<Rightarrow> ls_state" where
"mk_ls_state r = LS_down (r,[])"

definition step_down :: "r*stk \<Rightarrow> lss SM_t" where
"step_down rfs = (
  let (r,fs) = rfs in
  page_ref_to_frame r |> fmap 
  (% f. case f of 
    Node_frame (ks,rs) \<Rightarrow> (
      let r' = List.hd rs in
      let rs' = List.tl rs in
      let frm = \<lparr> f_ks1=[],f_ts1=[],f_t=r', f_ks2=ks,f_ts2=rs' \<rparr> in
      LS_down (r',frm#fs))  (* r' = f_t of frm *)
    | Leaf_frame (kvs) \<Rightarrow> LS_leaf (kvs,fs))
)"

(* don't have to access disk *)
definition step_leaf :: "leaf_ref \<Rightarrow> lss" where
"step_leaf r = (
  let (kvs,fs) = r in
  LS_up fs
)"

(* assumes fs <> [] *)
definition step_up :: "stk \<Rightarrow> lss" where
"step_up fs = (
  let _ = assert_true () (fs \<noteq> []) in
  case fs of 
  [] \<Rightarrow> (failwith (STR ''impossible: Leaf_stream.step_up''))
  | f#fs' \<Rightarrow> (
    let ((ks1,rs1),r,(ks2,rs2)) = f|>dest_frame in
    case rs2 of
    [] \<Rightarrow> (LS_up fs')
    | r'#rs' \<Rightarrow> (
      let f' = \<lparr> 
        f_ks1=ks1@[List.hd ks2],
        f_ts1=rs1@[r],
        f_t=r', 
        f_ks2=(List.tl ks2),
        f_ts2=rs' \<rparr> 
      in
      LS_down (r',f'#fs')
    )
  )
)"

(* detect when we are finished *)
definition lss_is_finished :: "lss \<Rightarrow> bool" where
"lss_is_finished lss = (
  case lss of
  LS_up [] \<Rightarrow> True
  | _ \<Rightarrow> False)"

(* detect when we are at the next leaf *)
definition dest_LS_leaf :: "lss \<Rightarrow> kvs option" where
"dest_LS_leaf x = (
  case x of 
  LS_leaf (kvs,_) \<Rightarrow> Some kvs
  | _ \<Rightarrow> None
)"
  
definition lss_step :: "lss \<Rightarrow> lss SM_t" where
"lss_step lss = (
  case lss of 
  LS_down x \<Rightarrow> (step_down x)
  | LS_leaf x \<Rightarrow> (return (step_leaf x))
  | LS_up x \<Rightarrow> (return (step_up x)) 
)"

end