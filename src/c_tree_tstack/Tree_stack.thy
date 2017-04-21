theory Tree_stack 
imports Tree 
begin

(* some of these defns could be parametric, but polytypes were getting a bit clunky, and the
defns aren't exposed to the user so we don't need polymorphism *)

(* treestack ts_frame ------------------------------- *)
type_synonym rstk = "(k,r) ts_frame list"
  
definition dest_ts_frame :: "('k,'a) ts_frame \<Rightarrow> ('k list * 'a list) * 'a * ('k list * 'a list)" where
"dest_ts_frame f = (
  (f|>f_ks1,f|>f_ts1),
  f|>f_t,
  (f|>f_ks2, f|>f_ts2)
)"

definition ts_frame_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) ts_frame \<Rightarrow> ('k,'b) ts_frame" where
"ts_frame_map g f = (
  \<lparr>
    f_ks1=(f|>f_ks1),
    f_ts1=(f|>f_ts1|>List.map g),
    f_t=(f|>f_t|>g),
    f_ks2=(f|>f_ks2),
    f_ts2=(f|>f_ts2|>List.map g)
  \<rparr>
)"

definition with_t :: "'a \<Rightarrow> ('k,'a) ts_frame \<Rightarrow> ('k,'a) ts_frame" where
"with_t x f = f \<lparr> f_t:=x  \<rparr>"


(* stack types ------------------------------------------------------------------- *)

(* FIXME rename to stack *)
type_synonym ('k,'a) stack' = "('k,'a) ts_frame list"  


type_synonym tstk = "(k,kv_tree) stack'" 

definition stack_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) stack' \<Rightarrow> ('k,'b) stack'" where
"stack_map f stk = (
  stk |> List.map (ts_frame_map f)
)"

(* get bounds --------------------------------------------------- *)

primrec stack_to_lu_of_child :: "('k,'a) stack' \<Rightarrow> 'k option * 'k option" where
"stack_to_lu_of_child [] = (None,None)"
| "stack_to_lu_of_child (x#stk') = (
    let (l',u') = stack_to_lu_of_child stk' in
    let (ks1,ks2) = (x|>f_ks1,x|>f_ks2) in    
    let l = (if ks1 \<noteq> [] then Some(ks1|>List.last) else l') in
    let u = (if ks2 \<noteq> [] then Some(ks2|>List.hd) else u') in
    (l,u)
  )"



(* convert to/from tree from/to tree stack ----------------------------------- *)

(* the n argument ensures the stack has length n; we assume we only call this with n\<le>height t *)
primrec tree_to_stack :: "k \<Rightarrow> kv_tree \<Rightarrow> nat \<Rightarrow> (kv_tree * tstk)" where
"tree_to_stack k t 0 = (t,[])"
| "tree_to_stack k t (Suc n) = (
    let (fo,stk) = tree_to_stack k t n in
    case fo of 
    Leaf kvs \<Rightarrow> (failwith (STR ''tree_to_stack''))
    | Node(ks,ts) \<Rightarrow> (
      let ((ks1,ts1),t',(ks2,ts2)) = split_ks_rs compare_k k (ks,ts) in
      let frm = \<lparr>f_ks1=ks1,f_ts1=ts1,f_t=t',f_ks2=ks2,f_ts2=ts2\<rparr> in
      (t',frm#stk)
    )
  )"

(* we may provide a new focus *)
fun stack_to_tree :: "kv_tree \<Rightarrow> tstk \<Rightarrow> kv_tree" where
"stack_to_tree fo ts = (
  case ts of 
  [] \<Rightarrow> fo
  | x#ts' \<Rightarrow> (
    let (ks1,ts1,_,ks2,ts2) = (x|>f_ks1,x|>f_ts1,(),x|>f_ks2,x|>f_ts2) in
    let fo' = Node(ks1@ks2,ts1@[fo]@ts2) in
    stack_to_tree fo' ts' 
  )
)"

(* remove "focus" *)
definition no_focus :: "('k,'a) stack' \<Rightarrow> ('k,'a option) stack'" where
"no_focus stk = (
  stk |> stack_map Some |> (% stk. 
  case stk of [] \<Rightarrow> [] | frm#stk' \<Rightarrow> (frm\<lparr>f_t:=None \<rparr>)#stk')
)"

(* add new stk ts_frame -------------------------------------------- *)

definition add_new_stack_frame :: 
  "'k ord => 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k,'a) stack' \<Rightarrow> (('k,'a) stack' * 'a)" where
"add_new_stack_frame cmp k ks_rs stk = (
  let (ks,rs) = ks_rs in
  let ((ks1,rs1),r',(ks2,rs2)) = split_ks_rs cmp k (ks,rs) in
  let (l,u) = stack_to_lu_of_child stk in
  let frm' = \<lparr>f_ks1=ks1,f_ts1=rs1,f_t=r', f_ks2=ks2,f_ts2=rs2 \<rparr> in
  (frm'#stk,r')
)"


definition r_stk_to_rs :: "(k,r) ts_frame list \<Rightarrow> r list" where 
"r_stk_to_rs xs = (xs|>List.map f_t)"

end
