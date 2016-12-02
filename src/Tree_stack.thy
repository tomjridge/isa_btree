theory Tree_stack 
imports Tree 
begin
(* FIXME rename to stack? *)

(* treestack frame ------------------------------- *)

record 'a frame =
  f_ks1 :: "key list"
  f_ts1 :: "'a list"
  f_t :: 'a
  f_ks2 :: "key list"
  f_ts2 :: "'a list"
  
definition dest_frame :: "'a frame \<Rightarrow> (ks * 'a list) * 'a * (ks * 'a list)" where
"dest_frame f = (
  (f|>f_ks1,f|>f_ts1),
  f|>f_t,
  (f|>f_ks2, f|>f_ts2)
)"

definition frame_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a frame \<Rightarrow> 'b frame" where
"frame_map g f = (
  \<lparr>
    f_ks1=(f|>f_ks1),
    f_ts1=(f|>f_ts1|>List.map g),
    f_t=(f|>f_t|>g),
    f_ks2=(f|>f_ks2),
    f_ts2=(f|>f_ts2|>List.map g)
  \<rparr>
)"

definition with_t :: "'a \<Rightarrow> 'a frame \<Rightarrow> 'a frame" where
"with_t x f = f \<lparr> f_t:=x  \<rparr>"


(* stack types ------------------------------------------------------------------- *)

type_synonym 'a stack = "'a frame list"  

type_synonym 'a stk = "'a stack" 


definition stack_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a stk \<Rightarrow> 'b stk" where
"stack_map f stk = (
  stk |> List.map (frame_map f)
)
"

(* get bounds --------------------------------------------------- *)

primrec stack_to_lu_of_child :: "'a stack \<Rightarrow> key option * key option" where
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
primrec tree_to_stack :: "key \<Rightarrow> tree \<Rightarrow> nat \<Rightarrow> (tree * tree stack)" where
"tree_to_stack k t 0 = (t,[])"
| "tree_to_stack k t (Suc n) = (
    let (fo,stk) = tree_to_stack k t n in
    case fo of 
    Leaf kvs \<Rightarrow> (failwith ''tree_to_stack'')
    | Node(ks,ts) \<Rightarrow> (
      let ((ks1,ts1),t',(ks2,ts2)) = split_ks_rs k (ks,ts) in
      let frm = \<lparr>f_ks1=ks1,f_ts1=ts1,f_t=t',f_ks2=ks2,f_ts2=ts2\<rparr> in
      (t',frm#stk)
    )
  )"

(* we may provide a new focus *)
fun stack_to_tree :: "tree \<Rightarrow> tree stack \<Rightarrow> tree" where
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
definition no_focus :: "tree stack \<Rightarrow> tree stack" where
"no_focus stk = (
  case stk of [] \<Rightarrow> [] | frm#stk' \<Rightarrow> (frm\<lparr>f_t:=(Leaf[]) \<rparr>)#stk'
)"

(* add new stk frame -------------------------------------------- *)

definition add_new_stk_frame :: "key \<Rightarrow> (ks * 'a list) \<Rightarrow> 'a stk \<Rightarrow> ('a stk * 'a)" where
"add_new_stk_frame k ks_rs stk = (
  let (ks,rs) = ks_rs in
  let ((ks1,rs1),r',(ks2,rs2)) = split_ks_rs k (ks,rs) in
  let (l,u) = stack_to_lu_of_child stk in
  let frm' = \<lparr>f_ks1=ks1,f_ts1=rs1,f_t=r', f_ks2=ks2,f_ts2=rs2 \<rparr> in
  (frm'#stk,r')
)"






end
