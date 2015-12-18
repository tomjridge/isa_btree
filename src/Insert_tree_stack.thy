theory Insert_tree_stack
imports Tree_stack
begin

definition wellformed_context :: "context_t \<Rightarrow> bool" where
"wellformed_context xs == (
case xs of Nil \<Rightarrow> True
| (((l,cs),i)#xs) \<Rightarrow> (
wellformed_tree (Node(l,cs))
& List.list_all (% n. wellformed_subtree (Node(l,cs))) xs 
& i : { 0 .. (length l) }
)
)"

definition wellformed_focus :: "focus_t \<Rightarrow> bool" where
"wellformed_focus f == (
case f of
Inserting_one t \<Rightarrow> (wellformed_subtree t)
| Inserting_two (tl_,k0,tr) \<Rightarrow> (
wellformed_subtree tl_ 
& wellformed_subtree tl_
& List.list_all (% k. key_lt k k0) (keys(tl_))
& List.list_all (% k. key_le k0 k) (keys(tr))
)
)"

definition check_keys :: "key option \<Rightarrow> key list \<Rightarrow> key option \<Rightarrow> bool" where
"check_keys kl ks kr == (
let b1 = (
case kl of None \<Rightarrow> True 
| Some k0 \<Rightarrow> (! k : set ks. key_le k0 k)
)
in
let b2 = (
case kr of None \<Rightarrow> True 
| Some k0 \<Rightarrow> (! k : set ks. key_lt k k0)
)
in
b1 & b2
)"

definition wellformed_ts :: "tree_stack \<Rightarrow> bool" where
"wellformed_ts ts == (
let (f,stk) = dest_ts ts in
case stk of 

Nil \<Rightarrow> (
case f of 
Inserting_one t \<Rightarrow> (wellformed_tree t)
| Inserting_two (tl_,k0,tr) \<Rightarrow> (
wellformed_subtree tl_
& wellformed_subtree tr
& check_keys None (keys tl_) (Some k0) 
& check_keys (Some k0) (keys tr) None
)) (* Nil *)

| (((l,cs),i)#nis) \<Rightarrow> (
  let kl = (case i=0 of 
  True \<Rightarrow> None
  | False \<Rightarrow> Some(l!(i-1)))
  in
  let kr = (case i=length l of
  True \<Rightarrow> None
  | False \<Rightarrow> Some(l!i))
  in
case f of
Inserting_one t \<Rightarrow> (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 = (height (cs!i) = height t) in
let b4 = (
  check_keys kl (keys t) kr
)
in
(* keys ordered *)
let b5 = True in
let wf = b1&b2&b3&b4&b5 in
wf
)  (* Inserting_one *)

| Inserting_two (tl_,k0,tr) \<Rightarrow> (
let b1 = True in
let b2 = True in
let b3 = (
  let h = height (cs!i) in
  (height tl_ = h)
  & (height tr = h)
)
in
(* keys consistent *)
let b4 = (
  check_keys kl (keys tl_) (Some k0)
  & check_keys (Some k0) (keys tr) kr
)
in
(* keys ordered *)
let b5 = (
check_keys kl [k0] kr
)
in
let wf = b1&b2&b3&b4&b5 in
wf
)

)


)"


end