theory Insert_tree_stack
imports Tree_stack
begin


definition wellformed_context_1 :: "node_t * nat \<Rightarrow> bool" where
"wellformed_context_1 lcsi = (
let ((l,cs),i) = lcsi in
wellformed_tree (Rmbs False) (Node(l,cs))
& i : { 0 .. (length l) }
)"

definition wellformed_context :: "context_t \<Rightarrow> bool" where
"wellformed_context xs == (
case xs of Nil \<Rightarrow> True
| _ \<Rightarrow> (
let ((l,cs),i) = last xs in
wellformed_tree (Rmbs True) (Node(l,cs))
& i : { 0 .. (length l - 1) }
& List.list_all wellformed_context_1 (butlast xs)
))
"

definition check_keys :: "key option \<Rightarrow> key list \<Rightarrow> key option \<Rightarrow> bool" where
"check_keys kl ks kr == (
let b1 = (
case kl of None \<Rightarrow> True 
| Some kl \<Rightarrow> (! k : set ks. key_le kl k)
)
in
let b2 = (
case kr of None \<Rightarrow> True 
| Some kr \<Rightarrow> (! k : set ks. key_lt k kr)
)
in
b1 & b2
)"

definition wellformed_focus :: "focus_t \<Rightarrow> bool \<Rightarrow> bool" where
"wellformed_focus f stack_empty == (
case f of
Inserting_one t \<Rightarrow> (wellformed_tree (Rmbs stack_empty) t)
| Inserting_two (tl_,k0,tr) \<Rightarrow> (
wellformed_tree (Rmbs False) tl_ 
& wellformed_tree (Rmbs False) tr
& check_keys None (keys(tl_)) (Some k0)
& check_keys (Some k0) (keys(tr)) None
)
)"



definition wellformed_ts_1 :: "tree_stack \<Rightarrow> bool" where
"wellformed_ts_1 ts == (
let (f,stk) = dest_ts ts in
(case stk of 

Nil \<Rightarrow> (True) (* Nil - focus is wf *)

| (((l,cs),i)#nis) \<Rightarrow> (
  let kl = (case i=0 of 
  True \<Rightarrow> None
  | False \<Rightarrow> Some(l!(i-1)))
  in
  let kr = (case i \<le> length l -1 of
  True \<Rightarrow> Some(l!i)
  | False \<Rightarrow> None)
  in
case f of
Inserting_one t \<Rightarrow> (
(* size not checked; we assume focus is wf *)
let b1 = True in
(* ksrs fine *)
let b2 = True in
let b3 = (height (cs!i) = height t) in
let b4 = (check_keys kl (keys t) kr)
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
  (height tl_ = h) & (height tr = h)
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
check_keys kl [k0] kr  (* andrea: error here! proof needs more *)
)
in
let wf = b1&b2&b3&b4&b5 in
wf
)

)


))"

definition wellformed_ts :: "tree_stack \<Rightarrow> bool" where
"wellformed_ts ts == (
let (f,stk) = dest_ts ts in
wellformed_focus f (stk=[])
& wellformed_context stk
& wellformed_ts_1 ts)"


end
