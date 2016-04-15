theory Insert_tree_stack
imports Tree_stack
begin

definition subtree_indexes :: "node_t \<Rightarrow> nat set" where
"subtree_indexes n == (
  case n of (l,_) \<Rightarrow>  { 0 .. (length l)})"

definition is_subnode :: "(node_t * nat) \<Rightarrow> (node_t * nat) \<Rightarrow> bool" where
"is_subnode ni pi == (
  let (n,_) = ni in
  let ((ks,rs),i) = pi in
  Node n = (rs!i))"
                                        
fun linked_context :: "(left_bound * (node_t * nat) * right_bound) \<Rightarrow> context_t \<Rightarrow> bool" where
"linked_context ni [] = True" |
"linked_context (lb,ni,rb) ((plb,pi,prb)#pis) = (
  is_subnode ni pi \<and> linked_context (plb,pi,prb) pis)"

definition wellformed_context_1 :: "rmbs_t \<Rightarrow> (left_bound * (node_t * nat) * right_bound) \<Rightarrow> bool " where
"wellformed_context_1 rmbs lbnirb == (
let (lb,((l,cs),i),rb) = lbnirb in
let node = (Node(l,cs)) in(
wellformed_tree rmbs node
& i : (subtree_indexes (l,cs)))
& check_keys lb (keys node) rb)"

definition get_lower_upper_keys_for_node_t :: "(left_bound * (node_t * nat) * right_bound) \<Rightarrow> (key option * key option)" where
"get_lower_upper_keys_for_node_t ni == (
let (lb,((ls,_),i),rb) = ni in (
let l = if (i = 0) then lb else Some(ls ! (i - 1))     in
let u = if (i = (length ls)) then rb else Some(ls ! i) in
(l,u)
))"

fun wellformed_context :: "context_t \<Rightarrow> bool" where
"wellformed_context Nil = True" |
"wellformed_context (x # Nil) = wellformed_context_1 (Rmbs True) x" |
"wellformed_context (x1 # (x2 # rest)) = (
let (l2,u2) = get_lower_upper_keys_for_node_t x2 in
let (l1,_,u1) = x1 in
wellformed_context_1 (Rmbs False) x1
& (l1,u1) = (l2,u2)
& linked_context x1 (x2#rest)
& wellformed_context (x2#rest)
)
"

definition wellformed_focus :: "focus_t \<Rightarrow> bool \<Rightarrow> bool" where
"wellformed_focus f stack_empty == (
case f of
Inserting_one t \<Rightarrow> (wellformed_tree (Rmbs stack_empty) t)
| Inserting_two (tl_,k0,tr) \<Rightarrow> (
wellformed_tree (Rmbs False) tl_ 
& wellformed_tree (Rmbs False) tr
& check_keys None (keys (tl_)) (Some k0)
& check_keys (Some k0) (keys tr) None)
)"



definition wellformed_ts_1 :: "tree_stack \<Rightarrow> bool" where
"wellformed_ts_1 ts == (
let (f,stk) = dest_ts ts in
(case stk of 

Nil \<Rightarrow> (True) (* Nil - focus is wf *)

| ((lb,((l,cs),i),rb)#nis) \<Rightarrow> (
let (kl,kr) = get_lower_upper_keys_for_node_t (lb,((l,cs),i),rb) in
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
