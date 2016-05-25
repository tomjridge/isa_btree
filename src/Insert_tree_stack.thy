theory Insert_tree_stack
imports Tree_stack
begin

(*begin wfcontext definition*)
definition subtree_indexes :: "node_t => nat set" where
"subtree_indexes n == (
  case n of (l,_) =>  { 0 .. (length l)})"

definition is_subnode :: "(node_t * nat) => (node_t * nat) => bool" where
"is_subnode ni pi == (
  let (n,_) = ni in
  let ((ks,rs),i) = pi in
  Node n = (rs!i))"
                                        
fun linked_context :: "(left_bound * (node_t * nat) * right_bound) => context_t => bool" where
"linked_context ni [] = True" |
"linked_context (lb,ni,rb) ((plb,pi,prb)#pis) = (
  is_subnode ni pi & linked_context (plb,pi,prb) pis)"

definition wellformed_context_1 :: "rmbs_t => (left_bound * (node_t * nat) * right_bound) => bool " where
"wellformed_context_1 rmbs lbnirb == (
let (lb,((l,cs),i),rb) = lbnirb in
let node = (Node(l,cs)) in(
wellformed_tree rmbs node
& i : (subtree_indexes (l,cs)))
& check_keys lb (keys node) rb)"

definition get_lower_upper_keys_for_node_t :: "key list => left_bound => nat => right_bound => (key option * key option)" where
"get_lower_upper_keys_for_node_t ls lb i rb == (
let l = if (i = 0) then lb else Some(ls ! (i - 1))     in
let u = if (i = (length ls)) then rb else Some(ls ! i) in
(l,u)
)"

export_code get_lower_upper_keys_for_node_t in Scala module_name Problem file "/tmp/Problem.scala"

fun wellformed_context :: "context_t => bool" where
"wellformed_context Nil = True" |
"wellformed_context (x # Nil) = wellformed_context_1 (Rmbs True) x" |
"wellformed_context (x1 # (x2 # rest)) = (
let (lb,((ls,_),i),rb) = x2 in
let (l2,u2) = get_lower_upper_keys_for_node_t ls lb i rb in
let (l1,_,u1) = x1 in
wellformed_context_1 (Rmbs False) x1
& (l1,u1) = (l2,u2)
& linked_context x1 (x2#rest)
& wellformed_context (x2#rest)
)
"
(*end wfcontext definition*)

(*begin wffocus definition*)
definition wellformed_focus :: "focus_t => bool => bool" where
"wellformed_focus f stack_empty == (
case f of
Inserting_one t => (wellformed_tree (Rmbs stack_empty) t)
| Inserting_two (tl_,k0,tr) => (
wellformed_tree (Rmbs False) tl_ 
& wellformed_tree (Rmbs False) tr
& check_keys None (keys (tl_)) (Some k0)
& check_keys (Some k0) (keys tr) None)
)"
(*end wffocus definition*)

(*begin wfts1 definition*)
definition wellformed_ts_1 :: "tree_stack => bool" where
"wellformed_ts_1 ts == (
let (f,stk) = dest_ts ts in
(case stk of 

Nil => (True) (* Nil - focus is wf *)

| ((lb,((l,cs),i),rb)#nis) => (
let (kl,kr) = get_lower_upper_keys_for_node_t l lb i rb in
case f of
Inserting_one t => (
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

| Inserting_two (tl_,k0,tr) => (
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
check_keys kl [k0] kr
)
in
let wf = b1&b2&b3&b4&b5 in
wf
)

)


))"
(*end wfts1 definition*)

(*begin wftreestack definition*)
definition wellformed_ts :: "tree_stack => bool" where
"wellformed_ts ts == (
let (f,stk) = dest_ts ts in
wellformed_focus f (stk=[])
& wellformed_context stk
& wellformed_ts_1 ts)"
(*end wftreestack definition*)

end
