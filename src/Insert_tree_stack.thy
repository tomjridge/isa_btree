(* [[file:~/workspace/agenda/myTasks.org::*=ts_to_map=][=ts_to_map=:1]] *)
theory Insert_tree_stack
imports Find_tree_stack "~~/src/HOL/Library/Code_Target_Nat"
begin

(*begin ins focus definition*)
datatype its_focus_t = 
Inserting_one "Tree"
| Inserting_two "Tree * key * Tree"
(*end ins focus definition*)

type_synonym inserting_two_t =  "Tree * key * Tree"

(*begin its_tree_stack definition*)
type_synonym its_tree_stack = "its_focus_t tree_stack"
(*end its_tree_stack definition*)

(*begin step its_state definition *)
datatype its_state =
Its_down "(f_tree_stack * value_t)"
| Its_up "its_tree_stack"
(*end step its_state definition *)

definition its_f_to_map
 :: "its_focus_t => (key,value_t) map"
where
"its_f_to_map f = (
(case f of
(*note that the focus map must be after the ++ in order to consider the new entry in case of an update*)
Inserting_one t => (tree_to_map t)
| Inserting_two (tl_,_,tr_) => (tree_to_map tl_)++(tree_to_map tr_) )
)"

(*begin split node definition *)
definition split_node :: "node_t => inserting_two_t" where
"split_node n == (
let (l,cs) = n in
let n0 = min_node_keys in
let left_ks = take n0 l in
let (k,right_ks) = (case drop n0 l of (k#ks) => (k,ks)) in
let left_rs = take (1+n0) cs in
let right_rs = drop (1+n0) cs in
(Node(left_ks,left_rs),k,Node(right_ks,right_rs))
)"
(*end split node definition *)

(* tr: want to split a too-large leaf *)
(*begin split leaf definition*)
definition split_leaf_kvs
 :: "(key * value_t) list => ((key * value_t) list * key * (key * value_t) list)"
where
"split_leaf_kvs kvs == (
let n0 = min_leaf_size in
let left = take n0 kvs in
let right = drop n0 kvs in
let k = fst( hd right) in
(left,k,right)
)"
(*end split leaf definition*)

(*begin step up definition*)
definition update_focus_at_position
 :: "node_t => nat => its_focus_t => its_focus_t"
where
"update_focus_at_position n i f == (
let (ks,rs) = n in
case f of
Inserting_one t => (
let rs2 = dest_Some(list_replace_1_at_n rs i t) in
Inserting_one(Node(ks,rs2)))
| Inserting_two (tl_,k,tr) => (
let ks2 = list_insert_at_n ks i [k] in
let rs2 = list_replace_at_n rs i [tl_,tr] |> dest_Some in
case (length ks2 <= max_node_keys) of
True => Inserting_one(Node(ks2,rs2))
| False => (
Inserting_two(split_node(ks2,rs2))
)
)
)"

definition its_to_map1 
 :: "its_tree_stack => (key,value_t) map"
where
"its_to_map1 ts = (
let (f,ctx) = dest_ts ts in
ctx_to_map ctx ++
(case f of
Inserting_one t => tree_to_map t
| Inserting_two (t1,_,t2) => tree_to_map t1 ++ tree_to_map t2)
)"

function its_to_tree
 :: "its_tree_stack => Tree"
where
"its_to_tree (Tree_stack(Focus f, [])) = (
case f of
Inserting_one t => t
| Inserting_two (tl_,k,tr_) => Node([k],[tl_,tr_])
)" |
"its_to_tree (Tree_stack(Focus f, (_,((ks,rs),i),_)#t)) = (
its_to_tree (Tree_stack((Focus (update_focus_at_position (ks,rs) i f)),t))
)"
by pat_completeness auto
termination its_to_tree
apply (relation "measure (\<lambda>ts. case ts of (Tree_stack(Focus _,ctx)) => length ctx)")
apply auto
done

definition its_to_map
 :: "its_tree_stack => (key,value_t) map"
where
"its_to_map its = (
its |> its_to_tree |> tree_to_map
)"


definition step_up
 :: "its_tree_stack => (its_tree_stack) option"
where
"step_up ts == (
let (f,stk) = dest_ts ts in
case stk of 
Nil => None
| ((lb,(n,i),rb)#xs) => (
let f2 = update_focus_at_position n i f in
Some(Tree_stack((Focus f2),xs))
)
)
"
(*end step up definition*)

(*// we have located the right node
              // switch to up phase
              //
              // at the end of the down phase, we have a context, and
              // a leaf frame (and a k,v)
              //
              // then we need to move to the up phase; but what state
              // to initialize with? in Insert.scala, there is similar
              // code in step across and step up; this is because we
              // need to distinguish whether the updated leaf is too
              // big or not; would be nice to combine these cases, but
              // this seems somewhat difficult*)
(*begin step bottom definition*)
definition step_bottom
 :: "f_tree_stack => value_t => (its_tree_stack) option"
where
"step_bottom fts v0 == (
let (k0,lf,stk) = dest_f_tree_stack fts in
(case lf of
Leaf kvs =>
(*tr:need to check whether the leaf is small enough to insert directly*)
let entry_in_kvs =
 (List.find (%x. key_eq k0 (fst x)) kvs) ~= None
in
let cond =
 (entry_in_kvs | length kvs < max_leaf_size )
in
if (cond) then
let kvs2 =
 list_ordered_insert (%x. key_lt (fst x) k0) (k0,v0) kvs entry_in_kvs
in
let focus = (Inserting_one(Leaf kvs2)) in
Some(Tree_stack(Focus focus,stk))
else
(*tr:we need to split*)
let kvs2 =
 list_ordered_insert (%x. key_lt (fst x) k0) (k0,v0) kvs entry_in_kvs
in 
let (left,k,right) = split_leaf_kvs kvs2 in
let focus = Inserting_two(Leaf left, k,Leaf right)in
Some(Tree_stack(Focus focus,stk))
| _ => None (* impossible: find returns leaf *))
)
"
(*end step bottom definition*)

(*begin insert step *)
definition its_step_tree_stack
 :: "its_state => (its_state) option"
where
"its_step_tree_stack ist == (
case ist of
Its_down (fts,v0) =>
let fts1 = step_fts fts in
(case fts1 of
None => Option.bind (step_bottom fts v0) (% x . Some (Its_up x))
| Some x => Some(Its_down(x,v0)))
| Its_up ts => Option.bind (step_up ts) (% x . Some (Its_up x)))
"
(*end insert step*)

declare [[code abort: key_lt min_node_keys max_node_keys min_leaf_size max_leaf_size]]
export_code its_step_tree_stack in Scala module_name Insert_tree_stack file "/tmp/Insert_tree_stack.scala"

(*begin wffocus definition*)
definition wellformed_focus :: "its_focus_t => bool => bool" where
"wellformed_focus f stack_empty == (
case f of
Inserting_one t =>
let ms = case stack_empty of 
 True => (Some Small_root_node_or_leaf)
 | _ => None
in
(wellformed_tree ms t)
| Inserting_two (tl_,k0,tr) => (
wellformed_tree None tl_ 
& wellformed_tree None tr
& check_keys None (keys (tl_)) (Some k0)
& check_keys (Some k0) (keys tr) None)
)"
(*end wffocus definition*)

(*begin wfts1 definition*)
definition wellformed_ts_1 :: "its_tree_stack => bool" where
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
definition wellformed_ts :: "its_tree_stack => bool" where
"wellformed_ts ts == (
let (f,stk) = dest_ts ts in
wellformed_focus f (stk=[])
& wellformed_context stk
& wellformed_ts_1 ts)"
(*end wftreestack definition*)

end
(* =ts_to_map=:1 ends here *)
