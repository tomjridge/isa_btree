theory Tree_stack 
imports Tree 
begin

(* FIXME needs more documentation *)

(* some of these defns could be parametric, but polytypes were getting
a bit clunky, and the defns aren't exposed to the user so we don't
need polymorphism *)



(* node_stack, a stack of frames ------------------------------------ *)

(* FIXME rename to stack; FIXME change to use rsplit_node *)
(* type_synonym ('k,'a) node_stack = "(('k,'a) rsplit_node list)"    *)

type_synonym ('k,'a) rstack = "('k,'a) rsplit_node list"

type_synonym ('k,'r) rstk = "('k,'r) rstack"


(* map a function over the non-'k component *)
definition rstack_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a) rstack \<Rightarrow> ('k,'b) rstack" where
"rstack_map f stk = (
  stk |> List.map (rsplit_node_map f))"

definition rstack_equal :: "('k,'a) rstack \<Rightarrow> ('k,'a) rstack \<Rightarrow> bool" where
"rstack_equal s1 s2 = failwith (STR ''FIXME patch'')"


(* tree_stack ------------------------------------------------------- *)

(* a tree_stack has 'a = ('k,'v)tree *)
type_synonym ('k,'v) tree_rstack = "('k,('k,'v)tree) rstack"



(* stack_to_lu_of_child (get bounds of focus) ----------------------- *)

(* FIXME align this with other splitting/bounds code *)

(* get the bound surrounding the focus, via rsplit_get_bounds *)
primrec rstack_get_bounds :: "('k,'a) rstack \<Rightarrow> 'k option * 'k option" where
"rstack_get_bounds [] = (None,None)"
| "rstack_get_bounds (x#stk') = (
    let (l',u') = rsplit_get_bounds x in
    let (l,u) = (
      case (l',u') of
      (Some l,Some u) \<Rightarrow> (Some l,Some u)
      | _ \<Rightarrow> (
        let (l,u) = rstack_get_bounds stk' in
        ((if l'=None then l else l'), if u'=None then u else u')))
    in
    (l,u))"


(* tree_to_rstack, rstack_to_tree, no_focus ------------------------- *)

(* the n argument ensures the stack has length n; we assume we only call this with n\<le>height t *)
(* FIXME why is focus returned separately? *)
primrec tree_to_rstack :: 
  "'k ord \<Rightarrow> 'k \<Rightarrow> ('k,'v)tree \<Rightarrow> nat \<Rightarrow> (('k,'v)tree * ('k,'v)tree_rstack)" 
where
"tree_to_rstack ord k t 0 = (t,[])"
| "tree_to_rstack ord k t (Suc n) = (
    let (fo,stk) = tree_to_rstack ord k t n in
    case fo of 
    Leaf kvs \<Rightarrow> (failwith (STR ''tree_to_stack''))
    | Node(ks,ts) \<Rightarrow> (
      let frm = mk_rsplit_node ord k (ks,ts) in
      (frm|>r_t,frm#stk)))"

(* when converting a stack to a tree we may provide a new focus *)
(* FIXME have to reveal PRIVATE here *)
fun rstack_to_tree :: "('k,'v)tree \<Rightarrow> ('k,'v)tree_rstack \<Rightarrow> ('k,'v)tree" where
"rstack_to_tree fo ts = (
  case ts of 
  [] \<Rightarrow> fo
  | x#ts' \<Rightarrow> (rstack_to_tree (Node(unsplit_node x)) ts' ))"


(* remove "focus"; NOTE 'a option is always None FIXME so why not use unit? *)
definition no_focus :: "('k,'a) rstack \<Rightarrow> ('k,'a option) rstack" where
"no_focus stk = (
  stk |> rstack_map Some |> (% stk. 
  case stk of [] \<Rightarrow> [] | frm#stk' \<Rightarrow> (frm\<lparr>r_t:=None \<rparr>)#stk'))"



(* add_new_stk_frame; r_stk_to_rs ----------------------------------- *)

definition add_new_stack_frame :: 
  "'k ord => 'k \<Rightarrow> ('k list * 'a list) \<Rightarrow> ('k,'a) rstack \<Rightarrow> (('k,'a) rstack * 'a)" 
where
"add_new_stack_frame cmp k ks_rs stk = (
  let (ks,rs) = ks_rs in
  let r = mk_rsplit_node cmp k (ks,rs) in
  (r#stk,r|>r_t) )"  (* FIXME why return r' explicitly? why not get from f_t? *)


definition r_stk_to_rs :: "('k,'r) rstack \<Rightarrow> 'r list" where 
"r_stk_to_rs xs = (xs|>List.map r_t)"

end