theory Find 
imports Frame Tree_stack (* FIXME for sktoi; move to kv *)
begin

type_synonym find_error = store_error

type_synonym stk = "(page_ref * nat) list"

datatype find_state_t = 
  F_down "key * page_ref * stk" (* fs *)
  | F_finished "page_ref * kvs_t * stk"

type_synonym 'a M = "store \<Rightarrow> (store * ('a,find_error) rresult)"
(* s \<Rightarrow> (s * ['a + e] ) *) 

definition bind :: "('a \<Rightarrow> 'b M) \<Rightarrow> 'a M \<Rightarrow> 'b M" where
"bind f v = (% s. (case v s of (s1,Error x) \<Rightarrow> (s1,Error x) | (s1,Ok y) \<Rightarrow> (f y s1)))"

definition return :: "'a \<Rightarrow> 'a M" where
"return x = (% s. (s,Ok x))"

definition get_store :: "unit \<Rightarrow> store M" where
"get_store _ = (% s. (s,Ok(s)))"

(* FIXME the following should really only require one read from store, not two *)
definition page_ref_to_frame :: "page_ref \<Rightarrow> frame M" where
"page_ref_to_frame r = (
  get_store () |>bind 
  (% s. let f = Frame.page_ref_to_frame s r in 
  case f of Error x \<Rightarrow> (% s1. (s1,Error x)) | Ok y \<Rightarrow> (% s1. (s1,Ok y)))
)"

definition step :: "find_state_t \<Rightarrow> find_state_t option M" where
"step fs = (
  case fs of 
  F_finished _ \<Rightarrow> (return None)
  | F_down(k,r,stk) \<Rightarrow> (
    page_ref_to_frame r |>bind
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let i = search_key_to_index ks k in
        let r' = rs!i in
        return(Some(F_down(k,r',(r,i)#stk)))
      )
      | Leaf_frame kvs \<Rightarrow> (return(Some(F_finished(r,kvs,stk))))
)))"

(* general recursive find *)
type_synonym 'a trace = "nat \<Rightarrow> 'a"
function find :: "find_state_t \<Rightarrow> (find_state_t option M) trace" where
"find fs n = (
  case n of 0 \<Rightarrow> (step fs)
  | Suc n \<Rightarrow> (
    (find fs n) |>bind
    (% fs. case fs of
    None \<Rightarrow> return None
    | Some fs \<Rightarrow> (step fs)    
)))
"    
by auto

(* and prove for code extraction... but we really want the first place (if any) that we get F_finished FIXME express in terms of leaf, and rewrite using "current" state to next state *)

definition find_def_2 :: bool where
"find_def_2 = (! fs n. find fs n = (if n=0 then return (Some fs) else 
  step fs|>bind (% fs'. case fs' of None \<Rightarrow> return None | Some fs' \<Rightarrow> find fs' (n-1))))"

end
