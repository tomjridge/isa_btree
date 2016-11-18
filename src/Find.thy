theory Find 
imports Tree_stack Frame (* FIXME for sktoi; move to kv *)
begin

datatype find_error = Find_store_error store_error | Find_step_error
type_synonym fe = find_error

definition se_to_fe :: "se \<Rightarrow> fe" where 
"se_to_fe se = Find_store_error se"

type_synonym stk = "(rs * ks * r * ks * rs) list"

datatype find_state_t = 
  Find_down "k*r*stk" 
  | Find_finished "r*kvs*stk"

type_synonym fs = find_state_t
  
type_synonym 'a fe_M = "('a,fe) M"
 
definition fe_bind :: "('a \<Rightarrow> 'b fe_M) \<Rightarrow> 'a fe_M \<Rightarrow> 'b fe_M" where 
"fe_bind f v = bind f v"

definition page_ref_to_frame :: "r \<Rightarrow> fr fe_M" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r) |> fmap_error se_to_fe"

definition find_step :: "fs \<Rightarrow> fs fe_M" where
"find_step fs = (
  case fs of 
  Find_finished _ \<Rightarrow> (% s. (s,Error Find_step_error))
  | Find_down(k,r,stk) \<Rightarrow> (
    page_ref_to_frame r |>fmap
    (% f. case f of 
      Node_frame (ks,rs) \<Rightarrow> (
        let i = search_key_to_index ks k in
        let (ks1,ks2) = split_at i ks in
        let (rs1,r',rs2) = split_at_3 i rs in
        Find_down(k,r',(rs1,ks1,r',ks2,rs2)#stk)
      )
      | Leaf_frame kvs \<Rightarrow> (Find_finished(r,kvs,stk))))
)"


(* general recursive find ------------------------------------- *)

type_synonym 'a trace = "nat \<Rightarrow> 'a"

function find :: "fs \<Rightarrow> (fs fe_M) trace" where
"find fs n = (
  case n of 0 \<Rightarrow> (find_step fs)
  | Suc n \<Rightarrow> ( (find fs n) |>bind find_step)
)
"    
by auto

(* and prove for code extraction... but we really want the first place (if any) that we get F_finished FIXME express in terms of leaf, and rewrite using "current" state to next state *)

(*
definition find_def_2 :: bool where
"find_def_2 = (! fs n. find fs n = (if n=0 then return (Some fs) else 
  step fs|>bind (% fs'. case fs' of None \<Rightarrow> return None | Some fs' \<Rightarrow> find fs' (n-1))))"
*)


end
