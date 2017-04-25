theory Util
imports Main
begin


(* FIXME move soem of this to prelude *)

lemma FIXME: "P" sorry

(* various undefinedness constants ----------------------------- *)


definition failwith :: "String.literal \<Rightarrow> 'b" where
"failwith x = undefined"

definition impossible1 :: "String.literal \<Rightarrow> 'a" where
  "impossible1 x = failwith (STR '''')"  
  
(*
definition FIXME :: "'a" where
"FIXME == undefined"

definition arb :: "'a" where
  "arb == undefined"  


*)

(* a single error type, for all proof-relevant errors ------------------------------------ *)

datatype error = String_error "String.literal"

definition mk_err :: "String.literal \<Rightarrow> error" where
"mk_err s = String_error s"

type_synonym e = error

(* misc ------------------------------------------ *)  
  

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"

(* Quickcheck_Examples/Completeness.thy - should be in Main? simpler defn here*)
definition is_Some :: "'a option => bool" where
  "is_Some x == x ~= None"

primrec dest_Some (* :: "'a option => 'a" *) where 
  "dest_Some (Some x) = x"
  | "dest_Some None = undefined"

definition is_None :: "'a option \<Rightarrow> bool" where 
"is_None x == x = None"
  
(* for debugging ocaml code; otherwise remove; FIXME don't need extra arg *)
definition assert_true :: "'a \<Rightarrow> bool \<Rightarrow> bool" where
"assert_true arg b = b"

definition assert_true' :: "bool \<Rightarrow> bool" where
"assert_true' b = assert_true () b"


(* res -------------------------------------- *)  
  
datatype 'a res = Ok 'a | Error e 

definition is_Ok :: "'a res \<Rightarrow> bool" where
"is_Ok x = (case x of Ok _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition dest_Ok :: "'a res \<Rightarrow> 'a" where
"dest_Ok x = (case x of Ok x \<Rightarrow> x | _ \<Rightarrow> failwith (STR ''dest_Ok''))"



definition dest_list :: "'a list \<Rightarrow> ('a * 'a list)" where
"dest_list xs = (case xs of x#xs \<Rightarrow> (x,xs) | _ \<Rightarrow> failwith (STR ''dest_list''))"

definition dest_list' :: "'a list \<Rightarrow> ('a list * 'a)" where
"dest_list' xs = (case xs of [] \<Rightarrow> failwith (STR ''dest_list' '') | _ \<Rightarrow> (butlast xs,last xs))"


definition unzip :: "('a*'b) list \<Rightarrow> ('a list * 'b list)" where
"unzip xs = (xs|>List.map fst, xs|>List.map snd)"


(* various list lemmas ---------------------------------- *)

definition split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a list" where
"split_at n xs = (take n xs,drop n xs)"

definition split_at_3 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a * 'a list" where
"split_at_3 n xs = (take n xs,xs!n,drop (n+1) xs)"

definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"



(* iteration ---------------------------------------------------- *)


(*no termination proof for the following*)
(*begin iterator*)
function iter_step :: "('a => 'a option) => 'a => 'a" where
"iter_step f x = (
let r = f x in
(case r of
None => x
| Some x => iter_step f x
))"
(*end iterator*)
apply (force)+ done
termination iter_step
 by (force intro:FIXME)

  
definition max_of_list :: "nat list \<Rightarrow> nat" where
  "max_of_list xs == foldr max xs 0"

 
end