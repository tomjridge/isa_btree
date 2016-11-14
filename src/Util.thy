theory Util
imports Main
begin

lemma FIXME: "P" sorry

(* various undefinedness constants ----------------------------- *)

definition failwith :: "string \<Rightarrow> 'b" where
"failwith x = undefined"


(*
definition FIXME :: "'a" where
"FIXME == undefined"

definition arb :: "'a" where
  "arb == undefined"  

definition impossible :: "'a" where
  "impossible = failwith ''impossible''"  
*)

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
  
(* for debugging ocaml code; otherwise remove *)
definition assert_true :: "'a \<Rightarrow> bool \<Rightarrow> bool" where
"assert_true arg b = b"


(* rresult -------------------------------------- *)  
  
datatype 'a rresult = Ok 'a | Error 

definition rresult_to_option :: "'a rresult => 'a option" where
  "rresult_to_option x = (case x of Ok x => Some x | Error => None)"

lemma [simp]: "(Error |> rresult_to_option = None) & ((Ok x) |> rresult_to_option = Some x)"
  apply(force simp: rresult_to_option_def rev_apply_def)
  done

definition is_Ok :: "'a rresult \<Rightarrow> bool" where
"is_Ok x == x |> rresult_to_option |> is_Some"

definition dest_Ok :: "'a rresult \<Rightarrow> 'a" where
"dest_Ok x == x |> rresult_to_option |> dest_Some"


(* various list lemmas ---------------------------------- *)

definition split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a list" where
"split_at n xs = (take n xs,drop n xs)"

definition split_at_3 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a * 'a list" where
"split_at_3 n xs = (take n xs,xs!n,drop (n+1) xs)"

(* FIXME remove these in favour of split_at and split_at_3 *)
definition list_insert_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_insert_at_n xs n as == (
let (ys,zs) = split_at n xs in
ys@as@zs
)"

definition list_replace_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"list_replace_at_n xs n as ==
  (if (length xs \<le> n) then None else
  (let (ys,zs) = split_at n xs in
  Some (ys@as@tl zs)))"

(* tests for list_replace_at_n:
value "(dest_Some(list_replace_at_n [0,0,0] 0 [1,2])) = [1,2,0,0]"
value "(dest_Some(list_replace_at_n [0,0,0] 1 [1,2])) = [0,1,2,0]"
value "(dest_Some(list_replace_at_n [0,0,0] 2 [1,2])) = [0,0,1,2]"
value "((list_replace_at_n [0,0,0] 3 [1,2])) = None"
*)

definition list_replace_1_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list option" where
"list_replace_1_at_n xs n a == (Some (list_update xs n a))"

(*begin ordered insert definition*)
(*
definition list_ordered_insert
 :: "('a => bool) => 'a => 'a list => bool => 'a list"
where
"list_ordered_insert is_ord e l is_subst == (
let left = (takeWhile is_ord l) in
let right = dropWhile is_ord l in
let left' = if right = [] then butlast left else left in
let right' = tl right in
if is_subst
then left'@e#right'
else left@e#right)"
*)
(*end ordered insert definition*)




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

end