theory Util
imports Main
begin

lemma FIXME: "P" sorry



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

definition FIXME :: "'a" where
"FIXME == undefined"

definition arb :: "'a" where
  "arb == undefined"  

definition impossible :: "'a" where
  "impossible == undefined"  

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

definition split_at :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list * 'a list" where
"split_at xs n == (take n xs,drop n xs)"

definition list_insert_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_insert_at_n xs n as == (
let (ys,zs) = split_at xs n in
ys@as@zs
)"

definition list_replace_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"list_replace_at_n == FIXME"

definition list_replace_1_at_n :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list option" where
"list_replace_1_at_n xs n a == (Some (list_update xs n a))"

end