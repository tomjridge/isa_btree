theory Util
imports Main
begin


(* FIXME move some of this to prelude *)

lemma FIXME: "P" sorry

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"


(* failwith --------------------------------------------------------- *)

(* patch following in generated ocaml *)


(* failwith is for errors that are not expected; such an error should
never arise *)

definition failwith :: "String.literal \<Rightarrow> 'b" where
"failwith x = (STR ''FIXME patch'') |> (% _. undefined)"


(* impossible1 marks cases that are impossible; the 1 suffix is needed
because impossible is reserved (FIXME in OCaml?) *)

definition impossible1 :: "String.literal \<Rightarrow> 'a" where
  "impossible1 x = failwith x"  



(* debugging, asserts ----------------------------------------------- *)


(* assert_true always evaluates argument; this is useful for debugging
OCaml code; FIXME replaced with simple assert in OCaml? *)

definition assert_true :: "bool \<Rightarrow> bool" where
"assert_true b = (if b then b else failwith (STR ''assert_true''))"


(* check_true is patched in OCaml; may evaluate its argument, but can
be disabled by setting a flag; used during debugging to check various
conditions; should be disabled in production *)

definition check_true :: "(unit \<Rightarrow> bool) \<Rightarrow> bool" where
"check_true f = (STR ''FIXME patch'') |> (% _. undefined)"



(* a single error type, for all proof-relevant errors --------------- *)

(* errors are for cases that are expected, and which the code should
handle; at the moment they are just strings *)

datatype error = String_error "String.literal"

definition mk_err :: "String.literal \<Rightarrow> error" where
"mk_err s = String_error s"

type_synonym e = error



(* misc ------------------------------------------------------------- *)
  

(* is_Some also in Quickcheck_Examples/Completeness.thy - should be in
Main? simpler defn here*)

definition is_Some :: "'a option => bool" where
  "is_Some x = (x ~= None)"


primrec dest_Some (* :: "'a option => 'a" *) where 
  "dest_Some (Some x) = x"
  | "dest_Some None = undefined"


definition is_None :: "'a option \<Rightarrow> bool" where 
"is_None x = (x = None)"



definition dest_list :: "'a list \<Rightarrow> ('a * 'a list)" where
"dest_list xs = (case xs of x#xs \<Rightarrow> (x,xs) | _ \<Rightarrow> failwith (STR ''dest_list''))"

definition dest_list' :: "'a list \<Rightarrow> ('a list * 'a)" where
"dest_list' xs = (case xs of [] \<Rightarrow> failwith (STR ''dest_list' '') | _ \<Rightarrow> (butlast xs,last xs))"


(* FIXME inefficient *)

definition unzip :: "('a*'b) list \<Rightarrow> ('a list * 'b list)" where
"unzip xs = (xs|>List.map fst, xs|>List.map snd)"

  

(* res -------------------------------------------------------------- *)
  
(* This is similar to the result type from OCaml *)

datatype 'a res = Ok 'a | Error e 

definition is_Ok :: "'a res \<Rightarrow> bool" where
"is_Ok x = (case x of Ok _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition dest_Ok :: "'a res \<Rightarrow> 'a" where
"dest_Ok x = (case x of Ok x \<Rightarrow> x | _ \<Rightarrow> failwith (STR ''dest_Ok''))"



(* various list defs, split_at etc ---------------------------------- *)

definition split_at :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a list" where
"split_at n xs = (
  let _ = check_true (% _. n \<le> List.length xs) in
  take n xs,drop n xs)"

definition split_at_tests :: "unit" where
"split_at_tests = (
  let _ = assert_true (split_at 3 [(0::nat),1,2,3,4] = ([0,1,2],[3,4])) in
  let _ = assert_true (split_at 3 [(0::nat),1,2] = ([0,1,2],[])) in
  ())"


definition split_at_3 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a * 'a list" where
"split_at_3 n xs = (
  let _ = check_true (% _. n < List.length xs) in
  (take n xs,xs!n,drop (n+1) xs))"

definition split_at_3_tests :: "unit" where
"split_at_3_tests = (
  let _ = assert_true (split_at_3 3 [(0::nat),1,2,3,4] = ([0,1,2],3,[4])) in
  let _ = assert_true (split_at_3 3 [(0::nat),1,2,3] = ([0,1,2],3,[])) in
  ())"



definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"

definition from_to_tests :: "unit" where
"from_to_tests = (
  let _ = assert_true (from_to 3 5 = [3,4,5]) in
  let _ = assert_true (from_to 3 3 = [3]) in
  let _ = assert_true (from_to 3 2 = []) in
  ())"



definition while_not_nil :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
"while_not_nil f init xs = (List.foldr f xs init)"


definition max_of_list :: "nat list \<Rightarrow> nat" where
"max_of_list xs = foldr max xs 0"


(* iterate f:'a -> 'a option ---------------------------------------- *)

(*no termination proof for the following*)
(*begin iterator*)
function iter_step :: "('a => 'a option) => 'a => 'a" where
"iter_step f x = (
  let r = f x in
  case r of
    None => x
  | Some x => iter_step f x)"
(*end iterator*)
apply (force)+ done
termination iter_step
 by (force intro:FIXME)

  
 
end