theory A_start_here
imports Main "HOL-Library.RBT_Impl"  "HOL-Library.Datatype_Records" (* ~~/src/HOL/Library/Datatype_Records *)
begin


fun rbt_min' :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option \<Rightarrow> ('a*'b) option" where
"rbt_min' x sofar = (case x of
RBT_Impl.Empty \<Rightarrow> sofar
| Branch c l k v r \<Rightarrow> rbt_min' l (Some(k,v)))"

definition rbt_min :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option" where
"rbt_min x = rbt_min' x None"


fun rbt_max' :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option \<Rightarrow> ('a*'b) option" where
"rbt_max' x sofar = (case x of
RBT_Impl.Empty \<Rightarrow> sofar
| Branch c l k v r \<Rightarrow> rbt_max' r (Some(k,v)))"

definition rbt_max :: "('a,'b) RBT_Impl.rbt \<Rightarrow> ('a*'b) option" where
"rbt_max x = rbt_max' x None"




lemma FIXME: "P" sorry

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"

type_synonym 'a s = "'a list"




(* failwith --------------------------------------------------------- *)

(* occurrences of "FIXME patch" or just "patch" indicate that the defn
should be patched in ocaml *)

(* failwith is for errors that are not expected; such an error should
ideally never arise *)

definition failwith :: "String.literal \<Rightarrow> 'b" where
"failwith x = (STR ''FIXME patch'') |> (% _. undefined)"


(* impossible1 marks cases that are impossible; the 1 suffix is needed
because impossible is reserved (FIXME in OCaml?) *)

definition impossible1 :: "String.literal \<Rightarrow> 'a" where
"impossible1 x = failwith x"  



(* debugging, asserts ----------------------------------------------- *)


(* assert_true always evaluates its argument; this is similar to
assert in OCaml; should be replaced with simple assert in OCaml, which
can then be disabled with a compilation flag for production *)

definition assert_true :: "bool \<Rightarrow> bool" where
"assert_true b = (if b then b else failwith (STR ''assert_true''))"



(* get_check_flag is essentially a mutable reference (exposed as a
function from unit to bool); flag can be set in OCaml to disable
checking within Isabelle (but assert_true is still checked... that can
be disabled by disabling OCaml assertions) *)

definition get_check_flag :: "(unit \<Rightarrow> bool)" where
"get_check_flag _ = failwith (STR ''FIXME patch'')"



(* check_true is patched in OCaml; it should obey check_flag; used
during debugging to check various conditions; should be disabled in
production *)

definition check_true :: "(unit \<Rightarrow> bool) \<Rightarrow> bool" where
"check_true f = (STR ''FIXME patch'') |> (% _. undefined)"



(* a single error type, for all proof-relevant errors --------------- *)


(* errors are for cases that are expected, and which the code should
handle; at the moment they are just strings *)

datatype error = String_error "String.literal"

definition mk_err :: "String.literal \<Rightarrow> error" where
"mk_err s = String_error s"

type_synonym e = error



(* misc aux defns --------------------------------------------------- *)
  

(* is_Some also in Quickcheck_Examples/Completeness.thy - should be in
Main? simpler defn here*)

definition is_Some :: "'a option => bool" where
  "is_Some x = (x ~= None)"

(* FIXME dest_Some None should never happen - so use failwith *)
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


(* This defn avoids equality on 'a *)  
definition is_Nil' :: "'a list \<Rightarrow> bool" where
"is_Nil' x = (case x of [] \<Rightarrow> True | _ \<Rightarrow> False)"

(* NOTE this includes the endpoint *)
definition from_to :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"from_to x y = upt x (Suc y)"

definition from_to_tests :: "bool" where
"from_to_tests = check_true (% _.
  let _ = assert_true (from_to 3 5 = [3,4,5]) in
  let _ = assert_true (from_to 3 3 = [3]) in
  let _ = assert_true (from_to 3 2 = []) in
  True)"


definition max_of_list :: "nat list \<Rightarrow> nat" where
"max_of_list xs = foldr max xs 0"





(* iterate f:'a -> 'a option ---------------------------------------- *)

(* no termination proof for the following; FIXME rename to iter_opt? *)
function iter_step :: "('a => 'a option) => 'a => 'a" where
"iter_step f x = (
  let r = f x in
  case r of
    None => x
  | Some x => iter_step f x)"
apply (force)+ done
termination iter_step
 by (force intro:FIXME)



end
