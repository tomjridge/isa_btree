(* old res -------------------------------------------------------------- *)
  
(* This is similar to the result type from OCaml *)

(*
datatype 'a res = Ok 'a | Error e 

definition is_Ok :: "'a res \<Rightarrow> bool" where
"is_Ok x = (case x of Ok _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition dest_Ok :: "'a res \<Rightarrow> 'a" where
"dest_Ok x = (case x of Ok x \<Rightarrow> x | _ \<Rightarrow> failwith (STR ''dest_Ok''))"
*)


(* split_at etc ---------------------------------- *)

(* FIXME take and drop used separately is inefficient *)
(*
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

*)


(*
definition while_not_nil :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
"while_not_nil f init xs = (List.foldr f xs init)"
*)


 
(* transition systems ----------------------------------------------- *)

(* transition system basic definitions *)

type_synonym 's trans_t = "('s * 's) set"

definition trace_set :: "('s * 's) set \<Rightarrow> (nat \<Rightarrow> 's) set" where
"trace_set trns = { f .  (! (n::nat). (f n, f(n+1)) : trns) }"

definition invariant :: "('s * 's) set \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant trns P = (! s s'. (s,s') : trns \<longrightarrow> P s \<longrightarrow> P s')"

(* the main lemma about invariants FIXME prove this *)  
definition invariant_thm :: "'s trans_t \<Rightarrow> bool" where
"invariant_thm trns = (! P f.
  invariant trns P & 
  f : trace_set trns &
  P(f 0) \<longrightarrow> (! n. P (f n)) 
)"


(* Q is invariant, assuming P holds always; allows staging of the proof of various invariants *)
definition invariant_assuming :: "('s * 's) set \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant_assuming trns P Q = (
  let trns = { (s,s'). (s,s') : trns & P s & P s' } in
  invariant trns Q)
"

definition invariant_assuming_thm :: "'s trans_t \<Rightarrow>  ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
"invariant_assuming_thm trns P Q = (
  invariant trns P &
  invariant_assuming trns P Q 
  \<longrightarrow> invariant trns (% x. P x & Q x)
)"



