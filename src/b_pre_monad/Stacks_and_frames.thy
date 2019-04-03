theory Stacks_and_frames imports A_start_here Key_value begin

(* for performance, we need to abstract over frames *)

datatype ('k,'r) rkr_or_r = Rkr "'r*'k*'r" | R 'r

(* \doc(doc:frame_ops) *)
datatype_record ('k,'r,'frame,'node) frame_ops =
  split_node_on_key :: "'r \<Rightarrow> 'k \<Rightarrow> 'node \<Rightarrow> 'frame"
  midpoint :: "'frame \<Rightarrow> 'r"
  get_right_sibling_and_separator :: "'frame \<Rightarrow> ('k * 'r) option"
  remove_right_sibling :: "'frame \<Rightarrow> 'frame"  (* for merge; assumes present *)
  replace_right_sibling :: "'k \<Rightarrow> 'r \<Rightarrow> 'frame \<Rightarrow> 'frame"  (* NOTE extra k argument; the new lower bound *)
  get_left_sibling_and_separator :: "'frame \<Rightarrow> ('r * 'k) option"
  remove_left_sibling :: "'frame \<Rightarrow> 'frame"
  replace_left_sibling :: "'r \<Rightarrow> 'frame \<Rightarrow> 'frame"
  unsplit_with_new_focus :: "'r \<Rightarrow> 'frame \<Rightarrow> 'node" 
  unsplit_with_new_focus_2 :: "'r*'k*'r \<Rightarrow> 'frame \<Rightarrow> 'node" 
  get_midpoint_bounds :: "'frame \<Rightarrow> ('k option * 'k option)"
  backing_node_blk_ref :: "'frame \<Rightarrow> 'r"  (* for rewriting in place *)

  (* FIXME may want to use lists for the following *)
  split_node_on_first_key :: "'node \<Rightarrow> 'frame"  (* for leaf stream *)
  step_frame_for_ls :: "'frame \<Rightarrow> 'frame option"

(*
  left_halfx :: "'frame \<Rightarrow> 'left_half"
  right_half :: "'frame \<Rightarrow> 'right_half"
  lh_dest_snoc :: "'left_half \<Rightarrow> ('left_half*'r*'k) option"

*)


definition get_bounds :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow>
'frame list \<Rightarrow> ('k option *  'k option)" where
"get_bounds frame_ops stk = (
  iter_step (% (l,u,stk).
    case stk of [] \<Rightarrow> None
    | frm#stk \<Rightarrow> (
      case (l,u) of (Some _,Some _) \<Rightarrow> None
      | _ \<Rightarrow> (
        let (l',u') = (frame_ops|>get_midpoint_bounds) frm in
        let l = (case l of None \<Rightarrow> l' | _ \<Rightarrow> l) in
        let u = (case u of None \<Rightarrow> u' | _ \<Rightarrow> u) in
        Some(l,u,stk))))
    (None,None,stk)
  |> (% (l,u,_). (l,u)))"

end

(*
(* NOTE the 4th component is the parent root *)
datatype ('a,'b,'c,'d) stk_frame = Frm "'a * 'b * 'c * 'd"

fun dest_Frm :: "('a,'b,'c,'d) stk_frame \<Rightarrow> 'a * 'b * 'c * 'd" where "
dest_Frm (Frm (a,b,c,d)) = (a,b,c,d)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

(* NOTE the first component has the lists reversed *)
type_synonym ('k,'r) frame = "( ('r list * 'k list), 'r, ('k list * 'r list), 'r) stk_frame"

type_synonym ('k,'r) stk = "('k,'r) frame list"

definition make_frame :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'r \<Rightarrow> 'k s \<Rightarrow> 'r s \<Rightarrow> ('k,'r)frame * 'r" where
"make_frame k_cmp k r_parent ks rs = (
  iter_step (% ((rs,ks),(ks',rs')).
    case ks' of
    [] \<Rightarrow> None
    | k'#ks' \<Rightarrow> (
      case key_lt k_cmp k k' of
      True \<Rightarrow> None
      | False \<Rightarrow>
        let (r',rs') = (List.hd rs', List.tl rs') in
        Some ( (r'#rs,k'#ks),(ks',rs'))))
    ( ([],[]),(ks,rs))
  |> (% ((rs,ks),(ks',rs')).
     let r' = List.hd rs' in
     (Frm((rs,ks),r',(ks',List.tl rs'),r_parent),  r')))"

(* convert a rsplit_node to a disk node; focus rks has one more r than k *)
definition unsplit_node :: "('r s * 'k s) * ('r s * 'k s) * ('k s * 'r s) \<Rightarrow> ('k s * 'r s)" where
"unsplit_node x = (
  let ((rs1,ks1),(rs2,ks2),(ks3,rs3)) = x in
  ( (List.rev ks1)@ks2@ks3, (List.rev rs1)@rs2@rs3) )"

definition get_bounds :: "('k,'r) stk \<Rightarrow> ('k option *  'k option)" where
"get_bounds stk = (
  iter_step (% (l,u,stk).
    case stk of [] \<Rightarrow> None
    | frm#stk \<Rightarrow> (
      case (l,u) of (Some _,Some _) \<Rightarrow> None
      | _ \<Rightarrow> (
        let ((_,ks1),_,(ks2,_),_) = dest_Frm frm in
        let l = (case l of None \<Rightarrow> (case ks1 of [] \<Rightarrow> None | k#_ \<Rightarrow> Some k) | _ \<Rightarrow> l) in
        let u = (case u of None \<Rightarrow> (case ks2 of [] \<Rightarrow> None | k#_ \<Rightarrow> Some k) | _ \<Rightarrow> u) in
        Some(l,u,stk))))
    (None,None,stk)
  |> (% (l,u,_). (l,u)))"

(*
(* NOTE the 4th component is the parent root *)
datatype ('a,'b,'c,'d) stk_frame = Frm "'a * 'b * 'c * 'd"

fun dest_Frm :: "('a,'b,'c,'d) stk_frame \<Rightarrow> 'a * 'b * 'c * 'd" where "
dest_Frm (Frm (a,b,c,d)) = (a,b,c,d)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

(* NOTE the first component has the lists reversed *)
type_synonym ('k,'r) frame = "( ('r list * 'k list), 'r, ('k list * 'r list), 'r) stk_frame"

type_synonym ('k,'r) stk = "('k,'r) frame list"

definition make_frame :: "'k ord \<Rightarrow> 'k \<Rightarrow> 'r \<Rightarrow> 'k s \<Rightarrow> 'r s \<Rightarrow> ('k,'r)frame * 'r" where
"make_frame k_cmp k r_parent ks rs = (
  iter_step (% ((rs,ks),(ks',rs')).
    case ks' of
    [] \<Rightarrow> None
    | k'#ks' \<Rightarrow> (
      case key_lt k_cmp k k' of
      True \<Rightarrow> None
      | False \<Rightarrow>
        let (r',rs') = (List.hd rs', List.tl rs') in
        Some ( (r'#rs,k'#ks),(ks',rs'))))
    ( ([],[]),(ks,rs))
  |> (% ((rs,ks),(ks',rs')).
     let r' = List.hd rs' in
     (Frm((rs,ks),r',(ks',List.tl rs'),r_parent),  r')))"

(* convert a rsplit_node to a disk node; focus rks has one more r than k *)
definition unsplit_node :: "('r s * 'k s) * ('r s * 'k s) * ('k s * 'r s) \<Rightarrow> ('k s * 'r s)" where
"unsplit_node x = (
  let ((rs1,ks1),(rs2,ks2),(ks3,rs3)) = x in
  ( (List.rev ks1)@ks2@ks3, (List.rev rs1)@rs2@rs3) )"

definition get_bounds :: "('k,'r) stk \<Rightarrow> ('k option *  'k option)" where
"get_bounds stk = (
  iter_step (% (l,u,stk).
    case stk of [] \<Rightarrow> None
    | frm#stk \<Rightarrow> (
      case (l,u) of (Some _,Some _) \<Rightarrow> None
      | _ \<Rightarrow> (
        let ((_,ks1),_,(ks2,_),_) = dest_Frm frm in
        let l = (case l of None \<Rightarrow> (case ks1 of [] \<Rightarrow> None | k#_ \<Rightarrow> Some k) | _ \<Rightarrow> l) in
        let u = (case u of None \<Rightarrow> (case ks2 of [] \<Rightarrow> None | k#_ \<Rightarrow> Some k) | _ \<Rightarrow> u) in
        Some(l,u,stk))))
    (None,None,stk)
  |> (% (l,u,_). (l,u)))"
*)


*)