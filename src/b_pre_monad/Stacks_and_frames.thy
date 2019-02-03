theory Stacks_and_frames imports A_start_here Key_value begin

(* NOTE the 4th component is the parent root *)
datatype ('a,'b,'c,'d) stk_frame = Frm "'a * 'b * 'c * 'd"

fun dest_Frm :: "('a,'b,'c,'d) stk_frame \<Rightarrow> 'a * 'b * 'c * 'd" where "
dest_Frm (Frm (a,b,c,d)) = (a,b,c,d)"


(* type_synonym ('a,'b,'c) stk = "('a,'b,'c) stk_frame list" *)

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

end