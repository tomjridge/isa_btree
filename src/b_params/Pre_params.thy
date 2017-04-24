theory Pre_params
imports  "$SRC/a_tree/Tree_stack"
begin

(* leaf stream types ----------------------------------------- *)

(* we need these exposed outside functor body in ML *)

datatype ('k,'v,'r) ls_state = 
  LS_down "'r*('k,'r) ts_frame list" 
  | LS_leaf "('k*'v) list * ('k,'r) ts_frame list" 
  | LS_up "('k,'r) ts_frame list"
  
end