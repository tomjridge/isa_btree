theory Pre_params
imports  Key_value Frame
begin

(* leaf stream types ----------------------------------------- *)

(* we need these exposed outside functor body in ML *)

record ('k,'a) ts_frame =
  f_ks1 :: "'k list"
  f_ts1 :: "'a list"
  f_t :: 'a
  f_ks2 :: "'k list"
  f_ts2 :: "'a list"
  
datatype ('k,'v,'r) ls_state = 
  LS_down "'r*('k,'r) ts_frame list" 
  | LS_leaf "('k*'v) list * ('k,'r) ts_frame list" 
  | LS_up "('k,'r) ts_frame list"
  
end