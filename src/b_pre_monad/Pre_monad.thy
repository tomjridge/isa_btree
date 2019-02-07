theory Pre_monad
imports 
(* suggested order *)
A_start_here
Disk_node
Key_value
Tree
(* Tree_stack *)
(* don't import the states - they tend to clash with each other? *)
Find_state
Insert_state
(* Insert_many_state *)
Delete_state
(* Leaf_stream_state *)
begin

definition dummy :: "unit" where "dummy = (
  let _ = (% x :: (int,int,int,unit) dnode. x) in
  let _ = (% x :: (int,int,int,unit)find_state. x) in
  let _ = (% x :: (int,int,int,int)insert_state. x) in
  let _ = (% x :: (int,int,int,int)delete_state. x) in
(*  let _ = (% x :: (int,int,int)im_state. x) in *)
(*  let _ = (% x :: (int,int,int)lss. x) in *)
  let _ = (% x :: (int,int)tree. x) in
  let _ = (% x :: (int + int). x) in
(*  let _ = Insert_many_state.dummy in *)
  ()
)"


end