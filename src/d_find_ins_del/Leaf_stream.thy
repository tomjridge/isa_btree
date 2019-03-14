theory Leaf_stream 
imports Find "$SRC/b_pre_monad/Leaf_stream_state"
begin


definition step_down :: "
('k,'r,'frame,'left_half,'right_half,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
('r*'frame list) \<Rightarrow> (('r,'leaf,'frame)ls_state,'t) MM" where
"step_down frame_ops store_ops r_fs = (
  let (r,fs) = r_fs in
  (store_ops|>read) r |> fmap 
  (% f. case f of 
    Disk_node n \<Rightarrow> (
      let frm = (frame_ops|>split_node_on_first_key) n in
      let r = (frame_ops|>midpoint) frm in
      LS_down (r,frm#fs)) 
    | Disk_leaf leaf \<Rightarrow> LS_leaf (leaf,fs))
)"


(* don't have to access disk *)
definition step_leaf :: "'leaf * 'frame list \<Rightarrow> ('r,'leaf,'frame) ls_state" where
"step_leaf r = (
  let (leaf,fs) = r in
  LS_up fs)"


(* assumes fs <> [] *)
definition step_up :: "
('k,'r,'frame,'left_half,'right_half,'node) frame_ops \<Rightarrow> 
'frame list \<Rightarrow> ('r,'leaf,'frame) ls_state" where
"step_up frame_ops fs = (
  case fs of 
  [] \<Rightarrow> (failwith (STR ''Leaf_stream, step_up''))
  | frm#fs \<Rightarrow> (
    case (frame_ops|>step_frame_for_ls) frm of 
    None \<Rightarrow> (LS_up fs)
    | Some frm' \<Rightarrow> (
      let r = (frame_ops|>midpoint) frm' in    
      LS_down (r,frm'#fs) )))"

  
definition ls_step :: "
('k,'r,'frame,'left_half,'right_half,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
('r,'leaf,'frame) ls_state \<Rightarrow> (('r,'leaf,'frame) ls_state,'t) MM" where
"ls_step frame_ops store_ops lss = (
  case lss of 
  LS_down x \<Rightarrow> (step_down frame_ops store_ops x)
  | LS_leaf x \<Rightarrow> (return (step_leaf x))
  | LS_up x \<Rightarrow> (return (step_up frame_ops x)))"

(* FIXME now we need the "step from leaf to leaf" *)

end