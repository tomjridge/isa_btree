theory Leaf_stream 
imports Find "$SRC/b_pre_monad/Leaf_stream_state" Insert_many
begin

definition step_down :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
('r*'frame list) \<Rightarrow> (('r,'leaf,'frame)leaf_stream_state,'t) MM" where
"step_down frame_ops store_ops r_fs = (
  let (r,fs) = r_fs in
  (store_ops|>read) r |> fmap 
  (% f. case f of 
    Disk_node n \<Rightarrow> (
      let frm = (frame_ops|>split_node_for_leaf_stream) r n in
      let r = (frame_ops|>midpoint) frm in
      LS_down (r,frm#fs)) 
    | Disk_leaf leaf \<Rightarrow> LS_leaf (leaf,fs))
)"


(* don't have to access disk *)
definition step_leaf :: "'leaf * 'frame list \<Rightarrow> ('r,'leaf,'frame) leaf_stream_state" where
"step_leaf r = (
  let (leaf,fs) = r in
  LS_up fs)"


(* assumes fs <> [] *)
definition step_up :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
'frame list \<Rightarrow> ('r,'leaf,'frame) leaf_stream_state" where
"step_up frame_ops fs = (
  case fs of 
  [] \<Rightarrow> (failwith (STR ''Leaf_stream, step_up''))
  | frm#fs \<Rightarrow> (
    case (frame_ops|>step_frame_for_leaf_stream) frm of 
    None \<Rightarrow> (LS_up fs)
    | Some frm' \<Rightarrow> (
      let r = (frame_ops|>midpoint) frm' in    
      LS_down (r,frm'#fs) )))"

  
definition ls_step :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
('r,'leaf,'frame) leaf_stream_state \<Rightarrow> (('r,'leaf,'frame) leaf_stream_state,'t) MM" where
"ls_step frame_ops store_ops lss = (
  case lss of 
  LS_down x \<Rightarrow> (step_down frame_ops store_ops x)
  | LS_leaf x \<Rightarrow> (return (step_leaf x))
  | LS_up x \<Rightarrow> (return (step_up frame_ops x)))"

(* FIXME now we need the "step from leaf to leaf" *)

(* we iterate ls_step until we reach a leaf (or we finish the traversal) *)
definition ls_step_to_next_leaf :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
('r,'leaf,'frame) leaf_stream_state \<Rightarrow> (('r,'leaf,'frame) leaf_stream_state option,'t) MM" where
"ls_step_to_next_leaf frame_ops store_ops lss = (
  case ls_is_finished lss of
  True \<Rightarrow> (return None)
  | False \<Rightarrow> (
  ls_step frame_ops store_ops lss |> bind (% lss.
  (lss,False) |> iter_m (% s.
    let (lss,known_finished) = s in
    case known_finished of 
    True \<Rightarrow> return None
    | False \<Rightarrow> (
      case ls_is_finished lss of
      True \<Rightarrow> return (Some(lss,True))
      | False \<Rightarrow> (
        case dest_LS_leaf lss of
        None \<Rightarrow> (
          ls_step frame_ops store_ops lss |> fmap (% lss. 
          (Some(lss,False))))
        | Some _ \<Rightarrow> return None))))
  |> fmap (% (lss,known_finished).
    case known_finished \<or> ls_is_finished lss of 
    True \<Rightarrow> None
    | False \<Rightarrow> (Some(lss)))))"

(* we also need to establish the initial leaf stream state, from a root pointer and stepping down 
to the first leaf *)
definition initial_ls_state :: "
('k,'r,'frame,'node) frame_ops \<Rightarrow> 
('r,('node,'leaf)dnode,'t) store_ops \<Rightarrow>  
'r \<Rightarrow> (('r,'leaf,'frame)leaf_stream_state,'t) MM" where
"initial_ls_state frame_ops store_ops r = (
  ls_step_to_next_leaf frame_ops store_ops (LS_down (r,[])) |> fmap (% s.
  case s of 
  None \<Rightarrow> failwith (STR ''impossible, there must be at least one leaf'')
  | Some x \<Rightarrow> x))
"

definition dummy where "dummy = Insert_many.dummy"

end