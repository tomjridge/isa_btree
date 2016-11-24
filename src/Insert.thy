theory Insert
imports Find
begin


datatype i_t = I1 r | I2 "r*k*r"

type_synonym focus_t = "i_t"
type_synonym fo = focus_t

type_synonym down_state = "fs*v"
type_synonym d = down_state
type_synonym up_state = "fo*stk"
type_synonym u = up_state

datatype i_state_t = 
  I_down d
  | I_up u
  | I_finished r

type_synonym is_t = i_state_t  

definition step_down :: "d \<Rightarrow> d MM" where
"step_down d = (
  let (fs,v) = d in
  find_step fs |> fmap (% d'. (d',v))
)"

definition step_bottom :: "d \<Rightarrow> u MM" where
"step_bottom d = (
  let (fs,v) = d in
  case find_dest_finished fs of 
  None \<Rightarrow> impossible ()
  | Some(k,l,r,u,kvs,stk) \<Rightarrow> (
    let kvs' = kvs |> kvs_insert k v in
    let fo = (
      case (length kvs' \<le> max_leaf_size) of
      True \<Rightarrow> (Leaf_frame kvs' |> frame_to_page |> alloc |> fmap (% r'. I1(r')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf kvs' in
        Leaf_frame kvs1 |> frame_to_page |> alloc |> bind
        (% r1. Leaf_frame kvs2 |> frame_to_page |> alloc |> fmap (% r2. I2(r1,k',r2)))) )
    in
    fo |> fmap (% fo. (fo,stk)))
)"

definition step_up :: "u \<Rightarrow> u MM" where
"step_up u = (
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible ()  (* FIXME what about trace? can't have arb here; or just stutter on I_finished in step? *)
  | x#stk' \<Rightarrow> (
    let (l,((ks1,rs1),(ks2,rs2)),u) = x in
    case fo of
    I1 r \<Rightarrow> (
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> frame_to_page |> alloc |> fmap (% r. (I1 r,stk')))
    | I2 (r1,k,r2) \<Rightarrow> (
      let ks' = ks1@[k]@ks2 in
      let rs' = rs1@[r1,r2]@rs2 in
      case (List.length ks' \<le> max_node_keys) of
      True \<Rightarrow> (
        Node_frame(ks',rs') |> frame_to_page |> alloc |> fmap (% r. (I1 r,stk')))
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node (ks',rs') in
        Node_frame(ks_rs1) |> frame_to_page |> alloc |> bind
        (% r1. Node_frame (ks_rs2) |> frame_to_page |> alloc |> fmap (% r2. (I2(r1,k,r2),stk'))))
    )
  )
)"

definition post_step_up :: "fo \<Rightarrow> r MM" where
"post_step_up fo = (
  case fo of 
  I1 r \<Rightarrow> (return r)
  | I2(r1,k,r2) \<Rightarrow> (Node_frame([k],[r1,r2]) |> frame_to_page |> alloc)
)"

definition step :: "is_t \<Rightarrow> is_t MM" where
"step s = (
  case s of 
  I_down d \<Rightarrow> (
    let (fs,v) = d in
    case (find_dest_finished fs) of 
    None \<Rightarrow> (step_down d |> fmap (% d. I_down d))
    | Some _ \<Rightarrow> step_bottom d |> fmap (% u. I_up u))
  | I_up u \<Rightarrow> (
    let (fo,stk) = u in
    case stk of
    [] \<Rightarrow> post_step_up fo |> fmap (% r. I_finished r)
    | _ \<Rightarrow> (step_up u |> fmap (% u. I_up u)))
)"

definition insert_dest_finished :: "is_t \<Rightarrow> r option" where
"insert_dest_finished s = (case s of I_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"



end