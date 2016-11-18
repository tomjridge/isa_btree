theory Insert
imports Find
begin

datatype i_error = I_find_error find_error | I_malformed_stack string | I_store_error store_error | I_error string
type_synonym ie = i_error

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

type_synonym is_t = i_state_t  

type_synonym 'a ie_M = "('a,ie) M"

definition ie_bind :: "('a \<Rightarrow> 'b ie_M) \<Rightarrow> 'a ie_M \<Rightarrow> 'b ie_M" where
"ie_bind f v = bind f v"


definition split_leaf :: "kvs \<Rightarrow> (kvs * k * kvs)" where
"split_leaf kvs = (
  let min = min_leaf_size in
  let (l,r) = split_at min kvs in
  let k = (case r of (k,_)#_ \<Rightarrow> k | _ \<Rightarrow> impossible) in
  (l,k,r)
)"

definition split_node :: "ks_rs \<Rightarrow> (ks_rs * k * ks_rs)" where
"split_node n = (
  let (ks,rs) = n in
  let min = min_node_keys in
  let (ks1,k,ks2) = split_at_3 min ks in
  let (rs1,rs2) = split_at (min+1) rs in
  ((ks1,rs1),k,(ks2,rs2))
)"

definition i_alloc :: "p \<Rightarrow> r ie_M" where 
"i_alloc p = (alloc p |> fmap_error (% se. I_store_error se))"

definition page_ref_to_frame :: "r \<Rightarrow> fr ie_M" where
"page_ref_to_frame r = (Frame.page_ref_to_frame r |> fmap_error (% se. I_store_error se))"

definition step_down :: "d \<Rightarrow> d ie_M" where
"step_down d = (
  let (fs,v) = d in
  find_step fs |> fmap_error (% fe. I_find_error fe) |> fmap (% d'. (d',v))
)"

definition step_bottom :: "d \<Rightarrow> u ie_M" where
"step_bottom d = (
  let (fs,v) = d in
  case fs of
  Find_down _ \<Rightarrow> impossible
  | Find_finished (k,r,kvs,stk) \<Rightarrow> (
    let kvs' = kvs |> kvs_insert k v in
    let fo = (
      case (length kvs' \<le> max_leaf_size) of
      True \<Rightarrow> (Leaf_frame kvs' |> frame_to_page |> i_alloc |> fmap (% r'. I1(r')))
      | False \<Rightarrow> (
        let (kvs1,k',kvs2) = split_leaf kvs' in
        Leaf_frame kvs1 |> frame_to_page |> i_alloc |> ie_bind
        (% r1. Leaf_frame kvs2 |> frame_to_page |> i_alloc |> fmap (% r2. I2(r1,k',r2)))
      )
    )
    in
    fo |> fmap (% fo. (fo,stk)) 
  )
)"

definition step_up :: "u \<Rightarrow> u ie_M" where
"step_up u = (
  let (fo,stk) = u in
  case stk of 
  [] \<Rightarrow> impossible
  | x#stk' \<Rightarrow> (
    let (rs1,ks1,_,ks2,rs2) = x in
    case fo of
    I1 r \<Rightarrow> (
      Node_frame(ks1@ks2,rs1@[r]@rs2) |> frame_to_page |> i_alloc |> fmap (% r. (I1 r,stk'))
    )
    | I2 (r1,k,r2) \<Rightarrow> (
      let ks' = ks1@[k]@ks2 in
      let rs' = rs1@[r1,r2]@rs2 in
      case (List.length ks' \<le> max_node_keys) of
      True \<Rightarrow> (
        Node_frame(ks',rs') |> frame_to_page |> i_alloc |> fmap (% r. (I1 r,stk'))
      )
      | False \<Rightarrow> (
        let (ks_rs1,k,ks_rs2) = split_node (ks',rs') in
        Node_frame(ks_rs1) |> frame_to_page |> i_alloc |> ie_bind
        (% r1. Node_frame (ks_rs2) |> frame_to_page |> i_alloc |> fmap (% r2. (I2(r1,k,r2),stk')))
      )
    )
  )
)"

end