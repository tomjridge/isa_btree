theory Delete2
imports Find
begin

(* FIXME merge in documentation from Delete *)

(* new version with less attempt at treating all cases uniformly *)

datatype ('k,'v,'r)del_t =
  D_small_leaf "('k*'v)s"
  | D_small_node "'k s * 'r s"
  | D_updated_subtree "'r"

type_synonym ('k,'v,'r) fo = "('k,'v,'r) del_t"  (* focus *)

(* dead: https://groups.google.com/forum/#!topic/fa.isabelle/hWGSgu3pSsM *)

(* D_down: r is the original pointer to root, in case we don't delete anything *)
datatype (dead 'k, dead 'v,dead 'r) delete_state = 
  D_down "('k,'v,'r) fs * 'r"  
  | D_up "('k,'v,'r) fo * ('k,'r) rstk"
  | D_finished "'r" 
  
type_synonym ('k,'v,'r)u = "('k,'v,'r)fo * ('k,'r)rstk"  
type_synonym ('k,'v,'r)d = "('k,'v,'r)find_state * 'r"

type_synonym ('k,'v,'r)dst = "('k,'v,'r) delete_state"

definition mk_delete_state :: "'k \<Rightarrow> 'r \<Rightarrow> ('k,'v,'r)dst" where
"mk_delete_state k r = (D_down(mk_find_state k r,r))"

definition dest_d_finished :: "('k,'v,'r)dst \<Rightarrow> 'r option" where
"dest_d_finished x = (case x of D_finished r \<Rightarrow> Some r | _ \<Rightarrow> None)"



(* steal or merge --------------------------------------------------- *)

(* some variable namings 

p.ks1: k1#ks1'
p.ks2: 

*)


(* node steal -------------- *)

definition dest_krs :: "('k s * 'r s) \<Rightarrow> ('k * 'r * ('k s * 'r s))" where
"dest_krs krs = (
  case krs of 
  (k#rest,r#rest') \<Rightarrow> (k,r,(rest,rest'))
  | _ \<Rightarrow> failwith (STR ''dest_node''))"
  

(* args are left split node context, focus, right sib; returns updated parent *)
definition node_steal_right :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM" 
where
"node_steal_right store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (k2#rest,r2#rest') \<Rightarrow> 
  case (p|>r_ks2,p|>r_ts2) of (k1#ks2,_#rs2) \<Rightarrow>   
  (ks1@[k1],rs1@[r2]) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r3.
  (rest,rest') |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4.
  p \<lparr> r_t:=r3, r_ks2:=k2#ks2, r_ts2:=r4#rs2 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"


definition node_steal_left :: 
  "('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('r,'t) MM" 
where
"node_steal_left store_ops p c1 c2 = (
  let c1 = (c1 |> (% (x,y). (rev x, rev y))) in
  case c1 of (k1#rest,r1#rest') \<Rightarrow>
  case c2 of (ks2,rs2) \<Rightarrow>
  case (p|>r_ks1,p|>r_ts1) of (k2#ks1,_#rs1) \<Rightarrow>
  (rev rest,rev rest') |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r3.
  (k2#ks2,r1#rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4.
  p \<lparr> r_ks1:=k1#ks1, r_ts1:=r3#rs1, r_t:=r4 \<rparr>
  |> unsplit_node |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
  return p))))"

(* node merge ----------------- *)

definition node_merge_right :: 
  "constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> (('k,'v,'r)fo,'t) MM"
where
"node_merge_right cs store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (ks2,rs2) \<Rightarrow> 
  case (p|>r_ks2,p|>r_ts2) of (k2#ks2,_#p_rs2) \<Rightarrow>   
  (ks1@[k2]@ks2,rs1@rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4. 
  p \<lparr> r_t:=r4, r_ks2:=ks2, r_ts2:=p_rs2 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  case List.length ks < cs|>min_node_keys of
  False \<Rightarrow> (
    (ks,rs) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
    return (D_updated_subtree(p))))
  | True \<Rightarrow> (
    return (D_small_node(ks,rs))))))"

definition node_merge_left :: 
"constants \<Rightarrow> ('k,'v,'r,'t)store_ops \<Rightarrow> ('k,'r)rsplit_node \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> (('k,'v,'r)fo,'t) MM"
where
"node_merge_left cs store_ops p c1 c2 = (
  case c1 of (ks1,rs1) \<Rightarrow> 
  case c2 of (ks2,rs2) \<Rightarrow> 
  case (p|>r_ks1,p|>r_ts1) of (k2#ks1,_#p_rs1) \<Rightarrow>   
  (ks1@[k2]@ks2,rs1@rs2) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% r4. 
  p \<lparr> r_t:=r4, r_ks1:=ks1, r_ts1:=p_rs1 \<rparr>
  |> unsplit_node |> (% (ks,rs).
  case List.length ks < cs|>min_node_keys of
  False \<Rightarrow> (
    (ks,rs) |> mk_Disk_node |> (store_ops|>store_alloc) |> bind (% p.
    return (D_updated_subtree(p))))
  | True \<Rightarrow> (
    return (D_small_node(ks,rs))))))"


(* leaf steal --------------------- *)

type_synonym ('k,'v) leaf = "('k * 'v) list"

(* parent, left, right *)
type_synonym ('k,'a) l3 = "('k,'a) rsplit_node * ('k,'a) leaf * ('k,'a) leaf"
type_synonym ('k,'a) l2 = "('k,'a) rsplit_node * ('k,'a) leaf"


definition leaf_steal_right :: "('k,'a)l3 \<Rightarrow> ('k,'a)l3" where
"leaf_steal_right plr = (
  let (p,l,r) = plr in
  case (p|>r_ks2,r) of
  (_#ks2',((k,v)#(k',v')#rest)) \<Rightarrow> (  (* FIXME min size constraint *)
    let l = l@[(k,v)] in
    let p = p \<lparr> r_ks2:=k'#ks2' \<rparr> in
    let r = (k',v')#rest in
    (p,l,r))
  | _ \<Rightarrow> impossible1 (STR ''leaf_steal_right''))"

definition leaf_steal_left :: "('k,'a)l3 \<Rightarrow> ('k,'a)l3" where
"leaf_steal_left plr = (
  let (p,l,r) = plr in
  let l = List.rev l in
  case (l,p|>r_ks1) of
  (((k,v)#rest),_#ks1') \<Rightarrow> ( 
    let l = List.rev rest in
    let p = p \<lparr> r_ks1:=k#ks1' \<rparr> in
    let r = (k,v)#rest in
    (p,l,r))
  | _ \<Rightarrow> impossible1 (STR ''leaf_steal_left''))"


(* leaf merge -------------------------- *)

definition leaf_merge_right :: "('k,'a)l3 \<Rightarrow> ('k,'a)l2" where
"leaf_merge_right plr = (
  let (p,l,r) = plr in
  case p|>r_ks2 of 
  _#ks2' \<Rightarrow> (
    let l = l@r in
    let p = p \<lparr> r_ks2:=ks2' \<rparr> in
    (p,l))
  | _ \<Rightarrow> impossible1 (STR ''leaf_merge_right''))"

definition leaf_merge_left :: "('k,'a)l3 \<Rightarrow> ('k,'a)l2" where
"leaf_merge_left plr = (
  let (p,l,r) = plr in
  case p|>r_ks1 of 
  _#ks1' \<Rightarrow> (
    let r = l@r in
    let p = p \<lparr> r_ks1:=ks1' \<rparr> in
    (p,r))
  | _ \<Rightarrow> impossible1 (STR ''leaf_merge_left''))"



(* post_steal_or_merge ---------------------- *)

(* when called on a node (D_...) which is a root resulting from a delete op,
we may have the situation that the root contains no keys, or is small *)

(*
definition post_steal_or_merge :: "('k,'v,'r,'t) ps1 \<Rightarrow> ('k,'r)rstk \<Rightarrow> ('k,'r) rsplit_node \<Rightarrow> 
  ('k s * 'r s) \<Rightarrow> ('k s * 'r s) \<Rightarrow> ('k,'r) d12_t => (('k,'v,'r) u,'t) MM" 
where
"post_steal_or_merge ps1 stk' p_unused p_1 p_2 x = (
      let store_ops = ps1 |> dot_store_ops in
      let m = frac_mult in
      case x of 
      D1 c' \<Rightarrow> (
        let p' = mk_Disk_node(m (m p_1 ([],[c'])) p_2) in
        let p_sz = p'|>dest_Disk_node|>fst|>List.length in
        let f' = ( (* we may be at root, having deleted the single key *)
          case (p_sz = 0) of
          True \<Rightarrow> (
            (* the parent was the root; it had one key *)
            let _ = check_true (%_. stk'=[]) in
            return (D_updated_subtree(c')))
          | False \<Rightarrow> (
            case (p_sz < ps1|>dot_constants|>min_node_keys) of 
            True \<Rightarrow> (
              (* new parent is small *)
              return (D_small_node(p'|>dest_Disk_node)))
            | False \<Rightarrow> (
              (* new parent is not small *)
              (* write the frame at this point *)
              p'|>(store_ops|>store_alloc)|>fmap (% r. D_updated_subtree(r)))))
        in
        f' |> fmap (% f'. (f',stk')) )
      | D2(c1,k,c2) \<Rightarrow> (
        let p' = mk_Disk_node(m (m p_1 ([k],[c1,c2])) p_2) in
        let p_sz = p'|>dest_Disk_node|>fst|>List.length in
        let f' = (
          (* we may be at the root, in which case f' may be small *)
          case (p_sz < ps1|>dot_constants|>min_node_keys) of
          True \<Rightarrow> (
            (* we are at the root, and the new root is small *)
            let _ = check_true (%_.stk'=[]) in
            return (D_small_node(p'|>dest_Disk_node))
          )
          | False \<Rightarrow> (
            p' |>(store_ops|>store_alloc)|>fmap (% r. D_updated_subtree(r))))
        in
        f' |> fmap (% f'. (f',stk')))       
)"
*)



(* delete ----------------------------------------------------------  *)

definition step_up :: "('k,'v,'r,'t)ps1 \<Rightarrow>('k,'v,'r)u \<Rightarrow> (('k,'v,'r)u,'t) MM" where
"step_up ps1 du = (
  let (f,stk) = du in
  let store_ops = ps1|>dot_store_ops in
  case stk of
  [] \<Rightarrow> (impossible1 (STR ''delete, step_up''))
  | p#stk' \<Rightarrow> (
    (* NOTE p is the parent *)
    case f of   
    D_updated_subtree r \<Rightarrow> (
      let (ks,rs) = unsplit_node (p\<lparr>r_t:=r\<rparr>) in
      mk_Disk_node(ks,rs) |> (store_ops|>store_alloc) |> fmap (% r'. (D_updated_subtree r',stk')))
    | D_small_leaf(kvs) \<Rightarrow> (
      (* we need to steal or merge *)
      case p|>r_ks2 of 
      [] \<Rightarrow> (
        (* no right sibling; steal or merge from left *)
        case p|>r_ks1 of
        [] \<Rightarrow> impossible1 (STR ''step_up: no right sibling, no left sibling'')
        | ks1 \<Rightarrow> (        
          (* decide whether to steal or merge *)
          let l = List.hd (p|>r_ts1) in
          (store_ops|>store_read) l 
          |> fmap (% frm. dest_Disk_leaf frm) 
          |> bind (% l_kvs. 
            case List.length l_kvs = ps1|>dot_cs|>min_leaf_keys of
            True \<Rightarrow> (
              (* left sibling has minimal length; merge *)
              leaf_merge_left (p,l_kvs,kvs) |> 
              (% (p,r). 
                (* FIXME we should go through something like d12 because we don't know the child
                reference to place in the parent *)
                r |> (store_ops|>store_alloc) |> bind 
                (% r. p |> (store_ops|>store_alloc) |> fmap
                (% p. 
                
            )
          
        )
      let leaf = True in
      let mk_c = (% ks_vs. let (ks,vs) = ks_vs in Disk_leaf(List.zip ks vs)) in
      let (p_ks1,p_rs1,_,p_ks2,p_rs2) = p|>dest_rsplit_node in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm = (store_ops|>store_read) r in
      let d12 :: (('k,('k,'v,'r) dnode) d12_t,'t) MM = 
        frm |> fmap (% frm. 
          steal_or_merge 
            (ps1|>dot_constants) right leaf mk_c 
            (kvs|>unzip) p_k (frm|>dest_Disk_leaf|>unzip))
      in
      let d12' :: (('k,'r) d12_t,'t) MM = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> (store_ops|>store_alloc) |> fmap (% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> (store_ops|>store_alloc) |> bind
          (% r1. frm2 |> (store_ops|>store_alloc) |> fmap 
          (% r2. D2(r1,p_k,r2)))))
      in
      d12' |> bind (% x. post_steal_or_merge ps1 stk' p p_1 p_2 x) 
    )
    
  | D_small_node(ks,rs) \<Rightarrow> (
      (* FIXME almost identical to small leaf case *)
      let leaf = False in
      let mk_c = (% ks_rs. mk_Disk_node(ks_rs)) in 
      (* FIXME the small cases can be handled uniformly; want steal left,right to be uniform, and take a child as arg; also return option *)  
      (* parent info is already read, but we must read the siblings from disk *)
      let (p_ks1,p_rs1,_,p_ks2,p_rs2) = p|>dest_rsplit_node in
      let (right,(p_1,p_2),(p_k,r)) = get_sibling ((p_ks1,p_rs1),(p_ks2,p_rs2)) in
      let frm = (store_ops|>store_read) r in
      let d12 = frm |> fmap (% frm. 
        steal_or_merge (ps1|>dot_constants) right leaf mk_c 
          (ks,rs) p_k (frm|>dest_Disk_node)) 
      in
      let d12' = d12 |> bind
      (% x. case x of
        D1 frm \<Rightarrow> frm |> (store_ops|>store_alloc) |> fmap(% r. D1 r)
        | D2(frm1,p_k,frm2) \<Rightarrow> (
          frm1 |> (store_ops|>store_alloc) |> bind
          (% r1. frm2 |> (store_ops|>store_alloc) |> fmap 
          (% r2. D2(r1,p_k,r2)))))
      in
      d12' |> bind (% x. post_steal_or_merge ps1 stk' p p_1 p_2 x)
    )
  )
)"

definition delete_step :: 
  "('k,'v,'r,'t)ps1 \<Rightarrow> ('k,'v,'r)delete_state \<Rightarrow> (('k,'v,'r)delete_state,'t) MM" 
where
"delete_step ps1 s = (
  let store_ops = ps1|>dot_store_ops in
  case s of 
  D_down(f,r0) \<Rightarrow> (
    case (dest_f_finished f) of
    None \<Rightarrow> (find_step ps1 f |> fmap (% f'. D_down(f',r0)))
    | Some x \<Rightarrow> (
      let (r0,k,r,kvs,stk) = x in
      (store_ops|>store_free) (r0#(r_stk_to_rs stk)) |> bind 
      (% _.
      case (? x : set (kvs|>List.map fst). key_eq (ps1|>dot_cmp) x k) of
      True \<Rightarrow> (
        (* something to delete *)
        let kvs' = kvs|>List.filter (% x. ~ (key_eq (ps1|>dot_cmp) (fst x) k)) in
        case (List.length kvs' < ps1|>dot_constants|>min_leaf_size) of
        True \<Rightarrow> (return (D_up(D_small_leaf(kvs'),stk,r0)))
        | False \<Rightarrow> (
          Disk_leaf(kvs') |> (store_ops|>store_alloc) |> fmap
          (% r. D_up(D_updated_subtree(r),stk,r0))))
      | False \<Rightarrow> (
        (* nothing to delete *)
        return (D_finished r0) ))))  (* D_down *)
  | D_up(f,stk,r0) \<Rightarrow> (
    case stk of
    [] \<Rightarrow> (
      case f of
      D_small_leaf kvs \<Rightarrow> (Disk_leaf(kvs)|>(store_ops|>store_alloc)|>fmap (% r. D_finished r)) 
      | D_small_node (ks,rs) \<Rightarrow> (
        mk_Disk_node(ks,rs)|>(store_ops|>store_alloc)|>fmap (% r. D_finished r) )
      | D_updated_subtree(r) \<Rightarrow> (return (D_finished r)))
    | _ \<Rightarrow> (step_up ps1 (f,stk) |> fmap (% (f,stk). (D_up(f,stk,r0)))) )
  | D_finished(r) \<Rightarrow> (return s)  (* stutter *) )"


(* wellformedness --------------------------------------------------- *)

definition wf_d :: "'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v) tree \<Rightarrow> 't \<Rightarrow> ('k,'v,'r) d \<Rightarrow> bool" where
"wf_d k_ord r2f t0 s d =  assert_true (
  let (fs,r) = d in
  assert_true (wellformed_find_state k_ord r2f t0 s fs)
)"

definition wf_u :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v) tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> ('k,'v,'r)u \<Rightarrow> bool" 
where
"wf_u constants k_ord r2t t0 s k u =  assert_true (
  let (fo,stk) = u in
  let check_stack = % rstk tstk. (rstack_equal (rstk|>rstack_map (r2t s)|>no_focus) (tstk|>rstack_map Some|>no_focus)) in
  let check_wf = % ms t. (wellformed_tree constants ms k_ord t) in
  let check_focus = % fo kvs. kvs_equal (fo|> tree_to_kvs |> kvs_delete k_ord k) kvs in
  case fo of
  D_small_leaf kvs \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_leaf) in
    assert_true (check_stack stk t_stk) & 
    assert_true (check_wf ms (Leaf kvs)) &
    assert_true (check_focus t_fo kvs)
  )
  | D_small_node (ks,rs) \<Rightarrow> (
    (* FIXME don't we need some wf on Node(ks,rs)? *)
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> Some Small_node) in
    let t = Node(ks,rs|>List.map (r2t s) |> List.map dest_Some) in  (* FIXME check we can dest_Some *)
    assert_true (check_stack stk t_stk) &
    assert_true (check_wf ms t) &
    assert_true (check_focus t_fo (t|>tree_to_kvs))   
  )
  | D_updated_subtree(r) \<Rightarrow> (
    let (t_fo,t_stk) = tree_to_rstack k_ord k t0 (List.length stk) in
    let ms  = (case stk of [] \<Rightarrow> Some Small_root_node_or_leaf | _ \<Rightarrow> None) in
    let t = r|>r2t s|>dest_Some in  (* FIXME check dest *)
    assert_true (check_stack stk t_stk) &
    assert_true (check_wf ms t) &
    assert_true (check_focus t_fo (t|>tree_to_kvs))   
  )
)"

definition wf_f :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> 'r \<Rightarrow> bool" 
where
"wf_f constants k_ord r2t t0 s k r =  assert_true (
  let t' = r2t s r |> dest_Some in  (* check dest_Some *)
  assert_true (wellformed_tree constants (Some(Small_root_node_or_leaf)) k_ord t') &
  assert_true (kvs_equal ( (t0|>tree_to_kvs|>kvs_delete k_ord k)) (t'|>tree_to_kvs))
)"

definition wellformed_delete_state :: 
  "constants \<Rightarrow> 'k ord \<Rightarrow> ('k,'v,'r,'t)r2t \<Rightarrow> ('k,'v)tree \<Rightarrow> 't \<Rightarrow> 'k \<Rightarrow> ('k,'v,'r)delete_state \<Rightarrow> bool" 
where
"wellformed_delete_state constants k_ord r2t t0 s k ds =  assert_true (
  case ds of 
  D_down d \<Rightarrow> (wf_d k_ord r2t t0 s d)
  | D_up (fo,stk,r) \<Rightarrow> (
    wf_u constants k_ord r2t t0 s k (fo,stk) & 
    (case r2t s r of None \<Rightarrow> False | Some t \<Rightarrow> tree_equal t t0))
  | D_finished r \<Rightarrow> (wf_f constants k_ord r2t t0 s k r) 
)
"

end




(* old ----------------------- *)

(* steal or merge to the right *)
(*
definition node_steal_right :: "('k,'a) n3 \<Rightarrow> ('k,'a) n3" where
"node_steal_right pcs = (
  let (p,c,s) = pcs in
  case (p|>r_ks2,s) of
  (k#ks2',(k'#rest,t#rest')) \<Rightarrow> (
    let c = 
      let (ks,rs) = c in
      (ks@[k],rs@[t])
    in
    let s = (rest,rest') in
    let p = p \<lparr> r_ks2:=k'#ks2' \<rparr> in
    (p,c,s))
  | (_,_) \<Rightarrow> impossible1 (STR ''node_steal_right''))"
*)
