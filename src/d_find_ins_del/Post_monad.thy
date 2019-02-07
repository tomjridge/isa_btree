theory Post_monad imports "$SRC/c_monad/Monad" begin


(* ops types -------------------------------------------- *)

datatype_record ('r,'dnode,'t) store_ops =
  read :: "'r \<Rightarrow> ('dnode,'t) MM"
  wrte :: "'dnode \<Rightarrow> ('r,'t) MM"
  rewrite :: "'r \<Rightarrow> 'dnode \<Rightarrow> ('r option,'t) MM"
  free :: "'r s \<Rightarrow> (unit,'t) MM"

definition make_store_ops ::  "
('r \<Rightarrow> ('dnode,'t) MM) \<Rightarrow>
('dnode \<Rightarrow> ('r,'t) MM) \<Rightarrow> 
('r \<Rightarrow> 'dnode \<Rightarrow> ('r option,'t) MM) \<Rightarrow> 
('r s \<Rightarrow> (unit,'t) MM) \<Rightarrow> 
 ('r,'dnode,'t) store_ops" where
"make_store_ops r w rw f = \<lparr> read=r, wrte=w, rewrite=rw, free=f \<rparr>"




function iter_m :: "('a \<Rightarrow> ('a option,'t) MM) \<Rightarrow> 'a \<Rightarrow> ('a,'t) MM" where
"iter_m f x = (
  f x |> bind (% r.
  case r of
    None => return x
  | Some x => iter_m f x))"
apply (force)+ done
termination iter_m
 by (force intro:FIXME)


function get_tree :: "('k,'v,'leaf)leaf_ops \<Rightarrow> ('r,('k,'r,'leaf,unit)dnode,'t) store_ops \<Rightarrow> 'r \<Rightarrow> (('k,'v)tree,'t)MM" where
"get_tree leaf_ops store_ops r = (
  r |> (store_ops|>read) |> bind (% n. case n of 
  Disk_leaf kvs \<Rightarrow> return (Leaf((leaf_ops|>leaf_kvs)kvs))
  | Disk_node (ks,rs) \<Rightarrow> (
    iter_m (% (ts,rs). case rs of 
      [] \<Rightarrow> return None
      | r#rs \<Rightarrow> (
        get_tree leaf_ops store_ops r |> bind (% t. 
        return (Some(t#ts,rs)))))
      ([],rs)
    |> bind (% (ts,_).
    return (Node(ks,List.rev ts))))))"
apply (force)+ done
termination get_tree
  by (force intro:FIXME)

(* check tree wellformedness from a given root; note that the "min_size_t" argument may be
overly permissive *)
definition check_tree_at_r :: "
constants \<Rightarrow> 
'k ord \<Rightarrow>
('k,'v,'leaf) leaf_ops \<Rightarrow>
('r,('k,'r,'leaf,unit)dnode,'t) store_ops \<Rightarrow>
'r \<Rightarrow> (unit,'t)MM" where
"check_tree_at_r cs k_cmp leaf_ops store_ops r = (
  case get_check_flag () of
  False \<Rightarrow> return ()
  | True \<Rightarrow> 
    get_tree leaf_ops store_ops r |> bind (% t.
    let _ = check_true (% _. wf_tree cs (Some Small_root_node_or_leaf) k_cmp t) in
    return ()))"

end