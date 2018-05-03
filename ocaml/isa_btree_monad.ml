(* A syntactic/free monad for the btree code. Later, we interpret this
   in particular monads *)

type ('k,'v,'r) frame

(* FIXME too many tyvars *)
type ('a,'k,'v,'r,'t) free =
  | Return : 'a -> ('a,'k,'v,'r,'t) free
  | Bind: ('a,'k,'v,'r,'t) free * ('a -> ('b,'k,'v,'r,'t) free) -> ('b,'k,'v,'r,'t) free
  | Store_free: 'r list -> (unit,'k,'v,'r,'t) free
  | Store_read: 'r -> (('k, 'v,'r) frame,'k,'v,'r,'t) free
  | Store_alloc: ('k, 'v,'r) frame -> ('r,'k,'v,'r,'t) free



let return x = Return x
let bind a ab = Bind (a,ab)

let store_free rs = Store_free rs
let store_read r = Store_read r
let store_alloc f = Store_alloc f


