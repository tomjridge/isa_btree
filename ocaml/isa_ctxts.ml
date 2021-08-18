(** This ctxt gives us enough to construct the node leaf and leaf_stream types *)

(*
module type C_kvr = sig
  type k
  type v
  type r
  (* type t *)

  type k_cmp (* singleton type *)
  val k_cmp: (k_cmp,k -> k -> int)sng

(*
  val monad_ops: t monad_ops
  val ( >>= ) : ('a, t) m -> ('a -> ('b, t) m) -> ('b, t) m
  val return : 'a -> ('a, 't) m
*)

  type cs (* singleton type *)
  val cs: (cs,Constants.constants)sng
end
*)
