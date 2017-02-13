(* FIXME change the following to only enable tests when some config is set *)

let run_test : ((unit -> unit) -> unit) ref = ref (fun f -> f ())

let test f = (!run_test) f
