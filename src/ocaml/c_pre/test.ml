(* FIXME change the following to only enable tests when some config is set *)

let run_test : ((unit -> unit) -> unit) ref = ref (fun f -> f ())

let test f = (!run_test) f

let enable () = run_test := fun f -> f()
let disable () = run_test := fun f -> ()
