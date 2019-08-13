(** Various profilers. *)

[%%import "optcomp_config.ml"]

module Internal : sig
  val leaf_profiler : int profiler
  val node_profiler : int profiler
  val frame_profiler : int profiler
end = struct


[%%if PROFILE_ISA_BTREE]
  let leaf_profiler = make_profiler ~print_header:"leaf profiler" ()
  let node_profiler = make_profiler ~print_header:"node profiler" ()
  let frame_profiler = make_profiler ~print_header:"frame profiler" ()
[%%else]
let leaf_profiler, node_profiler, frame_profiler = dummy_profiler,dummy_profiler,dummy_profiler
[%%endif]

end

include Internal
