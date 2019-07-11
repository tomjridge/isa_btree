(** Various profilers. Profilers are controlled by a flag. *)

[%%define PROFILING_ENABLED true]

[%%if PROFILING_ENABLED]

(** Profiling is ENABLED! *)
let profiling_enabled = true
let _ = Tjr_profile_with_core.initialize()
[%%else]

(** Profiling is DISABLED! *)
let profiling_enabled = false
[%%endif]

module Make_profiler() = 
struct
[%%if PROFILING_ENABLED]
let internal_profiler = Tjr_profile.make_string_profiler ()
let mark = internal_profiler.mark
let profile s f = mark s; f() |> fun r -> mark (s^"'"); r
[%%else]
let mark (s:string) = () 
let profile s f = f ()
[%%endif]
end

module Leaf_profiler = Make_profiler()

module Node_profiler = Make_profiler()

module Frame_profiler = Make_profiler()
