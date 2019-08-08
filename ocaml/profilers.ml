(** Various profilers. *)

module Leaf_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ~print_header:"leaf profiler" ()
end

module Node_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ~print_header:"node profiler" ()
end

module Frame_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ~print_header:"frame profiler" ()
end
