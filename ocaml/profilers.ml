(** Various profilers. *)

module Leaf_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ()
end

module Node_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ()
end

module Frame_profiler = struct
  let { mark; time_thunk; _ } = make_profiler ()
end
