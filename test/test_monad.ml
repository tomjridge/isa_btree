open Test_leaf_node_frame_impls

module State = struct
  type t = test_r
  let compare (x:t) (y:t) = Pervasives.compare x y
end

let monad_ops : State.t state_passing monad_ops = 
  state_passing_monad_ops ()

let return = monad_ops.return

let ( >>= ) = monad_ops.bind 
