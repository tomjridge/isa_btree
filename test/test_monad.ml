open Test_leaf_node_frame_impls

module State = struct
  type t = test_r

  let compare (x:t) (y:t) = Pervasives.compare x y  
  (** Needed for exhaustive testing; but likely not correct since test implementations use balanced trees which may not have unique representatives for a given map. *)

end

let monad_ops : State.t state_passing monad_ops = 
  state_passing_monad_ops ()

let return = monad_ops.return

let ( >>= ) = monad_ops.bind 
