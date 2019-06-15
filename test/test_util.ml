open Tjr_fs_shared.Kv_op
open Test_monad

(* allow float representation *)
let int_of_string s = 
  float_of_string_opt s |> function
  | None -> int_of_string s
  | Some f -> int_of_float f


type ii_op = (int,int) op [@@deriving yojson]

(* let k_cmp : int -> int -> int = Int_.compare *)

let dbg_tree_at_r = fun r -> return ()

(* let map_ops : (int,int,(int,int,unit)Tjr_map.map) Tjr_map.map_ops = Tjr_map.make_map_ops k_cmp *)

