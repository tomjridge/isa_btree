(** Map ops for the spec (an int->int map) *)

let k_cmp : int -> int -> int = Pervasives.compare

let spec_map_ops : (int,int,(int,int,unit)Tjr_map.map) Tjr_map.map_ops = Tjr_map.make_map_ops k_cmp
