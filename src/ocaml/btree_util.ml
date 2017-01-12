(* general util stuff ---------------------------------------- *)

module Set_int = Set.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)

module Map_int = Map.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)



