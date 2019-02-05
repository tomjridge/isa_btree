
(** B-tree constants: minimum leaf size etc. These constants should be
    chosen so that nodes and leaves fit in a block. Clearly this
    depends on the block size, the size of keys and values, the
    on-disk format etc. *)
type constants = {
  min_leaf_size: int;
  max_leaf_size: int;
  min_node_keys: int;
  max_node_keys: int
}  [@@deriving yojson]

