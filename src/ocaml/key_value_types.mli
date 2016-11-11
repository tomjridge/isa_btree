open Gen_isa

module type T = sig
  type key
  val equal_keya : key -> key -> bool
  val equal_key : key HOL.equal
  type value_t
  val equal_value_ta : value_t -> value_t -> bool
  val equal_value_t : value_t HOL.equal
  val key_ord : key -> key -> Arith.int
end
