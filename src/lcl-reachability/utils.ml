(* Generic type for node, etc. Basically the same as Decorated_type *)
module type Decorated_type =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  (* insert pretty printer? *)
  val show : t -> string
  val pp : Format.formatter -> t -> unit
end;;
