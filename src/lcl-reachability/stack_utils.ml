open Utils;;

(* Data type signature for our stack grammars*)
module type Stack_grammar =
sig
  include Decorated_type;;
  val alphabet : t list
end;;

(* equivalent to Haskell Either *)
type ('a, 'b) choice =
  | Left of 'a
  | Right of 'b
[@@deriving eq, ord, show]
;;

type ('a) stack_action =
  | Push of 'a
  | Pop of 'a
  | Epsilon
[@@deriving eq, ord, show]
;;
