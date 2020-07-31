open Utils;;

(* Data type signature for our stack grammars*)
module type Stack_grammar =
sig
  include Decorated_type;;
end;;

module type StackElementPredicates =
sig
    type t;;
    module Grammar : Stack_grammar;;
    val exec_pred : t -> Grammar.t -> bool;;
    (*FIXME: check this w Zach, there might be a better way to do this? *)
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val show : t -> string
    val pp : Format.formatter -> t -> unit;;
end;;

(* equivalent to Haskell Either *)
type ('a, 'b) choice =
  | Left of 'a
  | Right of 'b
[@@deriving eq, ord, show]
;;

type ('a,'b,'c) trinary =
  | First of 'a
  | Second of 'b
  | Third of 'c
[@@deriving eq, ord, show]
;;

(* TODO: check w zach if there is a better way to do this for Examine *)
type stack_specification =
  | First_stack
  | Second_stack
  | Third_stack
[@@deriving eq, ord, show]
;;

type ('a) stack_action_lcl =
  | Push of 'a
  | Pop of 'a
  | Epsilon
[@@deriving eq, ord, show]
;;

type ('element, 'predicate) stack_action =
  (* 'a is a stack element, 'b is a predicate *)
  | Push of 'element
  | Pop of 'element
  | Epsilon
  | PeekEq of 'element
  | PeekNeq of 'element
  | PeekPred of 'predicate list
  | SearchAndReplace of 'predicate * 'predicate * 'predicate
  | Examine
[@@deriving eq, ord, show]
;;
