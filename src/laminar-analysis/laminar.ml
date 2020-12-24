(* FIXME: Technically we don't even need to steal Odefa's AST? *)
(* open Odefa_ast;;

open Ast;; *)
open Batteries;;
open Utils;;
open Stack_utils;;

(* AST stuff here... *)
type ident = Ident of string [@@deriving eq, ord, show]

module Ident =
struct
  type t = ident;;
  let equal = equal_ident;;
  let compare = compare_ident;;
  let pp = pp_ident;;
  let show = show_ident;;
end;;

(* Variables in AST *)
(* NOTE: AST details mainly taken from Odefa AST - credit odefa! *)
(* NOTE: currently we just have the lambda calculus *)
type abstract_var = | Abs_var of ident [@@deriving eq, ord, show]

module Abs_var =
struct
  type t = abstract_var;;
  let equal = equal_abstract_var;;
  let compare = compare_abstract_var;;
  let pp = pp_abstract_var;;
  let show = show_abstract_var;;
end;;

type abstract_function_value =
  | Abstract_function_value of abstract_var * abstract_expr
[@@deriving eq, ord, show]

and abstract_value =
  | Abstract_value_int of int
  | Abstract_value_book of bool
  | Abstract_value_string of string
  | Abstract_value_function of abstract_function_value
[@@deriving eq, ord, show]

and abstract_clause_body =
  | Abstract_value_body of abstract_value
  | Abstract_var_body of abstract_var
  | Abstract_appl_body of abstract_var * abstract_var
[@@deriving eq, ord, show]

and abstract_clause =
  | Abstract_clause of abstract_var * abstract_clause_body
[@@deriving eq, ord, show]

and abstract_expr =
  | Abstract_expr of abstract_clause list [@@deriving eq, ord, show]
;;

module Node =
struct
  type t = abstract_var
  let equal = equal_abstract_var
  let compare = compare_abstract_var
  let pp = pp_abstract_var
  let show = show_abstract_var
end;;

type annotated_clause =
  | Unannotated_clause of abstract_clause
  | Enter_clause of abstract_var * abstract_var * abstract_clause
  | Exit_clause of abstract_var * abstract_var * abstract_clause
  | Start_clause of abstract_var
  (** This variable is the return variable of the block that this clause
      starts. *)
  | End_clause of abstract_var
  (** This variable is the return variable of the block that this clause
      ends. *)
[@@deriving ord, eq, show]
;;

(* TODO: Create the three modules for stack grammars *)
(* Module 1: Lookup stack grammar *)
module Lookup_stack_grammar =
struct
  type t =
    | LU_stack_variable of abstract_var
    | LU_stack_value of abstract_value
    | LU_stack_rewind of Node.t
      (*
      (* NOTE: skipping complicated stuff for now just for the sake of lambda calculus *)
      | Search_start (* "Capture Start" *)
      | Replace (* "Capture Target" *)
*)
    | LU_stack_rewind_stack_bottom
  [@@deriving eq, ord, show]

end;;

(* Module 1.5: Lookup Stack Grammar Predicates *)
(* NOTE: currently on bare-bones lambda calculus
   so we're only gonna check whether things are abstract_values *)
module Lookup_stack_grammar_predicates =
struct
  type t =
    | IsValue
  [@@deriving eq, ord, show]
  ;;
  module Grammar = Lookup_stack_grammar
  let exec_pred (pred : t) (l : Grammar.t) =
    match pred with
    | IsValue ->
      begin
        match l with
        | LU_stack_value _ -> true
        | _ -> false
      end
  ;;
end;;

(* Module 2: Context stack grammar *)
module Context_stack_grammar =
struct
  type t =
    | C_stack_clause of abstract_clause
  [@@deriving eq, ord, show]
  ;;
end;;

(* Creating phantom type for non-existing predicates *)
module Phantom : sig
  type t
end = struct
  type t = unit
end

(* Module 2.5: Context stack grammar predicates *)
(* NOTE: this stack doesn't have any predicates :0000 *)
module Context_stack_grammar_predicates =
struct
  (* FIXME: check this w Zach? *)
  type t = Phantom.t
  ;;
  module Grammar = Context_stack_grammar;;
  let exec_pred _ _ = raise @@ Jhupllib_utils.Invariant_failure("phantom type");;
  let equal _ _ = raise @@ Jhupllib_utils.Invariant_failure("phantom type");;
  let compare _ _ = raise @@ Jhupllib_utils.Invariant_failure("phantom type");;
  let pp _ _ = raise @@ Jhupllib_utils.Invariant_failure("phantom type");;
  let show _ = raise @@ Jhupllib_utils.Invariant_failure("phantom type");;
end;;

(* Module 3: "Rewind" stack grammar *)
module Rewinding_stack_grammar =
struct
  type t =
    | R_stack_bottom
    | R_stack_push of Context_stack_grammar.t
    | R_stack_pop of Context_stack_grammar.t
  [@@deriving eq, ord, show]
  ;;

end;;

(* Module 3.5: "Rewind" stack grammar predicates *)
module Rewinding_stack_grammar_predicates =
struct
  (* NOTE: might be useful to have. I don't remember what other predicates were
     supposed to go for this stack but I'll remember it at some point hopefully *)
  type t =
    | IsBottomOfStack
  [@@deriving eq, ord, show]
  ;;
  module Grammar = Rewinding_stack_grammar;;
  let exec_pred (pred : t) (r : Grammar.t) =
    match pred with
    | IsBottomOfStack ->
      match r with
      | R_stack_bottom -> true
      | _ -> false
end;;

module Graph_Label :
  Decorated_type
  with type t = ( (Lookup_stack_grammar.t, Lookup_stack_grammar_predicates.t) stack_action,
                  (Context_stack_grammar.t, Context_stack_grammar_predicates.t) stack_action,
                  (Rewinding_stack_grammar.t, Rewinding_stack_grammar_predicates.t) stack_action) trinary
=
struct
  type t =
    (( (Lookup_stack_grammar.t, Lookup_stack_grammar_predicates.t) stack_action,
       (Context_stack_grammar.t, Context_stack_grammar_predicates.t) stack_action,
       (Rewinding_stack_grammar.t, Rewinding_stack_grammar_predicates.t) stack_action) trinary)
  [@@deriving eq, ord];;
  let pp _ _ = raise @@ Jhupllib_utils.Not_yet_implemented("need to write pp for user graph label");;
  let show _ = "";;

end;;

(* User graph *)
module Graph = Graph_types.Make(Node)(Graph_Label);;

module LCL_reachability_engine =
  Three_stack_reachability.Make(Lookup_stack_grammar)
    (Lookup_stack_grammar_predicates)
    (Context_stack_grammar)
    (Context_stack_grammar_predicates)
    (Rewinding_stack_grammar)
    (Rewinding_stack_grammar_predicates)
    (Graph)
;;

type analysis =
  { graph : Graph.t;
    lcl_reachability : LCL_reachability_engine.summary
  }
;;

(* TODO: Function for turning AST into LRA - need to pull up Odefa AST *)
let create_initial_analysis (_ : abstract_expr) : analysis =
  raise @@ Jhupllib_utils.Not_yet_implemented "Not quite sure how this is going to look in terms of code"
  (* match e with
  | Abstract_expr (c_list) -> *)
  (* We're gonna flip the clause list so that we can work from the back. *)
    (* let rev_c_list = List.rev c_list in
    let setup_fun (c : abstract_clause) *)
;;

(* TODO: Function for cranking the Inner reachability engine once and adding necessary things *)
let step (a : analysis) : analysis option =
  (* raise @@ Jhupllib_utils.Not_yet_implemented "I think I need a refresher on what examine is supposed to do" *)
  (* crank the inner engine until we hit closure *)
  let new_lcl_reachability = LCL_reachability_engine.step_to_closure a.lcl_reachability in
  (* we need to iterate over all nodes and see what we can extend through examine? *)
  let current_nodes = Graph.node_set in
  (* Function to go into outer fold *)
  let new_subgraph_builder (acc : Graph.t) (n : Node.t) =
    let examine_reachable_nodes = LCL_reachability_engine.get_examine_result_nodes n new_lcl_reachability in

  in

;;

(* TODO: Closure over above function *)

(* TODO: Function asking what is reachable *)
