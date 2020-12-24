open Batteries;;

open Graph_types;;
open Jhupllib.Logger_utils;;
open Jhupllib.Nondeterminism;;
open Stack_utils;;
open Utils;;

let logger = make_lazy_logger "Three_stack_reachability";;

(* Data type for module for constructing graph and computing the reachability
   question for a three-stack. *)
module type ThreeStackReachability =
sig
  (* The left grammar is the one that *needs* to be  *)
  module Stack1 : Stack_grammar
  module Stack2 : Stack_grammar
  module Stack3 : Stack_grammar
  module Predicate1 : StackElementPredicates
  module Predicate2 : StackElementPredicates
  module Predicate3 : StackElementPredicates
  module G : Graph
    with type Label.t = ( ((Stack1.t, Predicate1.t) stack_action,
                           (Stack2.t, Predicate2.t) stack_action,
                           (Stack3.t, Predicate3.t) stack_action ) trinary)

  (* Summary of three-stack graph *)
  type summary

  val create_initial_summary : G.t -> summary

  val step : summary -> summary option

  val step_to_closure : summary -> summary

  val reachable : G.Node.t -> G.Node.t -> summary -> bool

  val get_reachable_nodes : G.Node.t -> summary -> G.Node.t Enum.t

  (* retuns pair btwn G.Node.t and a stack grammar trinary *)
  val get_examine_result_nodes : G.Node.t -> summary ->
    (G.Node.t * ((Stack1.t, Stack2.t, Stack3.t) trinary)) Enum.t

  (* Adds edge to (inner) graph routine so that outside system can add edges after examining *)
  val add_new_edge :  G.edge -> summary -> summary

  val add_new_subgraph : G.t -> summary -> summary

end;;

module Make
    (SG1 : Stack_grammar)
    (P1 : StackElementPredicates with module Grammar = SG1)
    (SG2 : Stack_grammar)
    (P2 : StackElementPredicates with module Grammar = SG2)
    (SG3 : Stack_grammar)
    (P3 : StackElementPredicates with module Grammar = SG3)
    (G : Graph
     with type Label.t = ( (SG1.t, P1.t) stack_action,
                           (SG2.t, P2.t) stack_action,
                           (SG3.t, P3.t) stack_action ) trinary
    )
  : ThreeStackReachability
    with module Stack1 = SG1
     and module Stack2 = SG2
     and module Stack3 = SG3
     and module Predicate1 = P1
     and module Predicate2 = P2
     and module Predicate3 = P3
     and module G = G
=
struct
  module Stack1 = SG1
  module Stack2 = SG2
  module Stack3 = SG3
  module Predicate1 = P1
  module Predicate2 = P2
  module Predicate3 = P3
  module G = G (* User graph *)

  (* Pretty-printing for differentiating between grammars *)
  let _pp_grammar formatter (c : ('a, 'b, 'c) trinary) =
    match c with
    | First(x) ->
      Format.pp_print_string formatter "ɣ" ;
      SG1.pp formatter x
    | Second(x) ->
      Format.pp_print_string formatter "ψ";
      SG2.pp formatter x
    | Third(x) ->
      Format.pp_print_string formatter "θ" ;
      SG3.pp formatter x
  ;;

  (* Pretty-printing for differentiating between grammars *)
  let _pp_grammar_non_first_stack formatter (choice : ('a, 'b) choice) =
    match choice with
    | Left(x) ->
      Format.pp_print_string formatter "⦇" ;
      SG2.pp formatter x
    | Right(x) ->
      Format.pp_print_string formatter "⟦" ;
      SG3.pp formatter x
  ;;


  (* NOTE: old version of _pp_grammar2 where we only had two stacks *)
  (* let _pp_grammar2 formatter (choice : ('a, 'b) choice) =
     match choice with
     | Left(x) ->
      Format.pp_print_string formatter "⦇" ;
      SG2.pp formatter x
     | Right(x) ->
      Format.pp_print_string formatter "⟦" ;
      SG3.pp formatter x *)

  let _pp_preds formatter (p : ('a, 'b, 'c) trinary) =
    match p with
    | First(x) ->
      Format.pp_print_string formatter "STACK 1 PREDICATE ";
      P1.pp formatter x
    | Second(x) ->
      Format.pp_print_string formatter "STACK 2 PREDICATE ";
      P2.pp formatter x
    | Third(x) ->
      Format.pp_print_string formatter "STACK 3 PREDICATE ";
      P3.pp formatter x
  ;;

  type some_stack_element = (Stack1.t, Stack2.t, Stack3.t) trinary
  [@@deriving ord, eq]
  ;;

  type dstm_op =
    | NoOp
    | Pop of some_stack_element
    | PeekEq of some_stack_element
    | PeekNeq of some_stack_element
    | PeekPred of ((Predicate1.t list, Predicate2.t list, Predicate3.t list) trinary)
    (* ↑ list allows for multiple queries. When we get to [] we switch to NoOP *)
    | SearchAndReplaceStep1 of ((Predicate1.t * Predicate1.t * Predicate1.t),
                                (Predicate2.t * Predicate2.t * Predicate2.t),
                                (Predicate3.t * Predicate3.t * Predicate3.t)) trinary
    (* ↑ the first predicate is making sure that the element on the top of the
       stack is the element we want to capture.*)
    | SearchAndReplaceStep2 of ((Stack1.t * Predicate1.t * Predicate1.t),
                                (Stack2.t * Predicate2.t * Predicate2.t),
                                (Stack3.t * Predicate3.t * Predicate3.t)) trinary
    (* ↑ Stack Element is what we want to capture... now we're trying to make sure
       that the current topmost element on stack is a "Search" *)
    | SearchAndReplaceStep3 of ((Stack1.t * Predicate1.t),
                                (Stack2.t * Predicate2.t),
                                (Stack3.t * Predicate3.t)) trinary
    (* ↑ We're looking for a "Replace".*)
    | Examine of stack_specification
    | ExamineResult of some_stack_element (* Eternal stuck-ness *)
  [@@deriving ord, eq]
  ;;

  type dstm_state = { dstm_complete: bool;
                      dstm_operation: dstm_op
                    }
  [@@deriving ord, eq];;

  (* Pretty-printing DSTM operation. Used in pp_dstm_state *)
  let pp_dstm_op formatter dstm_op =
    match dstm_op with
    | NoOp -> Format.pp_print_string formatter "NoOp"
    | Pop (x) ->
      _pp_grammar formatter x
    | PeekEq (x) ->
      Format.pp_print_string formatter "Peek ";
      _pp_grammar formatter x
    | PeekNeq (x) ->
      Format.pp_print_string formatter "Peek Not Eq ";
      _pp_grammar formatter x
    | PeekPred _ ->
      (* FIXME: couldn't quickly figure out a way to print a list of predicates... *)
      Format.pp_print_string formatter "Peek Predicate ";
      (* _pp_preds formatter x; *)
    | Examine (o) ->
      let s =
        match o with
        | First_stack -> "First Stack (Lookup Stack)"
        | Second_stack -> "Second Stack (Context Stack)"
        | Third_stack -> "Third Stack (Rewind Stack)"
      in
      Format.pp_print_string formatter ("Examine " ^ s)
    | SearchAndReplaceStep1 _ ->
      Format.pp_print_string formatter "SAR1"
    | SearchAndReplaceStep2 _ ->
      Format.pp_print_string formatter "SAR2"
    | SearchAndReplaceStep3 _ ->
      Format.pp_print_string formatter "SAR3"
    | ExamineResult (x) ->
      Format.pp_print_string formatter "Examine Result ";
      _pp_grammar formatter x
  ;;

  let pp_dstm_state formatter dstm_state =
    let str =
      if (dstm_state.dstm_complete) then "Complete - "
      else
        "Incomplete - "
    in
    Format.pp_print_string formatter str;
    pp_dstm_op formatter (dstm_state.dstm_operation);
  ;;

  module Dstm_state =
  struct
    type t = dstm_state [@@deriving ord, show]
  end;;

  type dstm_tape_val =
    | TapeStackElement of some_stack_element
    | TapeHash
  [@@deriving ord, eq]

  let pp_dstm_tape_val formatter tape_val =
    match tape_val with
    | TapeStackElement (x) ->
      _pp_grammar formatter x
    | TapeHash ->
      Format.pp_print_char formatter '#'

  module Dstm_tape_val =
  struct
    type t = dstm_tape_val [@@deriving ord, show]
  end;;

  type edge_type =
    | Original
    | Summary
  [@@deriving ord, eq]
  ;;

  let pp_edge_type formatter edge =
    match edge with
    | Original ->
      Format.pp_print_string formatter "T"
    | Summary ->
      Format.pp_print_string formatter "⊥"
  ;;

  module N = G.Node;;
  module L : Decorated_type with type t = (dstm_state * dstm_tape_val * edge_type) =
  struct
    type t = (dstm_state * dstm_tape_val * edge_type)
    [@@deriving ord, eq]
    let pp formatter (s, t, e) =
      Format.pp_print_string formatter "〈" ;
      pp_dstm_state formatter s ;
      Format.pp_print_string formatter ", " ;
      pp_dstm_tape_val formatter t;
      Format.pp_print_string formatter ", " ;
      pp_edge_type formatter e;
      Format.pp_print_string formatter "〉" ;
    ;;
    let show p =
      Jhupllib.Pp_utils.pp_to_string pp p
    ;;
  end;;

  module Reachability_graph = Graph_types.Make(N)(L);;

  module Node_pair =
  struct
    type t = (N.t * N.t) [@@deriving ord, show]
  end;;

  module Node_pair_to_Dstm_tape_val_multimap =
  struct
    module Impl = Jhupllib.Multimap.Make(Node_pair)(Dstm_tape_val);;
    include Impl;;
    include Jhupllib.Multimap_pp.Make(Impl)(Node_pair)(Dstm_tape_val);;
  end;;

  module Node_pair_to_Dstm_state_multimap =
  struct
    module Impl = Jhupllib.Multimap.Make(Node_pair)(Dstm_state);;
    include Impl;;
    include Jhupllib.Multimap_pp.Make(Impl)(Node_pair)(Dstm_state);;
  end;;

  module Node_Label_pair =
  struct
    type t = (N.t * L.t) [@@deriving ord, show]
  end;;

  module Node_NL_set_multimap =
  struct
    module Impl = Jhupllib.Multimap.Make(N)(Node_Label_pair);;
    include Impl;;
    include Jhupllib.Multimap_pp.Make(Impl)(N)(Node_Label_pair);;
  end;;

  type summary =
    {
      graph : Reachability_graph.t;
      worklist : Reachability_graph.edge list;
      incoming_og_edges_map : Node_NL_set_multimap.t;
      outgoing_og_edges_map : Node_NL_set_multimap.t;
    } [@@deriving show];;
  let _ = pp_summary;;

  let og_edge_conversion (e : G.edge) : Reachability_graph.edge =
    let l = e.G.label in
    let new_label =
      match l with
      | First (sa) ->
        begin
          match sa with
          | Push (x) ->
            let push_dstm_state =
              { dstm_complete = false; dstm_operation = NoOp}
            in
            (push_dstm_state, TapeStackElement(First(x)), Original)
          | Pop (x) ->
            let pop_dstm_state =
              { dstm_complete = true; dstm_operation = Pop(First(x))}
            in
            (pop_dstm_state, TapeHash, Original)
          | Epsilon ->
            (* We are just happy w all Epsilons. They are just there. Very wholesome *)
            let epsilon_dstm_state =
              { dstm_complete = true; dstm_operation = NoOp}
            in
            (epsilon_dstm_state, TapeHash, Original)
          | PeekEq (x) ->
            let peekeq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekEq(First(x))}
            in
            (peekeq_dstm_state, TapeHash, Original)
          | PeekNeq (x) ->
            let peekneq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekNeq(First(x))}
            in
            (peekneq_dstm_state, TapeHash, Original)
          | PeekPred (p) ->
            let peekpred_dstm_state =
              { dstm_complete = true; dstm_operation = PeekPred(First(p))}
            in
            (peekpred_dstm_state, TapeHash, Original)
          | SearchAndReplace (p1, p2, p3) ->
            let sar_dstm_state =
              { dstm_complete = true; dstm_operation = SearchAndReplaceStep1(First(p1, p2, p3))}
            in
            (sar_dstm_state, TapeHash, Original)
          | Examine ->
            let examine_dstm_state =
              { dstm_complete = true; dstm_operation = Examine(First_stack)}
            in
            (examine_dstm_state, TapeHash, Original)
        end
      | Second (sa) ->
        begin
          match sa with
          | Push (x) ->
            let push_dstm_state =
              { dstm_complete = false; dstm_operation = NoOp}
            in
            (push_dstm_state, TapeStackElement(Second(x)), Original)
          | Pop (x) ->
            let pop_dstm_state =
              { dstm_complete = true; dstm_operation = Pop(Second(x))}
            in
            (pop_dstm_state, TapeHash, Original)
          | Epsilon ->
            (* We are just happy w all Epsilons. They are just there. Very wholesome *)
            let epsilon_dstm_state =
              { dstm_complete = true; dstm_operation = NoOp}
            in
            (epsilon_dstm_state, TapeHash, Original)
          | PeekEq (x) ->
            let peekeq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekEq(Second(x))}
            in
            (peekeq_dstm_state, TapeHash, Original)
          | PeekNeq (x) ->
            let peekneq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekNeq(Second(x))}
            in
            (peekneq_dstm_state, TapeHash, Original)
          | PeekPred (p) ->
            let peekpred_dstm_state =
              { dstm_complete = true; dstm_operation = PeekPred(Second(p))}
            in
            (peekpred_dstm_state, TapeHash, Original)
          | SearchAndReplace (p1, p2, p3) ->
            let sar_dstm_state =
              { dstm_complete = true; dstm_operation = SearchAndReplaceStep1(Second(p1, p2, p3))}
            in
            (sar_dstm_state, TapeHash, Original)
          | Examine ->
            let examine_dstm_state =
              { dstm_complete = true; dstm_operation = Examine(Second_stack)}
            in
            (examine_dstm_state, TapeHash, Original)
        end
      | Third (sa) ->
        begin
          match sa with
          | Push (x) ->
            let push_dstm_state =
              { dstm_complete = false; dstm_operation = NoOp}
            in
            (push_dstm_state, TapeStackElement(Third(x)), Original)
          | Pop (x) ->
            let pop_dstm_state =
              { dstm_complete = true; dstm_operation = Pop(Third(x))}
            in
            (pop_dstm_state, TapeHash, Original)
          | Epsilon ->
            (* We are just happy w all Epsilons. They are just there. Very wholesome *)
            let epsilon_dstm_state =
              { dstm_complete = true; dstm_operation = NoOp}
            in
            (epsilon_dstm_state, TapeHash, Original)
          | PeekEq (x) ->
            let peekeq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekEq(Third(x))}
            in
            (peekeq_dstm_state, TapeHash, Original)
          | PeekNeq (x) ->
            let peekneq_dstm_state =
              { dstm_complete = true; dstm_operation = PeekNeq(Third(x))}
            in
            (peekneq_dstm_state, TapeHash, Original)
          | PeekPred (p) ->
            let peekpred_dstm_state =
              { dstm_complete = true; dstm_operation = PeekPred(Third(p))}
            in
            (peekpred_dstm_state, TapeHash, Original)
          | SearchAndReplace (p1, p2, p3) ->
            let sar_dstm_state =
              { dstm_complete = true; dstm_operation = SearchAndReplaceStep1(Third(p1, p2, p3))}
            in
            (sar_dstm_state, TapeHash, Original)
          | Examine ->
            let examine_dstm_state =
              { dstm_complete = true; dstm_operation = Examine(Third_stack)}
            in
            (examine_dstm_state, TapeHash, Original)
        end
    in
    {
      Reachability_graph.source = e.G.source;
      Reachability_graph.target = e.G.target;
      Reachability_graph.label = new_label
    }
  ;;

  (* This function is the function we pass into fold for create_initial_summary,
     and I'm using pairs so that we only go through one pass, but I'm not quite
     sure if this is the best thing to do? *)
  let worklist_map_setup_fun
      (acc : (Reachability_graph.edge list * Node_NL_set_multimap.t * Node_NL_set_multimap.t))
      (new_edge : Reachability_graph.edge)
    : Reachability_graph.edge list * Node_NL_set_multimap.t * Node_NL_set_multimap.t =
    let (worklist_acc, incoming_acc, outgoing_acc) = acc in
    let w = List.append worklist_acc [new_edge] in
    let srclab_pair = (new_edge.source, new_edge.label) in
    let im =
      Node_NL_set_multimap.add new_edge.target srclab_pair incoming_acc
    in
    let tgtlab_pair = (new_edge.target, new_edge.label) in
    let om =
      Node_NL_set_multimap.add new_edge.source tgtlab_pair outgoing_acc
    in
    (w, im, om)
  ;;

  let create_initial_summary (input_graph : G.t) : summary =
    (* 1. Get all of the edges in the original graph *)
    let og_edges = G.get_all_edges input_graph in
    let reachability_edges =
      og_edges
      |> Enum.map og_edge_conversion
      |> List.of_enum
    in
    (* 2. For each edge, create edge in new graph *)
    (* 3. For each edge, we add it to both incoming and outgoing og edge multimaps
       for faster lookup *)
    let (new_worklist, new_incoming_og_map, new_outgoing_og_map) =
      List.fold_left
        worklist_map_setup_fun
        ([], Node_NL_set_multimap.empty, Node_NL_set_multimap.empty)
        reachability_edges
    in
    {
      graph = Reachability_graph.empty;
      worklist = new_worklist;
      incoming_og_edges_map = new_incoming_og_map;
      outgoing_og_edges_map = new_outgoing_og_map;
    }
  ;;

  (* Function that finds new symbols based on rules described by chart
     - q : the R-value to be considered
     - z : the L-value to be considered
  *)
  let find_rule (q : dstm_state) (z : dstm_tape_val) : (dstm_state * dstm_tape_val) option =
    match q.dstm_operation with
    | NoOp ->
      if q.dstm_complete then (* G *)
        (match z with
         | TapeHash -> Some (q, z)
         | TapeStackElement (s) ->
           begin
             match s with
             | First _ -> (* Still sth on the first stack --> B *)
               Some ({q with dstm_complete = false}, z)
             | Second _ | Third _ ->
               Some (q, z)
           end
        )
      else
        Some (q, z) (* B *)
    | Pop (sym) ->
      begin
        match sym with
        | First (q_fst) -> (* col D *)
          (
            match z with
            | TapeHash -> Some (q, z)
            | TapeStackElement (tse) ->
              (match tse with
               | First (tse_fst) ->
                 if (q_fst = tse_fst) then (* D3 *)
                   (* NOTE: bc this is first stack, q.dstm_complete should be set to true
                      but we will proceed w caution for now *)
                   Some ({ dstm_complete = true; dstm_operation = NoOp}, TapeHash)
                 else
                   None
               | Second _ | Third _ ->
                 Some (q, z) (* D8, D9 *)
              )
          )
        | Second (q_snd) -> (* col M, N *)
          (
            match z with
            | TapeHash -> Some (q, z)
            | TapeStackElement (tse) ->
              (match tse with
               | First _ -> (* M3, also N3 but trivial *)
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) -> (* M *)
                 if (q_snd = tse_snd) then
                   Some ({q with dstm_operation = NoOp}, TapeHash)
                 else None
               | Third _ ->
                 Some (q, z)
              )
          )
        | Third (q_thd) ->
          (
            match z with
            | TapeHash -> Some (q, z)
            | TapeStackElement (tse) ->
              (match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second _ ->
                 Some (q, z)
               | Third (tse_thd) ->
                 if (q_thd = tse_thd) then
                   Some ({q with dstm_operation = NoOp}, TapeHash)
                 else None
              )
          )
      end
    | PeekEq (sym) ->
      begin
        match sym with
        | First (q_fst) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_fst) ->
                 if (q_fst = tse_fst) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Second _ | Third _ ->
                 Some (q, z)
             end
          )
        | Second (q_snd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if (q_snd = tse_snd) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Third _ -> Some (q, z)
             end
          )
        | Third (q_thd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if (q_thd = tse_thd) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Second _ -> Some (q, z)
             end
          )
      end
    | PeekNeq (sym) ->
      begin
        match sym with
        | First (q_fst) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_fst) ->
                 if (not (q_fst = tse_fst)) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Second _ | Third _ ->
                 Some (q, z)
             end
          )
        | Second (q_snd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if (not (q_snd = tse_snd)) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Third _ -> Some (q, z)
             end
          )
        | Third (q_thd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if (not (q_thd = tse_thd)) then
                   Some ({q with dstm_operation = NoOp}, z)
                 else None
               | Second _ -> Some (q, z)
             end
          )
      end
    | PeekPred (preds) ->
      begin
        match preds with
        | First (preds_fst) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_fst) ->
                 if Predicate1.exec_pred (List.hd preds_fst) tse_fst
                 then (* We need to see if the list is done *)
                   (let preds_tl = List.tl preds_fst in
                    if (List.is_empty @@ preds_tl)
                    then (* We are done *)
                      Some ({q with dstm_operation = NoOp}, z)
                    else (* We proceed with the rest of the list *)
                      Some ({q with dstm_operation = PeekPred(First(preds_tl))}, z)
                   )
                 else None
               | Second _ | Third _ -> Some (q, z)
             end
          )
        | Second (preds_snd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if Predicate2.exec_pred (List.hd preds_snd) tse_snd
                 then (* We need to see if the list is done *)
                   (let preds_tl = List.tl preds_snd in
                    if (List.is_empty @@ preds_tl)
                    then (* We are done *)
                      Some ({q with dstm_operation = NoOp}, z)
                    else (* We proceed with the rest of the list *)
                      Some ({q with dstm_operation = PeekPred(Second(preds_tl))}, z)
                   )
                 else None
               | Third _ -> Some (q, z)
             end
          )
        | Third (preds_thd) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if Predicate3.exec_pred (List.hd preds_thd) tse_thd
                 then (* We need to see if the list is done *)
                   (let preds_tl = List.tl preds_thd in
                    if (List.is_empty @@ preds_tl)
                    then (* We are done *)
                      Some ({q with dstm_operation = NoOp}, z)
                    else (* We proceed with the rest of the list *)
                      Some ({q with dstm_operation = PeekPred(Third(preds_tl))}, z)
                   )
                 else None
               | Second _ -> Some (q, z)
             end
          )
      end
    | SearchAndReplaceStep1 (t) ->
      begin
        match t with
        | First (p1, p2, p3) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_fst) ->
                 if Predicate1.exec_pred p1 tse_fst
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep2(First(tse_fst, p2, p3))}, TapeHash)
                 else None (* topmost stack element didn't fit the predicate, we blow up *)
               | Second _ | Third _ -> Some (q, z)
             end
          )
        | Second (p1, p2, p3) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if Predicate2.exec_pred p1 tse_snd
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep2(Second(tse_snd, p2, p3))}, TapeHash)
                 else None (* topmost stack element didn't fit the predicate, we blow up *)
               | Third _ -> Some (q, z)
             end
          )
        | Third (p1, p2, p3) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if Predicate3.exec_pred p1 tse_thd
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep2(Third(tse_thd, p2, p3))}, TapeHash)
                 else None (* topmost stack element didn't fit the predicate, we blow up *)
               | Second _ -> Some (q, z)
             end
          )
      end
    | SearchAndReplaceStep2 (t) ->
      begin
        match t with
        | First (se, p1, p2) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_fst) ->
                 if Predicate1.exec_pred p1 tse_fst (* If topmost stack element fits "search" predicate *)
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep3(First(se, p2))}, TapeHash)
                 else None
               | Second _ | Third _ -> Some (q, z)
             end
          )
        | Second (se, p1, p2) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if Predicate2.exec_pred p1 tse_snd (* If topmost stack element fits "search" predicate *)
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep3(Second(se, p2))}, TapeHash)
                 else None
               | Third _ -> Some (q, z)
             end
          )
        | Third (se, p1, p2) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if Predicate3.exec_pred p1 tse_thd (* If topmost stack element fits "search" predicate *)
                 then
                   Some ({q with dstm_operation = SearchAndReplaceStep3(Third(se, p2))}, TapeHash)
                 else None
               | Second _ -> Some (q, z)
             end
          )
      end
    | SearchAndReplaceStep3 t ->
      (* We're almost done w our Search and Replace...
         If a stack element fits the "Replace" predicate, then we
         replace the current tape symbol with the stack element we've been carrying
         NOTE: some points to keep in mind
         - We can scream about the first stack while replacing on the first stack
         - This Doesn't have to be the topmost element (no blowing up)
      *)
      begin
        match t with
        | First (se, p) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First (tse_first) ->
                 if Predicate1.exec_pred p tse_first
                 then (* Replace *)
                   Some ({q with dstm_operation = NoOp}, TapeStackElement(First(se)))
                 else (* THIS IS VALID, keep on with the search *)
                   (* BUT scream about first stack *)
                   Some ({q with dstm_complete = false}, z)
               | Second _ | Third _ -> Some (q, z)
             end
          )
        | Second (se, p) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ -> Some ({q with dstm_complete = false}, z)
               | Second (tse_snd) ->
                 if Predicate2.exec_pred p tse_snd
                 then (* Replace *)
                   Some ({q with dstm_operation = NoOp}, TapeStackElement(Second(se)))
                 else (* THIS IS VALID, keep on with the search *)
                   Some (q, z)
               | Third _ -> Some (q, z)
             end
          )
        | Third (se, p) ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ -> Some ({q with dstm_complete = false}, z)
               | Third (tse_thd) ->
                 if Predicate3.exec_pred p tse_thd
                 then (* Replace *)
                   Some ({q with dstm_operation = NoOp}, TapeStackElement(Third(se)))
                 else (* THIS IS VALID, keep on with the search *)
                   Some (q, z)
               | Second _ -> Some (q, z)
             end
          )
      end
    | Examine (stack_spec) ->
      begin
        match stack_spec with
        | First_stack ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | First _ ->
                 Some ({q with dstm_operation = ExamineResult (tse)}, z)
               | Second _ | Third _ -> Some (q, z)
             end
          )
        | Second_stack ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | Second _ ->
                 Some ({q with dstm_operation = ExamineResult (tse)}, z)
               | First _ | Third _ -> Some (q, z)
             end
          )
        | Third_stack ->
          (match z with
           | TapeHash -> Some (q, z)
           | TapeStackElement (tse) ->
             begin
               match tse with
               | Third _ ->
                 Some ({q with dstm_operation = ExamineResult (tse)}, z)
               | Second _ | First _ -> Some (q, z)
             end
          )
      end
    | ExamineResult _ -> Some (q, z) (* we are just... stuck. *)
  ;;

  (* NOTE: old version Function that finds new symbols based on rules described by chart
     - q : the R-value to be considered
     - z : the L-value to be considered
  *)
  (* let find_rule (q : dstm_state) (z : dstm_tape_val) : (dstm_state * dstm_tape_val) option =
     match q with
     | Incomplete ->
      Some (q, z) (* column C *)
     | Complete ->
      (match z with
       | TapeHash ->
         Some (Complete, TapeHash) (* cell B2 *)
       | TapeSymbol(s) ->
         match s with
         | First _ ->
           Some (Incomplete, z) (* cell B3 *)
         | _ ->
           Some (Complete, z) (* cell B4, B5 *)
      )
     | IncompletePop (sym) -> (* column N and T *)
      begin
        match sym with
        | Left (q_psi) -> (* column N - ψB *)
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | Second (ts_psi) ->
                if (q_psi = ts_psi) then (* cell N8 *)
                  Some (Incomplete, TapeHash)
                else None
              | _ ->
                Some (q, z) (* cell N3, N9 *)
             )
           | TapeHash ->
             Some (q, z) (* cell N2 *)
          )
        | Right(q_theta) -> (* column T - θB *)
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | Third (ts_theta) ->
                if (q_theta = ts_theta) then (* cell T9 *)
                  Some (Incomplete, TapeHash)
                else None
              | _ -> Some (q, z) (* cell T3, T8 *)
             )
           | TapeHash -> Some (q, z) (* cell T2 *)
          )
      end
     | Pop (sym) ->
      begin
        match sym with
        | First (q_gamma) -> (* column D *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell D2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | First (ts_gamma) ->
                 if (q_gamma = ts_gamma) then (* cell D3 *)
                   Some (Complete, TapeHash)
                 else
                   None
               | _ ->
                 Some (Pop (sym), z) (* cell D8, D9 *)
              )
          )
        | Second (q_psi) -> (* column M *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell M2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | First _ ->
                 Some (IncompletePop (Left (q_psi)), z) (* cell M3 *)
               | Second (ts_psi) ->
                 if (q_psi = ts_psi) then (* cell M8 *)
                   Some (Complete, TapeHash)
                 else
                   None
               | Third _ ->
                 Some (Pop (sym), z) (* cell M9 *)
              )
          )
        | Third (q_theta) -> (* column S *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell S2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | Third (ts_theta) ->
                 if (q_theta = ts_theta) then (* cell S9 *)
                   Some (Complete, TapeHash)
                 else None
               | First _ ->
                 Some (IncompletePop (Right (q_theta)), z) (* cell G3 *)
               | Second _ ->
                 Some (Pop (sym), z) (* cell G4 *)
              )
          )
      end
     | _ -> raise @@ Jhupllib.Utils.Not_yet_implemented "working on it"
     ;; *)

  (* let generate_worklist_item_map (worklist : worklist_item list)
     : unit
     =
     let new_map =
      List.fold_left (fun map -> fun item ->
          let curr_num =
            if (Worklist_item_map.mem item map) then
              Worklist_item_map.find item map
            else 0 in
          Worklist_item_map.add item (curr_num + 1) map
        ) Worklist_item_map.empty worklist
     in
     let _ = new_map in
     ()
     (* print_endline "";
       print_endline @@ Jhupllib.Pp_utils.pp_to_string (Worklist_item_map.pp Format.pp_print_int) new_map *)
     ;; *)

  (* let show_worklist (wl: (Reachability_graph.edge * grayStatus) list)
     =
     let edges = List.map
         (fun (e, _) -> e) wl
     in
     show_edge_list edges
     ;; *)

  let is_original (e : Reachability_graph.edge) : bool =
    let (_, _, t) = e.label in
    match t with
    | Original -> true
    | _ -> false
  ;;

  let og_edge_is_v1_v2 (e : Reachability_graph.edge) (curr_summary : summary) : summary =
    let v1 = e.source in
    let v2 = e.target in
    let addition_to_worklist =
      let open Nondeterminism_monad in
      (* We want v3, which is all outgoing neighbors of v1 *)
      let%bind (v3, v1_v3_label) = pick_enum(Reachability_graph.get_outgoing_neighbors v1 curr_summary.graph) in
      (* We want v4, which is all outgoing neighbors of v2 that are
         initial neighbors of v3 *)
      let%bind (v4, _) = pick_enum(Node_NL_set_multimap.find v3 curr_summary.outgoing_og_edges_map) in
      let%bind v2_v4_label = pick_enum(Reachability_graph.get_labels (v2, v4) curr_summary.graph) in
      let (_, z, _) = v1_v3_label in
      let (q, _ , _) = v2_v4_label in
      let%orzero (Some (new_q, new_z)) = find_rule q z in
      let new_edge : Reachability_graph.edge =
        {
          source = v1;
          target = v4;
          label = (new_q, new_z, Summary)
        }
      in
      (* We want to add the edge to the worklist only if the new edge isn't
         already in the summary graph *)
      [%guard (not (Reachability_graph.contains_edge new_edge curr_summary.graph))];
      logger `trace (fun () -> Printf.sprintf
                        ("Original edge is v1->v2\n" ^^
                         "v1 = %s\nv2 = %s\nv3 = %s\nv4 = %s\n" ^^
                         "v1 to v3 = %s\nv2 to v4 = %s\n" ^^
                         "new label = %s\n"
                        )
                        (N.show v1) (N.show v2) (N.show v3) (N.show v4)
                        (L.show v1_v3_label) (L.show v2_v4_label)
                        (L.show (new_q, new_z, Summary))
                    );
      return (new_edge)
    in
    {curr_summary with
     worklist =
       (List.of_enum @@ Enum.append (List.enum curr_summary.worklist) (Nondeterminism_monad.enum addition_to_worklist))}
  ;;

  let og_edge_is_v3_v4 (e : Reachability_graph.edge) (curr_summary : summary) : summary =
    let v3 = e.source in
    let v4 = e.target in
    let addition_to_worklist =
      let open Nondeterminism_monad in
      (* Want v1, which is all incoming neighbors to v3 *)
      let%bind (v1, v1_v3_label) = pick_enum(Reachability_graph.get_incoming_neighbors v3 curr_summary.graph) in
      (* We want v2, which is all initial outgoing neighbors to v1, and also incoming neighbors to v4 *)
      let%bind (v2, _) = pick_enum(Node_NL_set_multimap.find v1 curr_summary.outgoing_og_edges_map) in
      let%bind v2_v4_label = pick_enum(Reachability_graph.get_labels (v2, v4) curr_summary.graph) in
      let (_, z, _) = v1_v3_label in
      let (q, _ , _) = v2_v4_label in
      let%orzero (Some (new_q, new_z)) = find_rule q z in
      let new_edge : Reachability_graph.edge =
        {
          source = v1;
          target = v4;
          label = (new_q, new_z, Summary)
        }
      in
      (* We want to add the edge to the worklist only if the new edge isn't
         already in the summary graph *)
      [%guard (not (Reachability_graph.contains_edge new_edge curr_summary.graph))];
      logger `trace (fun () -> Printf.sprintf
                        ("Original edge is v3->v4\n" ^^
                         "v1 = %s\nv2 = %s\nv3 = %s\nv4 = %s\n" ^^
                         "v1 to v3 = %s\nv2 to v4 = %s\n" ^^
                         "new label = %s\n"
                        )
                        (N.show v1) (N.show v2) (N.show v3) (N.show v4)
                        (L.show v1_v3_label) (L.show v2_v4_label)
                        (L.show (new_q, new_z, Summary))
                    );
      return (new_edge)
    in
    {curr_summary with
     worklist =
       (List.of_enum @@ Enum.append (List.enum curr_summary.worklist) (Nondeterminism_monad.enum addition_to_worklist))}
  ;;

  let og_edge_is_v1_v3 (e : Reachability_graph.edge) (curr_summary : summary) : summary =
    let v1 = e.source in
    let v3 = e.target in
    let v1_v3_label = e.label in
    (* logger `trace (fun () -> Printf.sprintf
                      ("\n===========================================\n" ^^
                        "Original edge is v1->v3\n" ^^
                       "v1 = %s\nv3 = %s\n" ^^
                       "v1 to v3 = %s\n"
                      )
                      (N.show v1) (N.show v3)
                      (L.show v1_v3_label)        );
       logger `trace (fun () -> Printf.sprintf
                      ("\n===========================================\n"
                      )
                      ); *)
    let addition_to_worklist =
      let open Nondeterminism_monad in
      (* We want v2, which are all original outgoing neighbors of v1 *)
      let%bind (v2, _) = pick_enum(Node_NL_set_multimap.find v1 curr_summary.outgoing_og_edges_map) in
      (* We want v4, which are all original outgoing neighbors of v3 *)
      let%bind (v4, _) = pick_enum(Node_NL_set_multimap.find v3 curr_summary.outgoing_og_edges_map) in
      let%bind v2_v4_label = pick_enum(Reachability_graph.get_labels (v2, v4) curr_summary.graph) in
      let (_, z, _) = v1_v3_label in
      let (q, _ , _) = v2_v4_label in
      let%orzero (Some (new_q, new_z)) = find_rule q z in
      let new_edge : Reachability_graph.edge =
        {
          source = v1;
          target = v4;
          label = (new_q, new_z, Summary)
        }
      in
      (* We want to add the edge to the worklist only if the new edge isn't
         already in the summary graph *)
      [%guard (not (Reachability_graph.contains_edge new_edge curr_summary.graph))];
      (* logger `trace (fun () -> Printf.sprintf
                        ("v2 = %s\nv4 = %s\n" ^^
                         "v2 to v4 = %s\n" ^^
                         "new label = %s\n"
                        )
                        (N.show v2)(N.show v4)
                        (L.show v2_v4_label)
                        (L.show (new_q, new_z, Summary))        ); *)
      logger `trace (fun () -> Printf.sprintf
                        ("Original edge is v1->v3\n" ^^
                         "v1 = %s\nv2 = %s\nv3 = %s\nv4 = %s\n" ^^
                         "v1 to v3 = %s\nv2 to v4 = %s\n" ^^
                         "new label = %s\n"
                        )
                        (N.show v1) (N.show v2) (N.show v3) (N.show v4)
                        (L.show v1_v3_label) (L.show v2_v4_label)
                        (L.show (new_q, new_z, Summary))        );
      return (new_edge)
    in
    {curr_summary with
     worklist =
       (List.of_enum @@ Enum.append (List.enum curr_summary.worklist) (Nondeterminism_monad.enum addition_to_worklist))}
  ;;

  let og_edge_is_v2_v4 (e : Reachability_graph.edge) (curr_summary : summary) : summary =
    let v2 = e.source in
    let v4 = e.target in
    let v2_v4_label = e.label in
    let addition_to_worklist =
      let open Nondeterminism_monad in
      (* We want v1, which are all original incoming neighbors of v2 *)
      let%bind (v1, _) = pick_enum(Node_NL_set_multimap.find v2 curr_summary.incoming_og_edges_map) in
      (* We want v3, which are all original incoming neighbors of v4 *)
      let%bind (v3, _) = pick_enum(Node_NL_set_multimap.find v4 curr_summary.incoming_og_edges_map) in
      let%bind v1_v3_label = pick_enum(Reachability_graph.get_labels (v1, v3) curr_summary.graph) in
      let (_, z, _) = v1_v3_label in
      let (q, _ , _) = v2_v4_label in
      let%orzero (Some (new_q, new_z)) = find_rule q z in
      let new_edge : Reachability_graph.edge =
        {
          source = v1;
          target = v4;
          label = (new_q, new_z, Summary)
        }
      in
      (* We want to add the edge to the worklist only if the new edge isn't
         already in the summary graph *)
      [%guard (not (Reachability_graph.contains_edge new_edge curr_summary.graph))];
      logger `trace (fun () -> Printf.sprintf
                        ("Original edge is v2->v4\n" ^^
                         "v1 = %s\nv2 = %s\nv3 = %s\nv4 = %s\n" ^^
                         "v1 to v3 = %s\nv2 to v4 = %s\n" ^^
                         "new label = %s\n"
                        )
                        (N.show v1) (N.show v2) (N.show v3) (N.show v4)
                        (L.show v1_v3_label) (L.show v2_v4_label)
                        (L.show (new_q, new_z, Summary))
                    );
      return (new_edge)
    in
    {curr_summary with
     worklist =
       (List.of_enum @@ Enum.append (List.enum curr_summary.worklist) (Nondeterminism_monad.enum addition_to_worklist))}
  ;;

  let step (curr_summary : summary) : summary option =
    (* let _ = print_endline @@ (Reachability_graph.show curr_summary.graph) in *)
    (* Get item off of worklist *)
    match curr_summary.worklist with
    | [] ->
      (* If there is nothing in the worklist, we are effectively done *)
      None
    | h :: t ->
      (* let _ = print_endline "" in
         let _ = print_endline @@ (Reachability_graph.show_edge h) in *)
      let new_graph = Reachability_graph.insert_edge h curr_summary.graph in
      (* We take the first edge in the worklist and add it to our graph *)
      (* TODO: check w Zach about adding before or after putting it on the worklist *)
      if (is_original h) then
        (* potential to become v1 - v2, or v3 - v4 *)
        Some
          (
            {curr_summary with graph = new_graph; worklist = t}
            |> og_edge_is_v1_v2 h
            |> og_edge_is_v3_v4 h
            |> og_edge_is_v1_v3 h
            |> og_edge_is_v2_v4 h
          )
      else
        (* src and tgt can only be v1 - v3, or v2 - v4 *)
        Some
          (
            {curr_summary with graph = new_graph; worklist = t}
            |> og_edge_is_v1_v3 h
            |> og_edge_is_v2_v4 h
          )
  ;;

  let rec step_to_closure (start_summary : summary) : summary =
    let new_summary = step start_summary in
    match new_summary with
    | None ->
      start_summary
    | Some unfinished_summary ->
      step_to_closure unfinished_summary
  ;;

  let reachable (src : G.Node.t) (tgt : G.Node.t) (s : summary) : bool =
    let _ = print_endline "computing reachability" in
    let summary_graph = s.graph in
    (* We want to look for all labels that have a G q-value, instead of just
       (G, #) ones *)
    let src_tgt_labels = Reachability_graph.get_labels (src, tgt) summary_graph in
    let _ = print_endline @@ ("No edges:") ^ (string_of_bool @@ Enum.is_empty src_tgt_labels) in
    Enum.exists (fun lab ->
        logger `trace (fun () -> Printf.sprintf
                          ("IN REACHABLE" ^^
                           "label = %s"
                          )
                          (L.show lab));
        match lab with
        | (state, _, _) ->
          begin
            match state.dstm_operation with
            | NoOp ->
              state.dstm_complete
            | _ ->
              false
          end
      ) src_tgt_labels
  ;;

  let get_reachable_nodes (src : G.Node.t) (s : summary) : G.Node.t Enum.t =
    let summary_graph = s.graph in
    let src_outgoing_neighbors = Reachability_graph.get_outgoing_neighbors src summary_graph in
    (* NOTE: maybe make this a dictionary? instead of doing filter map *)
    Enum.filter_map (fun (n, l) ->
        match l with
        | (state, _, _) ->
          begin
            match state.dstm_operation with
            | NoOp ->
              if state.dstm_complete then Some n else None
            | _ -> None
          end
      )
      src_outgoing_neighbors
  ;;

  let get_examine_result_nodes (src : G.Node.t) (s : summary) :
    (G.Node.t * ((Stack1.t, Stack2.t, Stack3.t) trinary)) Enum.t
    =
    let summary_graph = s.graph in
    let src_outgoing_neighbors = Reachability_graph.get_outgoing_neighbors src summary_graph in
    (* NOTE: maybe make this a dictionary? instead of doing filter map *)
    Enum.filter_map (fun (n, l) ->
        match l with
        | (state, _, _) ->
          begin
            match state.dstm_operation with
            | ExamineResult (se) ->
              Some (n, se)
            | _ -> None
          end
      )
      src_outgoing_neighbors
  ;;

  let add_new_edge (og_edge : G.edge) (s : summary)
    : summary =
    let new_edge = og_edge_conversion og_edge in
    let (new_worklist, new_incoming_og_map, new_outgoing_og_map) =
      worklist_map_setup_fun
        (s.worklist, s.incoming_og_edges_map, s.outgoing_og_edges_map)
        new_edge
    in
    { s with
      worklist = new_worklist;
      incoming_og_edges_map = new_incoming_og_map;
      outgoing_og_edges_map = new_outgoing_og_map
    }
  ;;

  let add_new_subgraph (input_subgraph : G.t) (s : summary) : summary =
    let flip = fun f -> fun fst -> fun snd ->
      f snd fst
    in
    Enum.fold (flip add_new_edge) s (G.get_all_edges input_subgraph)
  ;;


end;;
