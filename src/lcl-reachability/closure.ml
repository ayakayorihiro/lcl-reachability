open Batteries;;
open Graph_types;;
open Stack_utils;;
open Utils;;

(* Data type for module for constructing graph and computing the
   reachability question. *)
module type Reachability =
sig
  module LeftGrammar : Stack_grammar
  module RightGrammar : Stack_grammar
  module G : Graph
    with type Label.t = ((LeftGrammar.t, RightGrammar.t) choice) stack_action

  (* Want to define a type for DSTM states - want to take the stack grammars from
     the graph and define states based on them *)

  (* Same deal for contents of DSTM tape - contains the "open" expressions from
     both stack grammars, plus the "done" (#) symbol *)

  (* Summary of two-stack graph *)
  type summary

  val create_initial_summary : G.t -> summary

  val step : summary -> summary option

  val step_to_closure : summary -> summary

  val reachable : G.Node.t -> G.Node.t -> summary -> bool

  (* val show_summary : summary -> string *)

end;;

(** Functor - takes in graph type, and creates module for
    dealing with specific graph and reachability question.
*)
module Make
    (LG : Stack_grammar)
    (RG : Stack_grammar)
    (G : Graph
     with type Label.t = ((LG.t, RG.t) choice) stack_action)
  : Reachability
    with module LeftGrammar = LG
     and module RightGrammar = RG
     and module G = G
=
struct
  module LeftGrammar = LG
  module RightGrammar = RG
  module G = G (* User-inputted graph *)

  let _pp_grammar formatter choice =
    match choice with
    | Left(x) ->
      Format.pp_print_string formatter "⦇" ;
      LG.pp formatter x
    | Right(x) ->
      Format.pp_print_string formatter "⟦" ;
      RG.pp formatter x

  type dstm_state =
    | Incomplete (* q1 *)
    | LookingFor of ((LG.t, RG.t) choice)
    | IncompleteLookingFor of ((LG.t, RG.t) choice) (* q1 plus symbol *)
    | Complete (* q2 *)
  [@@deriving ord, eq]
  let pp_dstm_state formatter dstm_state =
    match dstm_state with
    | Incomplete -> Format.pp_print_string formatter "q1"
    | LookingFor (x) ->
      _pp_grammar formatter x
    | IncompleteLookingFor (x) ->
      Format.pp_print_string formatter "q1";
      _pp_grammar formatter x
    | Complete -> Format.pp_print_string formatter "q2"


  type dstm_tape_val =
    | TapeSymbol of ((LG.t, RG.t) choice)
    | TapeHash
  [@@deriving ord, eq]
  let pp_dstm_tape_val formatter tape_val =
    match tape_val with
    | TapeSymbol (x) ->
      _pp_grammar formatter x
    | TapeHash ->
      Format.pp_print_char formatter '#'

  module N = G.Node;;
  module L : Decorated_type with type t = (dstm_state * dstm_tape_val) =
  struct
    type t = (dstm_state * dstm_tape_val)
    [@@deriving ord, eq]
    let pp formatter (s, t) =
      Format.pp_print_string formatter "〈" ;
      pp_dstm_state formatter s ;
      Format.pp_print_string formatter ", " ;
      pp_dstm_tape_val formatter t;
      Format.pp_print_string formatter "〉" ;
    ;;
    let show p =
      Jhupllib.Pp_utils.pp_to_string pp p
    ;;
  end;;

  module Reachability_graph = Graph_types.Make(N)(L);;

  type summary =
    {
      graph : Reachability_graph.t;
      worklist : Reachability_graph.edge list
    } [@@deriving show];;
  let _ = pp_summary;;

  let create_initial_summary (input_graph : G.t) : summary =
    (* 0. Tentative TODO: Eliminate all epsilons - close over the epsilons *)
    (* 1. Get all of the edges in the original graph *)
    let og_edges = G.get_all_edges input_graph in
    let reachability_edges =
      og_edges
      |> Enum.map
        (fun e ->
          let l = e.G.label in
          let new_label =
            match l with
            | Push (grammar_choice) ->
              (Incomplete, TapeSymbol(grammar_choice))
            | Pop (grammar_choice) ->
              (LookingFor(grammar_choice), TapeHash)
            | Epsilon -> failwith "There should be no epsilons in this graph???"
          in
            {
              Reachability_graph.source = e.G.source;
              Reachability_graph.target = e.G.target;
              Reachability_graph.label = new_label
            }
        )
    |> List.of_enum
    in
    (* 2. For each edge, create edge in new graph *)
    let new_worklist =
      List.fold_left
        (fun worklist_acc -> fun new_edge ->
           (* new_edge :: worklist_acc *)
           (* TODO: trying out non-reverse ordering *)
           List.append worklist_acc [new_edge]
        ) [] reachability_edges
    in
    let new_graph =
      reachability_edges
      |> List.fold_left
        (flip Reachability_graph.insert_edge) Reachability_graph.empty
    in
    {
      graph = new_graph;
      worklist = new_worklist
    }
  ;;

  (* Function that finds new symbols based on LCL rules
     - q : the R-value to be considered
     - z : the L-value to be considered
  *)
  let find_rule (q : dstm_state) (z : dstm_tape_val) : L.t option =
    match q with
    | Incomplete ->
      Some (q, z) (* rule 5 *)
    | Complete ->
      (match z with
       | TapeHash ->
         Some (Complete, TapeHash) (* rule 6 *)
       | TapeSymbol(_) ->
         Some (Incomplete, z) (* rule 7 *)
      )
    | IncompleteLookingFor (sym) ->
      begin
        match sym with
        | Left(q_left) ->
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | Left(ts_left) ->
                if (q_left = ts_left) then (* rule 12 *)
                  Some (Incomplete, TapeHash)
                else None
              | Right _ ->
                Some (q, z) (* rule 11 *)
             )
           | TapeHash ->
             Some (q, z) (* rule 11 *)
          )
        | Right(q_right) ->
          (* Same thing as left... *)
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | Left (_) ->
                Some (q, z) (* rule 16 *)
              | Right (ts_right) ->
                if (q_right = ts_right) then (* rule 17 *)
                  Some (Incomplete, TapeHash)
                else None
             )
           | TapeHash -> Some (q, z) (* rule 16 *)
          )
      end
    | LookingFor (sym) ->
      begin
        match sym with
        | Left (q_left) ->
          (
            match z with
            | TapeHash -> Some (q, z) (* rule 8 *)
            | TapeSymbol (ts) ->
              (match ts with
               | Left (ts_left) ->
                 if (q_left = ts_left) then (* rule 10 *)
                   Some (Complete, TapeHash)
                 else
                   None
               | Right (_) ->
                 Some (IncompleteLookingFor (sym), z) (* rule 9 *)
              )
          )
        | Right (q_right) ->
          ( match z with
            | TapeHash -> Some (q, z) (* rule 13 *)
            | TapeSymbol (ts) ->
              (match ts with
               | Left (_) ->
                 Some (IncompleteLookingFor (sym), z) (* rule 14 *)
               | Right (ts_right) ->
                 if (q_right = ts_right) then (* rule 15 *)
                   Some (Complete, TapeHash)
                 else None
              )
          )
      end
  ;;

  let step (curr_summary : summary) : summary option =
    (* NOTE: For debugging purposes *)
    print_endline "" ;
    print_endline @@ show_summary curr_summary ;
    let curr_graph = curr_summary.graph in
    let curr_worklist = curr_summary.worklist in
    match curr_worklist with
    | [] ->
      (* If there is nothing in the worklist, we are effectively done *)
      None
    | h :: t ->
      (* We take the first edge in the worklist and add it to our graph  *)
      let src = h.source in
      let tgt = h.target in
      let (q, z) = h.label in (* TODO: forced match causing problems? *)
      let tgt_outgoing = Reachability_graph.get_outgoing_neighbors tgt curr_graph in
      let src_incoming = Reachability_graph.get_incoming_neighbors src curr_graph in
      if ((List.is_empty tgt_outgoing) && (List.is_empty src_incoming))
      then
        (* If there are no outgoing and incoming, then add the edge and return *)
        Some ({ graph = Reachability_graph.insert_edge h curr_graph;
                worklist = t })
      else
        let intermediate_summary =
          { graph = Reachability_graph.insert_edge h curr_graph;
            worklist = t
          }
        in
        (* OUTGOING NEIGHBORS OF TGT *)
        let outgoing_evaluation =
          List.fold_left
            (fun curr_sum -> fun (curr_outedge : (N.t * L.t)) ->
               let curr_reach_graph = curr_sum.graph in
               let curr_worklist = curr_sum.worklist in
               let (tgt', lbl') = curr_outedge in
               let (curr_q, _)  = lbl' in
               let rule_opt = find_rule curr_q z in
               match rule_opt with
               | None ->
                 curr_sum
               | Some (new_lbl) ->
                 (* define edge here  *)
                 let new_edge : Reachability_graph.edge =
                   {
                     source = src;
                     target = tgt';
                     label = new_lbl
                   }
                 in
                 (* FIXME: don't add in worklist if the edge already exists in the graph *)
                 let new_reach_graph = Reachability_graph.insert_edge new_edge curr_reach_graph in
                 (* let new_worklist = List.append curr_worklist [new_edge] in *)
                 let new_worklist = List.append curr_worklist [new_edge] in
                 {
                   graph = new_reach_graph ;
                   worklist = new_worklist
                 }
            ) intermediate_summary tgt_outgoing
        in
        (* INCOMING NEIGHBORS OF SRC *)
        let incoming_evaluation =
          List.fold_left
            (fun curr_sum -> fun (curr_inedge : (N.t * L.t)) ->
               let curr_reach_graph = curr_sum.graph in
               let curr_worklist = curr_sum.worklist in
               let (src', lbl') = curr_inedge in
               let (_, curr_z)  = lbl' in
               let rule_opt = find_rule q curr_z in
               match rule_opt with
               | None ->
                 curr_sum
               | Some (new_lbl) ->
                 (* define edge here *)
                 let new_edge : Reachability_graph.edge =
                   {
                     source = src';
                     target = tgt;
                     label = new_lbl
                   }
                 in
                 let new_reach_graph = Reachability_graph.insert_edge new_edge curr_reach_graph in
                 let new_worklist = List.append curr_worklist [new_edge] in
                 {
                   graph = new_reach_graph ;
                   worklist = new_worklist
                 }
            ) outgoing_evaluation src_incoming
        in
        Some incoming_evaluation
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
    let summary_graph = s.graph in
    let (search_label : L.t) = (Complete, TapeHash) in
    let search_edge : Reachability_graph.edge =
      { source = src ;
        target = tgt ;
        label = search_label
      }
    in
    Reachability_graph.contains_edge search_edge summary_graph
  ;;

end;;
