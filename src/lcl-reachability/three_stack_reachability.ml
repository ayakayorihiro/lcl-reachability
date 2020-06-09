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
  module StackA : Stack_grammar
  module StackB : Stack_grammar
  module StackC : Stack_grammar
  module G : Graph
    with type Label.t = ((StackA.t, StackB.t, StackC.t) three_stack) stack_action

  (* Summary of three-stack graph *)
  type summary

  val create_initial_summary : G.t -> summary

  val step : summary -> summary option

  val step_to_closure : summary -> summary

  val reachable : G.Node.t -> G.Node.t -> summary -> bool

  val get_reachable_nodes : G.Node.t -> summary -> G.Node.t Enum.t

end;;

module Make
    (A : Stack_grammar)
    (B : Stack_grammar)
    (C : Stack_grammar)
    (G : Graph
     with type Label.t = ((A.t, B.t, C.t) three_stack) stack_action)
  : ThreeStackReachability
    with module StackA = A
     and module StackB = B
     and module StackC = C
     and module G = G
=
struct
  module StackA = A
  module StackB = B
  module StackC = C
  module G = G (* User graph *)

  (* Pretty-printing for differentiating between grammars *)
  let _pp_grammar formatter (c : ('a, 'b, 'c) three_stack) =
    match c with
    | StackA(x) ->
      Format.pp_print_string formatter "ɣ" ;
      A.pp formatter x
    | StackB(x) ->
      Format.pp_print_string formatter "ψ";
      B.pp formatter x
    | StackC(x) ->
      Format.pp_print_string formatter "θ" ;
      C.pp formatter x

  (* Pretty-printing for differentiating between grammars *)
  let _pp_grammar2 formatter (choice : ('a, 'b) choice) =
    match choice with
    | Left(x) ->
      Format.pp_print_string formatter "⦇" ;
      B.pp formatter x
    | Right(x) ->
      Format.pp_print_string formatter "⟦" ;
      C.pp formatter x

  type dstm_state =
    | Incomplete (* B *)
    | LookingFor of ((A.t, B.t, C.t) three_stack) (* ɣ, ψ, or θ *)
    | IncompleteLookingFor of ((B.t, C.t) choice) (* ψB or θB *)
    | Complete (* G *)
  [@@deriving ord, eq]

  (* Pretty-printing DSTM state *)
  let pp_dstm_state formatter dstm_state =
    match dstm_state with
    | Incomplete -> Format.pp_print_string formatter "B"
    | LookingFor (x) ->
      _pp_grammar formatter x
    | IncompleteLookingFor (x) ->
      _pp_grammar2 formatter x;
      Format.pp_print_string formatter "B"
    | Complete -> Format.pp_print_string formatter "G"


  module Dstm_state =
  struct
    type t = dstm_state [@@deriving ord, show]
  end;;

  type dstm_tape_val =
    | TapeSymbol of ((A.t, B.t, C.t) three_stack)
    | TapeHash
  [@@deriving ord, eq]

  let pp_dstm_tape_val formatter tape_val =
    match tape_val with
    | TapeSymbol (x) ->
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

  type summary =
    {
      graph : Reachability_graph.t;
      worklist : Reachability_graph.edge list;
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
               (Incomplete, TapeSymbol(grammar_choice), Original)
             | Pop (grammar_choice) ->
               (LookingFor(grammar_choice), TapeHash, Original)
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
           List.append worklist_acc [new_edge]
        ) [] reachability_edges
    in
    (* let new_graph =
       reachability_edges
       |> List.fold_left
        (flip Reachability_graph.insert_edge) Reachability_graph.empty
       in *)
    {
      graph = Reachability_graph.empty;
      worklist = new_worklist;
    }
  ;;

  (* Function that finds new symbols based on rules described by chart
     - q : the R-value to be considered
     - z : the L-value to be considered
  *)
  let find_rule (q : dstm_state) (z : dstm_tape_val) : (dstm_state * dstm_tape_val) option =
    match q with
    | Incomplete ->
      Some (q, z) (* column C *)
    | Complete ->
      (match z with
       | TapeHash ->
         Some (Complete, TapeHash) (* cell B2 *)
       | TapeSymbol(s) ->
         match s with
         | StackA _ ->
           Some (Incomplete, z) (* cell B3 *)
         | _ ->
           Some (Complete, z) (* cell B4, B5 *)
      )
    | IncompleteLookingFor (sym) -> (* column F and H *)
      begin
        match sym with
        | Left (q_psi) -> (* column F - ψB *)
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | StackB (ts_psi) ->
                if (q_psi = ts_psi) then (* cell F4 *)
                  Some (Incomplete, TapeHash)
                else None
              | _ ->
                Some (q, z) (* cell F3, F5 *)
             )
           | TapeHash ->
             Some (q, z) (* cell F2 *)
          )
        | Right(q_theta) -> (* column H - θB *)
          (match z with
           | TapeSymbol (ts) ->
             (match ts with
              | StackC (ts_theta) ->
                if (q_theta = ts_theta) then (* cell H5 *)
                  Some (Incomplete, TapeHash)
                else None
              | _ -> Some (q, z) (* cell H3, H4 *)
             )
           | TapeHash -> Some (q, z) (* cell H2 *)
          )
      end
    | LookingFor (sym) ->
      begin
        match sym with
        | StackA (q_gamma) -> (* column D *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell D2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | StackA (ts_gamma) ->
                 if (q_gamma = ts_gamma) then (* cell D3 *)
                   Some (Complete, TapeHash)
                 else
                   None
               | _ ->
                 Some (LookingFor (sym), z) (* cell D4, D5 *)
              )
          )
        | StackB (q_psi) -> (* column E *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell E2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | StackA _ ->
                 Some (IncompleteLookingFor (Left (q_psi)), z) (* cell E3 *)
               | StackB (ts_psi) ->
                 if (q_psi = ts_psi) then (* cell E4 *)
                   Some (Complete, TapeHash)
                 else
                   None
               | StackC _ ->
                 Some (LookingFor (sym), z) (* cell E5 *)
              )
          )
        | StackC (q_theta) -> (* column G *)
          (
            match z with
            | TapeHash -> Some (q, z) (* cell G2 *)
            | TapeSymbol (ts) ->
              (match ts with
               | StackC (ts_theta) ->
                 if (q_theta = ts_theta) then (* cell G5 *)
                   Some (Complete, TapeHash)
                 else None
               | StackA _ ->
                 Some (IncompleteLookingFor (Right (q_theta)), z) (* cell G3 *)
               | StackB _ ->
                 Some (LookingFor (sym), z) (* cell G4 *)
              )
          )
      end
  ;;

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

  let get_incoming_original_neighbors (v : N.t) (g : Reachability_graph.t) : N.t Enum.t =
    let incoming_neighbors : (N.t * L.t) Enum.t =
      Reachability_graph.get_incoming_neighbors v g
    in
    Enum.filter_map
      (fun (n, l) ->
         let (_, _, t)  = l in
         match t with
         | Original -> Some n
         | _ -> None
      ) incoming_neighbors
  ;;

  let get_outgoing_original_neighbors (v : N.t) (g : Reachability_graph.t) : N.t Enum.t =
    let outgoing_neighbors : (N.t * L.t) Enum.t =
      Reachability_graph.get_outgoing_neighbors v g
    in
    Enum.filter_map
      (fun (n, l) ->
         let (_, _, t)  = l in
         match t with
         | Original -> Some n
         | _ -> None
      ) outgoing_neighbors
  ;;

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
      let%bind v4 = pick_enum(get_outgoing_original_neighbors v3 curr_summary.graph) in
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
      let%bind v2 = pick_enum(get_outgoing_original_neighbors v1 curr_summary.graph) in
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
    let addition_to_worklist =
      let open Nondeterminism_monad in
      (* We want v2, which are all original outgoing neighbors of v1 *)
      let%bind v2 = pick_enum(get_outgoing_original_neighbors v1 curr_summary.graph) in
      (* We want v4, which are all original outgoing neighbors of v3 *)
      let%bind v4 = pick_enum(get_outgoing_original_neighbors v3 curr_summary.graph) in
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
      let%bind v1 = pick_enum(get_incoming_original_neighbors v2 curr_summary.graph) in
      (* We want v3, which are all original incoming neighbors of v4 *)
      let%bind v3 = pick_enum(get_incoming_original_neighbors v4 curr_summary.graph) in
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
            {graph = new_graph; worklist = t}
            |> og_edge_is_v1_v2 h
            |> og_edge_is_v3_v4 h
            |> og_edge_is_v1_v3 h
            |> og_edge_is_v2_v4 h
          )
      else
        (* src and tgt can only be v1 - v3, or v2 - v4 *)
        Some
          (
            {graph = new_graph; worklist = t}
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
    let summary_graph = s.graph in
    (* We want to look for all labels that have a G q-value, instead of just
       (G, #) ones *)
    let src_tgt_labels = Reachability_graph.get_labels (src, tgt) summary_graph in
    Enum.exists (fun lab ->
        match lab with
        | (Complete, _, _) -> true
        | _ -> false
    ) src_tgt_labels
    (* let (search_label : L.t) = (Complete, TapeHash, Summary) in
    (* let _ = print_endline @@ (Reachability_graph.show summary_graph) in  *)
    let search_edge : Reachability_graph.edge =
      { source = src ;
        target = tgt ;
        label = search_label
      }
    in
    Reachability_graph.contains_edge search_edge summary_graph *)
  ;;

  let get_reachable_nodes (src : G.Node.t) (s : summary) : G.Node.t Enum.t =
    let summary_graph = s.graph in
    let src_outgoing_neighbors = Reachability_graph.get_outgoing_neighbors src summary_graph in
    Enum.filter_map (fun (n, l) ->
        match l with
        | (Complete, _, _) -> Some n
        | _ -> None
      )
      src_outgoing_neighbors
  ;;

end;;
