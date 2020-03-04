open Batteries;;

open Closure;;
open Graph_types;;
open Jhupllib.Nondeterminism;;
open Stack_utils;;
open Utils;;

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

  (* Pretty-printing for differentiating between grammars *)
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
    | LookingFor of ((LG.t, RG.t) choice) (* symbol *)
    | IncompleteLookingFor of ((LG.t, RG.t) choice) (* q1 plus symbol *)
    | Complete (* q2 *)
  [@@deriving ord, eq]

  (* Pretty-printing DSTM state *)
  let pp_dstm_state formatter dstm_state =
    match dstm_state with
    | Incomplete -> Format.pp_print_string formatter "q1"
    | LookingFor (x) ->
      _pp_grammar formatter x
    | IncompleteLookingFor (x) ->
      Format.pp_print_string formatter "q1";
      _pp_grammar formatter x
    | Complete -> Format.pp_print_string formatter "q2"

  module Dstm_state =
  struct
    type t = dstm_state [@@deriving ord, show]
  end;;

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


  (* type worklist_item =
     (Reachability_graph.edge)[@@deriving ord, show];;

     module Worklist_item =
     struct
     type t = worklist_item [@@deriving ord, show]
     end;;

     module Worklist_item_map =
     struct
     module M = BatMap.Make(Worklist_item);;
     include M;;
     include Jhupllib.Pp_utils.Map_pp(M)(Worklist_item);;
     end;; *)

  type summary =
    {
      graph : Reachability_graph.t;
      worklist : Reachability_graph.edge list;
      (* worklist : worklist_item list; *)
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
           (* new_edge :: worklist_acc *)
           (* FIXME: setting all initial edges to NonSpurious for now, but
              definitely need to update this because there must be spurious ones?
           *)
           List.append worklist_acc [new_edge]
        ) [] reachability_edges
    in
    (* let new_graph =
      reachability_edges
      |> List.fold_left
        (flip Reachability_graph.insert_edge) Reachability_graph.empty
    in *)
    {
      (* graph = new_graph; *)
      graph = Reachability_graph.empty;
      worklist = new_worklist;
    }
  ;;

  (* Function that finds new symbols based on LCL rules
     - q : the R-value to be considered
     - z : the L-value to be considered
  *)
  let find_rule (q : dstm_state) (z : dstm_tape_val) : (dstm_state * dstm_tape_val) option =
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
      in return (new_edge)
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
      let%bind v2 = pick_enum(get_incoming_original_neighbors v4 curr_summary.graph) in
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
      in return (new_edge)
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
      in return (new_edge)
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
      in return (new_edge)
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
    let (search_label : L.t) = (Complete, TapeHash, Summary) in
    (* let _ = print_endline @@ (Reachability_graph.show summary_graph) in  *)
    let search_edge : Reachability_graph.edge =
      { source = src ;
        target = tgt ;
        label = search_label
      }
    in
    Reachability_graph.contains_edge search_edge summary_graph
  ;;

end;;
