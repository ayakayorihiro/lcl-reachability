open Batteries;;
open Closure;;
open Graph_types;;
open Stack_utils;;
open Utils;;

(** Functor - takes in graph type, and creates module for
    dealing with specific graph and reachability question.
*)
module Make
    (LG : Stack_grammar)
    (RG : Stack_grammar)
    (G : Graph
     with type Label.t = ((LG.t, RG.t) choice) stack_action_lcl)
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
  let _pp_grammar formatter (choice : ('a, 'b) choice) =
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

  (* NonSpurious is equivalent to "good" in algorithm *)
  (* MaybeGray/NotGray *)
  type grayStatus =
    | NotGray
    | MaybeGray
  [@@deriving ord];;

  let pp_grayStatus formatter gray =
    match gray with
    | NotGray -> Format.pp_print_string formatter "NG"
    | MaybeGray -> Format.pp_print_string formatter "G"
;;

  type worklist_item =
    (Reachability_graph.edge * grayStatus)[@@deriving ord, show];;

  module Worklist_item =
  struct
    type t = worklist_item [@@deriving ord, show]
  end;;

  module Worklist_item_map =
  struct
    module M = BatMap.Make(Worklist_item);;
    include M;;
    include Jhupllib.Pp_utils.Map_pp(M)(Worklist_item);;
  end;;

  type summary =
    {
      graph : Reachability_graph.t;
      (* keep original graph for feasibility purposes *)
      original_graph : G.t;
      worklist : worklist_item list;
      left_z : Node_pair_to_Dstm_tape_val_multimap.t;
      (* left_z_bad: field for spurious left_zs *)
      left_z_bad : Node_pair_to_Dstm_tape_val_multimap.t;
      right_q : Node_pair_to_Dstm_state_multimap.t;
      good_map : Node_pair_to_Dstm_state_multimap.t
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
           (* FIXME: setting all initial edges to NonSpurious for now, but
              definitely need to update this because there must be spurious ones?
           *)
           List.append worklist_acc [(new_edge, MaybeGray)]
        ) [] reachability_edges
    in
    let new_graph =
      reachability_edges
      |> List.fold_left
        (flip Reachability_graph.insert_edge) Reachability_graph.empty
    in
    {
      graph = new_graph;
      original_graph = input_graph;
      worklist = new_worklist;
      left_z = Node_pair_to_Dstm_tape_val_multimap.empty;
      left_z_bad = Node_pair_to_Dstm_tape_val_multimap.empty;
      right_q = Node_pair_to_Dstm_state_multimap.empty;
      good_map = Node_pair_to_Dstm_state_multimap.empty
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

  (* let show_worklist =
    Jhupllib.Pp_utils.pp_to_string
    (Jhupllib.Pp_utils.pp_list Reachability_graph.pp_edge)
  ;; *)


  (* Utility function computing `good and q \in {q1, q2}` *)
  let wouldbeMaybeGray (q : dstm_state) (status : grayStatus) : bool =
    match status with
    | NotGray -> false
    | MaybeGray ->
      begin
        match q with
        | Incomplete | Complete -> true
        | _ -> false
      end
  ;;

  (* Helper function for computing whether outgoing edge is "feasible"
     src/tgt are src and tgt of edge in ORIGINAL GRAPH
  *)
  let isFeasible_outgoing (src : N.t) (tgt : N.t) (l : L.t) (s : summary) : bool =
    let (q, _) = l in
    let original_graph = s.original_graph in
    let labels_enum = G.get_labels (src, tgt) original_graph in
    let labels = List.of_enum labels_enum in
    (* function reStatusStatusturning true if an element is a push
       used to check if first condition for 1 is met.
    *)
    let is_push (og_l : G.Label.t) : bool =
      match og_l with
      | Push _ -> true
      | _ -> false
    in
    (* function returning true if element is left pop
       used to check if first condition for 2 is met.
    *)
    let is_left_pop (og_l : G.Label.t) : bool =
      match og_l with
      | Pop (c) ->
        begin
          match c with
          | Left _ -> true
          | _ -> false
        end
      | _ -> false
    in
    (* function returning true if element is right pop
       used to check if first condition for 3 is met.
    *)
    let is_right_pop (og_l : G.Label.t) : bool =
      match og_l with
      | Pop (c) ->
        begin
          match c with
          | Right _ -> true
          | _ -> false
        end
      | _ -> false
    in
    (* 1. If original edge is a push, then q must be q1 *)
    if (List.exists is_push labels)
    then
      (match q with
       | Incomplete -> true
       | _ -> false
      )
    else
      (
        (* 2. If original edge is a left pop, then q can't be
           LookingFor right push nor IncompleteLookingFor right push  *)
        if (List.exists is_left_pop labels)
        then
          begin
            match q with
            | LookingFor c | IncompleteLookingFor c ->
              begin
                match c with
                | Right _ -> false
                | _ -> true
              end
            | _ -> true
          end
        else
          (
            (* 3. If original edge is a right pop, then q can't be LookingFor left push *)
            if (List.exists is_right_pop labels)
            then
              begin
                match q with
                | LookingFor c | IncompleteLookingFor c ->
                  begin
                    match c with
                    | Left _ -> false
                    | _ -> true
                  end
                | _ -> true
              end
            else true (* trivial case *)
          )
      )
  ;;

  (* Helper function for computing whether incoming edge is "feasible" *)
  let isFeasible_incoming (src : N.t) (tgt : N.t) (l : L.t) (s : summary) : bool =
    let (_, z) = l in
    let labels_enum = G.get_labels (src, tgt) s.original_graph in
    let labels = List.of_enum labels_enum in
    (* function returning true if an element is a Pop,
       used to check if first condition for 1 is met
    *)
    let is_pop (og_l : G.Label.t) : bool =
      match og_l with
      | Pop _ -> true
      | _ -> false
    in
    (* function returning true if an element is a left push
       used to check if first condition for 2 is met.
    *)
    let is_left_push (og_l : G.Label.t) : bool =
      match og_l with
      | Push (c) ->
        begin
          match c with
          | Left _ -> true
          | _ -> false
        end
      | _ -> false
    in
    (* function returning true if element is a right push
       used to check if first condition for 3 is met.
    *)
    let is_right_push (og_l : G.Label.t) : bool =
      match og_l with
      | Push (c) ->
        begin
          match c with
          | Right _ ->  true
          | _ -> false
        end
      | _ -> false
    in
    (* 1. If original edge is a pop, then z must be # *)
    if (List.exists is_pop labels)
    then
      (match z with
       | TapeHash -> true
       | _ -> false
      )
    else
      (
        (* 2. If original edge is a left push, then z cannot be right push *)
        if (List.exists is_left_push labels)
        then
          begin
            match z with
            | TapeSymbol c ->
              (match c with
               | Right _ -> false
               | _ -> true
              )
            | _ -> true
          end
        else (
          (* 3. If original edge is a right push, then z cannot be left push *)
          if (List.exists is_right_push labels)
          then
            begin
              match z with
              | TapeSymbol c ->
                (match c with
                 | Left _ -> false
                 | _ -> true
                )
              | _ -> true
            end
          else true (* trivial case *)
        )
      )

  ;;

  let generate_worklist_item_map (worklist : worklist_item list)
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
  ;;

  (* let show_worklist (wl: (Reachability_graph.edge * grayStatus) list)
     =
     let edges = List.map
         (fun (e, _) -> e) wl
     in
     show_edge_list edges
;; *)

  let step (curr_summary : summary) : summary option =
    (* NOTE: For debugging purposes *)
    (* print_endline "";
    print_endline @@ string_of_int (List.length curr_summary.worklist); *)
    (* print_endline "" ;
       print_endline @@ show_summary curr_summary ; *)
    (* let _ = show_edges_from_worklist in *)
    (* print_endline "";
    print_endline @@ (Jhupllib.Pp_utils.pp_to_string @@ Jhupllib.Pp_utils.pp_list pp_worklist_item) curr_summary.worklist; *)
    (* print_endline "";
       print_endline @@ Reachability_graph.show curr_summary.graph; *)
    let _ = generate_worklist_item_map curr_summary.worklist in
    let curr_graph = curr_summary.graph in
    let curr_worklist = curr_summary.worklist in
    match curr_worklist with
    | [] ->
      (* If there is nothing in the worklist, we are effectively done *)
      None
    | h :: t ->
      (* We take the first edge in the worklist and add it to our graph  *)
      let (head_edge, head_status) = h in
      let src = head_edge.source in
      let tgt = head_edge.target in
      let (q, z) = head_edge.label in
      let tgt_outgoing = Reachability_graph.get_outgoing_neighbors tgt curr_graph in
      let src_incoming = Reachability_graph.get_incoming_neighbors src curr_graph in
      let intermediate_summary =
        { curr_summary with
          graph = Reachability_graph.insert_edge head_edge curr_graph;
          worklist = t;
        }
      in
      (* OUTGOING NEIGHBORS OF TGT *)
      let outgoing_evaluation =
        Enum.fold
          (fun curr_sum -> fun (curr_outedge : (N.t * L.t)) ->
             let curr_right_q = curr_sum.right_q in
             let (tgt', _) = curr_outedge in
             let z_in_curr_left_z =
               Node_pair_to_Dstm_tape_val_multimap.mem (src, tgt') z curr_sum.left_z
             in
             let z_in_curr_left_bad_z =
               Node_pair_to_Dstm_tape_val_multimap.mem (src, tgt') z curr_sum.left_z_bad
             in
             if (not (z_in_curr_left_z && z_in_curr_left_bad_z))
             then
               (* Case if Z not in either curr_left_z nor curr_left_z_bad *)
               (
                 let left_updated_summary =
                   if (wouldbeMaybeGray q head_status)
                   then (* add Z to left_z *)
                     { curr_sum with
                       left_z =
                         Node_pair_to_Dstm_tape_val_multimap.add (src,tgt') z curr_sum.left_z
                     }
                   else (* add Z to left_z_bad *)
                     { curr_sum with
                       left_z_bad =
                         Node_pair_to_Dstm_tape_val_multimap.add (src, tgt') z curr_sum.left_z_bad
                     }
                 in
                 let curr_right_mapping =
                   Node_pair_to_Dstm_state_multimap.find (src, tgt') curr_right_q
                 in
                 (* foreach x \in R(i, k) do... *)
                 let resulting_summary =
                   Enum.fold
                     (fun acc_summ -> fun curr_q ->
                        let acc_graph = acc_summ.graph in
                        let rule_opt = find_rule curr_q z in
                        match rule_opt with
                        | None ->
                          acc_summ
                        | Some (new_lbl) ->
                          (* NOTE: switched up the order of execution from the paper *)
                          (* define edge here *)
                          let new_edge : Reachability_graph.edge =
                            {
                              source = src;
                              target = tgt';
                              label = new_lbl
                            }
                          in
                          let new_item_on_worklist =
                            if (Node_pair_to_Dstm_tape_val_multimap.mem (src, tgt') z acc_summ.left_z)
                            then
                              let (new_q, _) = new_lbl in
                              match new_q with
                              | Incomplete | Complete ->
                                (new_edge, MaybeGray)
                              | _ -> (new_edge, NotGray)
                            else (new_edge, NotGray)
                          in
                          let result_worklist =
                            if (not (Reachability_graph.contains_edge new_edge acc_summ.graph))
                            then List.append acc_summ.worklist [new_item_on_worklist]
                            else acc_summ.worklist
                          in
                          (* check if feasible, tgt and tgt' because we are
                             checking the outgoing edge in the original graph *)
                          if (isFeasible_outgoing tgt tgt' new_lbl acc_summ)
                          then
                            (* if it's feasible, we add it to the summary graph *)
                            let result_graph =
                              Reachability_graph.insert_edge new_edge acc_graph
                            in
                            { acc_summ with
                              graph = result_graph;
                              worklist = result_worklist;
                            }
                          else
                            { acc_summ with worklist = result_worklist }
                     ) left_updated_summary curr_right_mapping
                 in
                 (* The R map should not be affected *)
                 { resulting_summary with right_q = curr_sum.right_q }
               )
             else
               (
                 if (z_in_curr_left_bad_z && wouldbeMaybeGray q head_status) then
                   (* case where it's currently in bad but it's actually good *)
                   (
                     (* take z out of left_z_bad and put it into left_z *)
                     let summary_z_switched =
                       { curr_sum with
                         left_z = Node_pair_to_Dstm_tape_val_multimap.add
                             (src, tgt') z curr_sum.left_z ;
                         left_z_bad = Node_pair_to_Dstm_tape_val_multimap.remove
                             (src, tgt') z curr_sum.left_z_bad;
                       }
                     in
                     let curr_right_mapping =
                       Node_pair_to_Dstm_state_multimap.find (src, tgt') summary_z_switched.right_q
                     in
                     (* foreach x \in R(i, k) do... from line 23 in alg 2 *)
                     let resulting_summary =
                       Enum.fold
                         (fun acc_summ -> fun curr_q ->
                            let rule_opt = find_rule curr_q z in
                            match rule_opt with
                            | None -> acc_summ
                            | Some (new_lbl) ->
                              (* define edge here *)
                              let new_edge : Reachability_graph.edge =
                                {
                                  source = src;
                                  target = tgt';
                                  label = new_lbl
                                }
                              in
                              let new_summ_graph =
                                if (isFeasible_outgoing tgt tgt' new_lbl acc_summ) then
                                  Reachability_graph.insert_edge new_edge acc_summ.graph
                                else
                                  acc_summ.graph
                              in
                              let new_good_map =
                                let (new_q, _) = new_lbl in
                                match new_q with
                                | Incomplete | Complete ->
                                  Node_pair_to_Dstm_state_multimap.add
                                    (src, tgt') new_q acc_summ.good_map
                                | _ ->
                                  acc_summ.good_map
                              in
                              let new_item_on_worklist =
                                if (Node_pair_to_Dstm_tape_val_multimap.mem (src, tgt') z acc_summ.left_z)
                                then
                                  let (new_q, _) = new_lbl in
                                  match new_q with
                                  | Incomplete | Complete ->
                                    (new_edge, MaybeGray)
                                  | _ -> (new_edge, NotGray)
                                else (new_edge, NotGray)
                              in
                              let result_worklist =
                                if (not (Reachability_graph.contains_edge new_edge acc_summ.graph))
                                then
                                  List.append acc_summ.worklist [new_item_on_worklist]
                                else
                                  acc_summ.worklist
                              in
                              { acc_summ with
                                graph = new_summ_graph;
                                worklist = result_worklist;
                                good_map = new_good_map
                              }
                         ) summary_z_switched curr_right_mapping
                     in
                     (* FIXME: do we really need the right_q bit? *)
                     { resulting_summary with right_q = curr_sum.right_q }
                   )
                 else
                   (* the other case is not reflected in the algorithm, so
                      I guess we just return the original summary *)
                   curr_sum
               )
          ) intermediate_summary tgt_outgoing
      in
      (* INCOMING NEIGHBORS OF SRC *)
      let incoming_evaluation =
        Enum.fold
          (fun curr_sum -> fun (curr_inedge : (N.t * L.t)) ->
             let (src', _) = curr_inedge in
             let q_in_curr_right_q =
               Node_pair_to_Dstm_state_multimap.mem (src', tgt) q curr_sum.right_q
             in
             if (q_in_curr_right_q) then curr_sum
             else
               (
                 (* Adding q to R(src', tgt) *)
                 let summary_q_added =
                   { curr_sum with
                     right_q = Node_pair_to_Dstm_state_multimap.add (src', tgt) q curr_sum.right_q
                   }
                 in
                 let curr_left_z_bad_mapping =
                   Node_pair_to_Dstm_tape_val_multimap.find (src', tgt) summary_q_added.left_z_bad
                 in
                 (* foreach X \in Lb (k,j) do ... *)
                 let left_z_bad_eval_summary =
                   Enum.fold
                     (fun acc_summ -> fun curr_z ->
                        let rule_opt = find_rule q curr_z in
                        match rule_opt with
                        | None -> acc_summ
                        | Some (new_lbl) ->
                          (* define edge here *)
                          let new_edge : Reachability_graph.edge =
                            {
                              source = src';
                              target = tgt;
                              label = new_lbl
                            }
                          in
                          let new_summ_graph =
                            if (isFeasible_incoming src' src new_lbl acc_summ) then
                              Reachability_graph.insert_edge new_edge acc_summ.graph
                            else
                              acc_summ.graph
                          in
                          let new_worklist =
                            (* if (not (Reachability_graph.contains_edge new_edge acc_summ.graph))
                            then *)
                            List.append acc_summ.worklist [(new_edge, NotGray)]
                            (* else acc_summ.worklist *)
                          in
                          {acc_summ with
                           graph = new_summ_graph;
                           worklist = new_worklist
                          }
                     ) summary_q_added curr_left_z_bad_mapping
                 in
                 let curr_left_z_mapping =
                   Node_pair_to_Dstm_tape_val_multimap.find (src', tgt) left_z_bad_eval_summary.left_z
                 in
                 (* foreach X \in L(k,g) do ... *)
                 let left_z_eval_summary =
                   Enum.fold
                     (fun acc_summ -> fun curr_z ->
                        let rule_opt = find_rule q curr_z in
                        match rule_opt with
                        | None -> acc_summ
                        | Some (new_lbl) ->
                          (* define edge here *)
                          let new_edge : Reachability_graph.edge =
                            {
                              source = src';
                              target = tgt;
                              label = new_lbl
                            }
                          in
                          let new_summ_graph =
                            if (isFeasible_outgoing src' src new_lbl acc_summ) then
                              Reachability_graph.insert_edge new_edge acc_summ.graph
                            else
                              acc_summ.graph
                          in
                          let potential_new_worklist_item = (new_edge, MaybeGray) in
                          let new_summary =
                            let (new_q, _) = new_lbl in
                            match new_q with
                            | Incomplete | Complete ->
                              if (not (Node_pair_to_Dstm_state_multimap.mem (src', tgt) new_q acc_summ.good_map))
                              then
                                let new_good =
                                  Node_pair_to_Dstm_state_multimap.add
                                    (src', tgt) new_q acc_summ.good_map
                                in
                                {acc_summ with
                                 graph = new_summ_graph;
                                 worklist = List.append acc_summ.worklist [potential_new_worklist_item];
                                 good_map = new_good;
                                }
                              else
                              if (not (Reachability_graph.contains_edge new_edge acc_summ.graph))
                              then
                                {acc_summ with
                                 graph = new_summ_graph;
                                 worklist = List.append acc_summ.worklist [potential_new_worklist_item]
                                }
                              else
                                {acc_summ with graph = new_summ_graph}
                            | _ ->
                              if (not (Reachability_graph.contains_edge new_edge acc_summ.graph))
                              then
                                {acc_summ with
                                 graph = new_summ_graph;
                                 worklist = List.append acc_summ.worklist [potential_new_worklist_item]
                                }
                              else
                                {acc_summ with graph = new_summ_graph}
                          in
                          new_summary
                     ) left_z_bad_eval_summary curr_left_z_mapping
                 in
                 left_z_eval_summary
               )
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
