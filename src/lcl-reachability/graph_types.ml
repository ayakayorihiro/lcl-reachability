open Batteries;;

open Utils;;

(* Data type signature for generic graph *)
module type Graph =
sig

  (* Type of graph created by the Graph_type module *)
  type t [@@deriving eq, show]
  module Node : Decorated_type
  module Label : Decorated_type

  (* Node functions... *)
  val node_set : t -> Node.t list
  val contains_node : Node.t -> t -> bool
  (* val show_node_set : Node.t list -> string *)

  val empty : t

  type edge =
    {
      source : Node.t
    ; target : Node.t
    ; label : Label.t
    } [@@deriving eq, show]
  ;;

  (* Edge functions... Why is merlin unhappy w edge *)
  val contains_edge : edge -> t -> bool
  val insert_edge : edge -> t -> t
  val remove_edge : edge -> t -> t
  val get_all_edges : t -> edge Enum.t

  val get_outgoing_neighbors : Node.t -> t -> (Node.t * Label.t) list
  val get_incoming_neighbors : Node.t -> t -> (Node.t * Label.t) list

end;;

module Make
    (N : Decorated_type)
    (L : Decorated_type)
  : Graph with module Node = N and module Label = L
=
struct
  module Node = N
  module Label = L

  module Node_Label_pair =
  struct
    type t = (Node.t * Label.t) [@@deriving ord, show]
  end;;

  module Node_set =
  struct
    module S = BatSet.Make(Node);;
    include S;;
    include Jhupllib.Pp_utils.Set_pp(S)(Node);;
  end;;

  module NL_set =
  struct
    module S = BatSet.Make(Node_Label_pair);;
    include S;;
    include Jhupllib.Pp_utils.Set_pp(S)(Node_Label_pair);;
  end;;

  module Node_map =
  struct
    module M = BatMap.Make(Node);;
    include M;;
    include Jhupllib.Pp_utils.Map_pp(M)(Node);;
  end;;

  (* TODO: add multimap routines as functions
    * use Node_map.Exceptionless.find
  *)
  type edge =
    {
      source : Node.t
    ; target : Node.t
    ; label : Label.t
    } [@@deriving eq, show]
  ;;

  type t =
    { outgoing_map : NL_set.t Node_map.t ;
      incoming_map : NL_set.t Node_map.t ;
      nodes : Node_set.t
    } [@@deriving eq, show]

  let empty =
    {
      outgoing_map = Node_map.empty;
      incoming_map = Node_map.empty;
      nodes = Node_set.empty
    }

  let node_set (graph : t) =
    Node_set.to_list graph.nodes
  ;;

  let contains_node (n : Node.t) (graph : t) : bool =
    let res = Node_set.Exceptionless.find n graph.nodes in
    match res with
    | None -> false
    | _ -> true
  ;;

  let contains_edge (e : edge) (graph : t) : bool =
    let src = e.source in
    let target_label = (e.target, e.label) in
    let res = Node_map.Exceptionless.find src graph.outgoing_map in
    match res with
    | None -> false
    | Some (src_outgoing_set) ->
      let res' = NL_set.Exceptionless.find target_label src_outgoing_set in
      match res' with
      | None -> false
      | _ -> true
  ;;

  let insert_edge (e : edge) (graph : t) : t =
    let src = e.source in
    let target_label = (e.target, e.label) in
    (* Editing the outgoing set... *)
    let res = Node_map.Exceptionless.find src graph.outgoing_map in
    let new_src_outgoing_set =
      let curr_set =
        match res with
        | None ->
          NL_set.empty
        | Some (src_outgoing_set) ->
          src_outgoing_set
      in
      NL_set.add target_label curr_set
    in
    let new_outgoing_map = Node_map.add src new_src_outgoing_set graph.outgoing_map in
    (* Editing the incoming map... *)
    let tgt = e.target in
    let src_label = (e.source, e.label) in
    let res' = Node_map.Exceptionless.find tgt graph.incoming_map in
    let new_tgt_incoming_set =
      let curr_set' =
        match res' with
        | None ->
          NL_set.empty
        | Some (tgt_incoming_Set) ->
          tgt_incoming_Set
      in
      NL_set.add src_label curr_set'
    in
    let new_incoming_map = Node_map.add tgt new_tgt_incoming_set graph.incoming_map in
    (* Add to the general set of nodes... *)
    let new_node_set = Node_set.add src (Node_set.add tgt graph.nodes) in
    {
      outgoing_map = new_outgoing_map;
      incoming_map = new_incoming_map;
      nodes = new_node_set
    }
  ;;

  let remove_edge (e : edge) (graph : t) : t =
    let src = e.source in
    let target_label = (e.target, e.label) in
    (* Erasing from outgoing edge...*)
    let res = Node_map.Exceptionless.find src graph.outgoing_map in
    let new_src_outgoing_set =
      match res with
      | None ->
        NL_set.empty
      | Some (src_outgoing_set) ->
        NL_set.remove target_label src_outgoing_set
    in
    let new_outgoing_map =
      Node_map.add src new_src_outgoing_set graph.outgoing_map in
    (* Erasing from incoming edges...*)
    let tgt = e.target in
    let src_label = (e.source, e.label) in
    let res' = Node_map.Exceptionless.find tgt graph.incoming_map in
    let new_tgt_incoming_set =
      match res' with
      | None ->
        NL_set.empty
      | Some (tgt_incoming_set) ->
        NL_set.remove src_label tgt_incoming_set
    in
    let new_incoming_map =
      Node_map.add tgt new_tgt_incoming_set graph.incoming_map in
    {
      outgoing_map = new_outgoing_map;
      incoming_map = new_incoming_map;
      nodes = graph.nodes
    }
  ;;

  let get_all_edges (graph : t) : edge Enum.t =
    let edge_map = graph.outgoing_map in
    let n_nl_set_enum = Node_map.enum edge_map in
    let n_nl_enum =
      Enum.map (fun (k, nl_set) ->
          let new_snd = NL_set.enum nl_set in
          Enum.map
            (fun nl -> (k, nl)) new_snd
        )
        n_nl_set_enum
      |> Enum.concat
    in
    (* At this point, we have an enum (k, (n, l)) *)
    Enum.map
      (fun (src, (tgt, lbl)) ->
         {
           source = src;
           target = tgt;
           label = lbl
         }
      )
      n_nl_enum
  ;;

  let get_outgoing_neighbors (src : Node.t) (graph : t) :
    (Node.t * Label.t) list =
    let outgoing_edge_set = Node_map.find_default NL_set.empty src graph.outgoing_map
    in
    NL_set.elements outgoing_edge_set
  ;;

  let get_incoming_neighbors (tgt : Node.t) (graph : t) :
    (Node.t * Label.t) list =
    let incoming_edge_set = Node_map.find_default NL_set.empty tgt graph.incoming_map
    in
    NL_set.elements incoming_edge_set
  ;;


end;;
