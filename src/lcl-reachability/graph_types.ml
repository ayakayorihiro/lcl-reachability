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

  val get_outgoing_neighbors : Node.t -> t -> (Node.t * Label.t) Enum.t
  val get_incoming_neighbors : Node.t -> t -> (Node.t * Label.t) Enum.t

  val get_labels : (Node.t * Node.t) -> t -> Label.t Enum.t
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

  module Node_pair =
  struct
    type t = (Node.t * Node.t) [@@deriving ord, show]
  end;;

  module Node_set =
  struct
    module S = BatSet.Make(Node);;
    include S;;
    include Jhupllib.Pp_utils.Set_pp(S)(Node);;
  end;;

  (* module Label_set =
  struct
    module S = BatSet.Make(Label);;
    include S;;
    include Jhupllib.Pp_utils.Set_pp(S)(Label);;
  end;;

  module NL_set =
  struct
    module S = BatSet.Make(Node_Label_pair);;
    include S;;
    include Jhupllib.Pp_utils.Set_pp(S)(Node_Label_pair);;
  end;;

  module Node_Node_pair_map =
  struct
    module M = BatMap.Make(Node_Node_pair);;
    include M;;
    include Jhupllib.Pp_utils.Map_pp(M)(Node_Node_pair);;
  end;; *)

  module Node_map =
  struct
    module M = BatMap.Make(Node);;
    include M;;
    include Jhupllib.Pp_utils.Map_pp(M)(Node);;
  end;;

  module Node_NL_set_multimap =
  struct
    module Impl = Jhupllib.Multimap.Make(Node)(Node_Label_pair);;
    include Impl;;
    include Jhupllib.Multimap_pp.Make(Impl)(Node)(Node_Label_pair);;
  end;;

  module Node_pair_Label_multimap =
  struct
    module Impl = Jhupllib.Multimap.Make(Node_pair)(Label);;
    include Impl;;
    include Jhupllib.Multimap_pp.Make(Impl)(Node_pair)(Label);;
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
    { outgoing_map : Node_NL_set_multimap.t ;
      incoming_map : Node_NL_set_multimap.t ;
      label_map : Node_pair_Label_multimap.t;
      nodes : Node_set.t
    } [@@deriving eq, show]

  let empty =
    {
      outgoing_map = Node_NL_set_multimap.empty;
      incoming_map = Node_NL_set_multimap.empty;
      label_map = Node_pair_Label_multimap.empty;
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
    Node_NL_set_multimap.mem src target_label graph.outgoing_map
  ;;

  let insert_edge (e : edge) (graph : t) : t =
    let src = e.source in
    let target_label = (e.target, e.label) in
    (* Editing the outgoing set... *)
    let new_outgoing_map =
      Node_NL_set_multimap.add src target_label graph.outgoing_map
    in
    (* Editing the incoming map... *)
    let tgt = e.target in
    let src_label = (e.source, e.label) in
    let new_incoming_map =
      Node_NL_set_multimap.add tgt src_label graph.incoming_map
    in
    (* Add to the label set... *)
    let srctgt = (e.source, e.target) in
    let new_label_map =
      Node_pair_Label_multimap.add srctgt e.label graph.label_map
    in
    (* Add to the general set of nodes... *)
    let new_node_set = Node_set.add src (Node_set.add tgt graph.nodes) in
    {
      outgoing_map = new_outgoing_map;
      incoming_map = new_incoming_map;
      label_map = new_label_map;
      nodes = new_node_set
    }
  ;;

  let remove_edge (e : edge) (graph : t) : t =
    let src = e.source in
    let target_label = (e.target, e.label) in
    (* Erasing from outgoing edge...*)
    let new_outgoing_map =
      Node_NL_set_multimap.remove src target_label graph.outgoing_map
    in
    (* Erasing from incoming edges...*)
    let tgt = e.target in
    let src_label = (e.source, e.label) in
    let new_incoming_map =
      Node_NL_set_multimap.remove tgt src_label graph.incoming_map
    in
    (* Erasing from label map... *)
    let srctgt = (src, tgt) in
    let new_label_map =
      Node_pair_Label_multimap.remove srctgt e.label graph.label_map
    in
    {
      outgoing_map = new_outgoing_map;
      incoming_map = new_incoming_map;
      label_map = new_label_map;
      nodes = graph.nodes
    }
  ;;

  let get_all_edges (graph : t) : edge Enum.t =
    let edge_map = graph.outgoing_map in
    let n_nl_multimap_enum = Node_NL_set_multimap.enum edge_map in
    (* At this point, we have an enum *)
    (* let n_nl_enum =
      Enum.map (fun (k, nl_set) ->
          let new_snd = NL_set.enum nl_set in
          Enum.map
            (fun nl -> (k, nl)) new_snd
        )
        n_nl_set_enum
      |> Enum.concat
    in *)
    (* At this point, we have an enum (k, (n, l)) *)
    Enum.map
      (fun (src, (tgt, lbl)) ->
         {
           source = src;
           target = tgt;
           label = lbl
         }
      )
      n_nl_multimap_enum
  ;;

  let get_outgoing_neighbors (src : Node.t) (graph : t) :
    (Node.t * Label.t) Enum.t =
    Node_NL_set_multimap.find src graph.outgoing_map
    (* let outgoing_edge_set = Node_map.find_default NL_set.empty src graph.outgoing_map
    in
    NL_set.elements outgoing_edge_set *)
  ;;

  let get_incoming_neighbors (tgt : Node.t) (graph : t) :
    (Node.t * Label.t) Enum.t =
    Node_NL_set_multimap.find tgt graph.incoming_map
  ;;

  (* val get_labels : (Node.t * Node.t) -> t -> Label.t list  *)
  let get_labels (srctgt : Node.t * Node.t) (graph : t) : Label.t Enum.t =
    Node_pair_Label_multimap.find srctgt graph.label_map
  ;;

end;;
