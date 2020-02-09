open Batteries;;
open OUnit2;;
open Lcl_reachability.Stack_utils;;

module Closure = Lcl_reachability.Closure;;
module Closure2 = Lcl_reachability.Closure_algorithm2;;
module Graph_types = Lcl_reachability.Graph_types;;

type probabilities = {terminal : int; nest : int; concat : int};;

let initial_probabilities : probabilities =
  {
    terminal = 20;
    nest = 30;
    concat = 50
  }
;;

(* returns a list of numbers, as well as the new count *)
let rec create_string (p : probabilities) (seed : int) (curr_count : int)
  : (int stack_action list * int)
  =
  let _ = Random.init seed in
  let aggregate = p.terminal + p.nest + p.concat in
  let choice = Random.int aggregate in
  if (choice <= p.terminal) then
    (* 1. s = () *)
    (* terminal case - open + close *)
    ([Push (curr_count); Pop(curr_count)], curr_count)
  else
  if (choice <= (p.terminal + p.nest)) then
    (* 2. s = (s1) *)
    (* we recurse once and put the current one in the beginning & the end *)
    let change = p.nest/5 in
    let new_probabilities =
      {
        terminal = p.terminal + change;
        nest = p.nest - change;
        concat = p.concat
      }
    in
    let (inside, new_count) = create_string new_probabilities seed curr_count in
    ([Push (new_count + 1)] @ inside @ [Pop (new_count + 1)], new_count + 1)
  else
    (* 3. s = s1 s2 *)
    (* We recurse twice and concat the results *)
    let change = p.concat/3 in
    let new_probabilities =
      {
        terminal = p.terminal + change;
        nest = p.nest;
        concat = p.concat - change
      }
    in
    let (s1, new_count1) = create_string new_probabilities seed curr_count in
    let (s2, new_count2) = create_string new_probabilities seed new_count1 in
    (s1 @ s2, new_count2)
;;

module Generated_test_node =
struct
  type t = int
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Generated_test_stack_elm =
struct
  type t = int
  (* type alphabet = int  *)
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Generated_test_label =
struct
  type t = ((Generated_test_stack_elm.t, Generated_test_stack_elm.t) choice) stack_action
  [@@deriving eq, ord, show]
end;;

module Generated_test_graph =
  Graph_types.Make(Generated_test_node)(Generated_test_label);;

  module Test_reachability =
    Closure2.Make
      (Generated_test_stack_elm)(Generated_test_stack_elm)
      (Generated_test_graph);;

let add_edge_w_right_stack
    (lst : int stack_action list)
    (graph : Generated_test_graph.t)
    (curr_last_node : int)
  =
  let new_edge : Generated_test_graph.edge =
    match List.hd lst with
    | Push n ->
      {source = curr_last_node; target = curr_last_node + 1;
       label = Push(Right(n))}
    | Pop n ->
      {source = curr_last_node; target = curr_last_node + 1;
       label = Pop(Right(n))}
    | _ -> failwith "epsilon"
  in
  Generated_test_graph.insert_edge new_edge graph
;;

let add_edge_w_left_stack
    (lst : int stack_action list)
    (graph : Generated_test_graph.t)
    (curr_last_node : int)
  =
  let new_edge : Generated_test_graph.edge =
    match List.hd lst with
    | Push n ->
      {source = curr_last_node; target = curr_last_node + 1;
       label = Push(Left(n))}
    | Pop n ->
      {source = curr_last_node; target = curr_last_node + 1;
       label = Pop(Left(n))}
    | _ -> failwith "epsilon"
  in
  Generated_test_graph.insert_edge new_edge graph
;;


(* Function creating single interleaving graph *)
let rec create_interleaving_graph
    (lst_1 : int stack_action list)
    (lst_2 : int stack_action list)
    (graph : Generated_test_graph.t)
    (curr_last_node : int)
  : (Generated_test_graph.t * int)
  =
  if (List.is_empty lst_1 && List.is_empty lst_2) then
    (* if both are empty, then we're done *)
    (graph, curr_last_node)
  else
  if (List.is_empty lst_1) then
    (* We just want to keep adding things from our second list *)
    let new_graph = add_edge_w_right_stack (lst_2) graph curr_last_node in
    create_interleaving_graph lst_1 (List.tl lst_2) new_graph (curr_last_node + 1)
  else
  if (List.is_empty lst_2) then
    (* We just want to keep adding things from our first list *)
    let new_graph = add_edge_w_left_stack lst_1 graph curr_last_node in
    create_interleaving_graph (List.tl lst_1) lst_2 new_graph (curr_last_node + 1)
  else
    let _ = Random.self_init () in
    let choice = Random.bool () in
    if (choice) then
      (* we take the head from lst_1 *)
      let new_graph = add_edge_w_left_stack lst_1 graph curr_last_node in
      create_interleaving_graph (List.tl lst_1) lst_2 new_graph (curr_last_node + 1)
    else
      (* we take the head from lst_2 *)
      let new_graph = add_edge_w_right_stack (lst_2) graph curr_last_node in
      create_interleaving_graph lst_1 (List.tl lst_2) new_graph (curr_last_node + 1)
;;

let create_interleaving_graph_wrapper (seed_1 : int) (seed_2 : int) =
  let (string_1, _) = create_string initial_probabilities seed_1 0 in
  print_endline "string 1 done";
  let (string_2, _) = create_string initial_probabilities seed_2 0 in
  print_endline "string 2 done";
  create_interleaving_graph string_1 string_2 Generated_test_graph.empty 0
;;

let first_generated_test =
  "first_generated_test" >:: fun _ ->
    let (generated_test_graph, last_node) =
      create_interleaving_graph_wrapper 10 100
    in
    let initial_summary = Test_reachability.create_initial_summary generated_test_graph in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable 0 last_node final_summary in
    assert_bool "generated_test_fail" reachable
;;

let tests = "Generated_tests" >:::
            [first_generated_test

            ]
;;
