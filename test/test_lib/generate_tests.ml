open Batteries;;
open OUnit2;;
open Lcl_reachability.Stack_utils;;

module Closure = Lcl_reachability.Closure;;
module Closure2 = Lcl_reachability.Closure_algorithm2;;
module New_closure = Lcl_reachability.New_closure;;
module Graph_types = Lcl_reachability.Graph_types;;

type probabilities = {terminal : int; nest : int; concat : int};;

let initial_probabilities : probabilities =
  {
    terminal = 10;
    nest = 100;
    concat = 100
  }
;;

let nest_factor = 0.9;;
let concat_factor = 0.8;;

(* returns a list of numbers, as well as the new count *)
let rec create_string (p : probabilities) (curr_count : int)
  : (int stack_action_lcl list * int)
  =
  let aggregate = p.terminal + p.nest + p.concat in
  let choice = Random.int aggregate in
  if (choice <= p.terminal) then
    (* let _ = print_endline "rule 1 chosen" in *)
    (* 1. s = () *)
    (* terminal case - open + close *)
    ([Push (curr_count); Pop(curr_count)], curr_count)
  else
  if (choice <= (p.terminal + p.nest)) then
    (* let _ = print_endline "rule 2 chosen" in *)
    (* 2. s = (s1) *)
    (* we recurse once and put the current one in the beginning & the end *)
    let change = int_of_float @@ (float_of_int p.nest) *. nest_factor in
    let new_probabilities =
      {
        terminal = p.terminal + change;
        nest = p.nest - change;
        concat = p.concat
      }
    in
    let (inside, new_count) = create_string new_probabilities curr_count in
    let (top : int stack_action_lcl list) = [Push (new_count + 1)] in
    (top @ inside @ [Pop (new_count + 1)], new_count + 1)
  else
    (* let _ = print_endline "rule 3 chosen" in *)
    (* 3. s = s1 s2 *)
    let change = int_of_float @@ (float_of_int p.nest) *. concat_factor in
    (* We recurse twice and concat the results *)
    let new_probabilities =
      {
        terminal = p.terminal + change;
        nest = p.nest;
        concat = p.concat - change
      }
    in
    let (s1, new_count1) = create_string new_probabilities curr_count in
    let (s2, new_count2) = create_string new_probabilities (new_count1 + 1) in
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
  type t = ((Generated_test_stack_elm.t, Generated_test_stack_elm.t) choice) stack_action_lcl
  [@@deriving eq, ord, show]
end;;

module Generated_test_graph =
  Graph_types.Make(Generated_test_node)(Generated_test_label);;

module Test_reachability =
  New_closure.Make
    (Generated_test_stack_elm)
    (Generated_test_stack_elm)
    (Generated_test_graph);;

let add_edge_w_right_stack
    (lst : int stack_action_lcl list)
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
    (lst : int stack_action_lcl list)
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
    (lst_1 : int stack_action_lcl list)
    (lst_2 : int stack_action_lcl list)
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

let create_interleaving_graph_wrapper () =
  let (string_1, _) = create_string initial_probabilities 0 in
  (* print_endline "string 1 done"; *)
  let (string_2, _) = create_string initial_probabilities 0 in
  (* print_endline "string 2 done"; *)
  create_interleaving_graph string_1 string_2 Generated_test_graph.empty 0
;;

let make_test (n : int) : test =
  let (generated_test_graph, last_node) =
    create_interleaving_graph_wrapper ()
  in
  "Test " ^ string_of_int n >:: fun _ ->
    let initial_summary = Test_reachability.create_initial_summary generated_test_graph in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable 0 last_node final_summary in
    assert_bool "generated_test_fail" reachable
;;

let generated_tests =
  List.of_enum
    (1---1000
     |> Enum.map
       (fun n ->
          Random.init n;
          make_test n
       )
    )
;;

(* let first_generated_test =
   "first_generated_test" >:: fun _ ->
    (* let _ = Random.init  *)
    let (generated_test_graph, last_node) =
      create_interleaving_graph_wrapper ()
    in
    let initial_summary = Test_reachability.create_initial_summary generated_test_graph in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable 0 last_node final_summary in
    assert_bool "generated_test_fail" reachable
   ;; *)

(* want to generate a list of units and then write a function converting a unit
   to a test element (most likely following the first_generated_test)...
   then do list.map on that
*)

let tests = "Generated_tests" >:::
            generated_tests
;;
