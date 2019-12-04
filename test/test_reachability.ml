(**
   This test module performs a series of operations to test the PDA reachability
   functionality in the Odefa analysis library.
*)

(* open Batteries;;
open Jhupllib;; *)
open OUnit2;;
open Lcl_reachability.Stack_utils;;

module Closure = Lcl_reachability.Closure;;
module Graph_types = Lcl_reachability.Graph_types;;

module Test_node =
struct
  type t = string
  let equal = (==)
  let compare = compare
  let pp fmt s = Format.pp_print_string fmt s
  let show s = s
end;;

module Test_stack_elm_1 =
struct
  type t = int
  let alphabet = [1;2;3;4;5]
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Test_stack_elm_2 =
struct
  type t = int
  let alphabet = [1;2;3;4;5]
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Test_label =
struct
  type t = ((Test_stack_elm_1.t, Test_stack_elm_2.t) choice) stack_action
      [@@deriving eq, ord, show]
end;;

module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_reachability =
  Closure.Make
    (Test_stack_elm_1)(Test_stack_elm_2)
    (Test_graph);;

let single_reachability_test =
  "single_reachability_test" >:: fun _ ->
    let open Test_graph in
    let test =
      Test_graph.empty
      |> insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> insert_edge
        {source = "b"; target = "c"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "c" final_summary in
    assert_bool "() FAIL" reachable
;;

let simple_double_reachability_test =
  "simple_double_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Pop(Left(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Push(Right(2))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = Pop(Right(2))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "e" final_summary in
    assert_bool "() [] FAIL" reachable
;;

let crossing_double_reachability_test =
  "crossing_double_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "u"; target = "x"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "x"; target = "w"; label = Push(Right(2))}
      |> Test_graph.insert_edge
        {source = "w"; target = "y"; label = Pop(Left(1))}
      |> Test_graph.insert_edge
        {source = "y"; target = "v"; label = Pop(Right(2))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "e" final_summary in
    assert_equal reachable true
;;

let embedded_double_reachability_test =
  "embedded_double_reachability_test" >:: fun _ ->
    let test =
    Test_graph.empty
    |> Test_graph.insert_edge
      {source = "a"; target = "b"; label = Push(Left(1))}
    |> Test_graph.insert_edge
      {source = "b"; target = "c"; label = Push(Right(2))}
    |> Test_graph.insert_edge
      {source = "c"; target = "d"; label = Pop(Right(2))}
    |> Test_graph.insert_edge
      {source = "d"; target = "e"; label = Pop(Left(1))}
  in
  let initial_summary = Test_reachability.create_initial_summary test in
  let final_summary = Test_reachability.step_to_closure initial_summary in
  let reachable = Test_reachability.reachable "a" "e" final_summary in
  assert_equal reachable true
;;

let separate_triple_reachability_test =
  "separate_triple_reachability_test" >:: fun _ ->
  let test =
  Test_graph.empty
  |> Test_graph.insert_edge
    {source = "a"; target = "b"; label = Push(Left(1))}
  |> Test_graph.insert_edge
    {source = "b"; target = "c"; label = Push(Right(2))}
  |> Test_graph.insert_edge
    {source = "c"; target = "d"; label = Pop(Right(2))}
  |> Test_graph.insert_edge
    {source = "d"; target = "e"; label = Pop(Left(1))}
  |> Test_graph.insert_edge
    {source = "e"; target = "f"; label = Push(Left(3))}
  |> Test_graph.insert_edge
    {source = "f"; target = "g"; label = Pop(Left(3))}
  in
  let initial_summary = Test_reachability.create_initial_summary test in
  let final_summary = Test_reachability.step_to_closure initial_summary in
  let reachable = Test_reachability.reachable "a" "g" final_summary in
  assert_equal reachable true
;;

let tests = "Test_reachability" >:::
            [
              (* single_reachability_test
            ; simple_double_reachability_test
            ; embedded_double_reachability_test *)
            crossing_double_reachability_test
            (* ; separate_triple_reachability_test *)
            ]
;;
