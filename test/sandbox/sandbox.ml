open Jhupllib.Logger_utils;;

(* open OUnit2;; *)
(* open Lcl_reachability_tests;; *)
open Lcl_reachability.Stack_utils;;
(* open Lcl_reachability.Utils;; *)

module Closure = Lcl_reachability.Closure;;
module Closure2 = Lcl_reachability.Closure_algorithm2;;
module New_closure = Lcl_reachability.New_closure;;
module Three_stack_reachability = Lcl_reachability.Three_stack_reachability;;
module Graph_types = Lcl_reachability.Graph_types;;

set_default_logging_level `trace;;


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
  (* type alphabet = int  *)
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Test_stack_elm_2 =
struct
  type t = int
  (* let alphabet = [1;2;3;4;5] *)
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

(* NOTE: Uncomment below for two stack testing *)
(* module Test_label =
struct
  type t = ((Test_stack_elm_1.t, Test_stack_elm_2.t) choice) stack_action
  [@@deriving eq, ord, show]
end;;
module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_reachability =
  New_closure.Make
    (Test_stack_elm_1)(Test_stack_elm_2)
    (Test_graph);; *)

(* NOTE: Test_label and Test_graph for three stack testing *)
module Test_label =
struct
  type t = ((Test_stack_elm_1.t, Test_stack_elm_1.t, Test_stack_elm_1.t) three_stack) stack_action
  [@@deriving eq, ord, show]
end;;

module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_three_stack_reachability =
  Three_stack_reachability.Make
    (Test_stack_elm_1)(Test_stack_elm_1)(Test_stack_elm_1)
    (Test_graph);;


let test_graph =
  Test_graph.empty
  |> Test_graph.insert_edge
    {source = "start"; target = "start"; label = Push(StackA(1))}
  |> Test_graph.insert_edge
    {source = "start"; target = "start"; label = Pop(StackA(1))}
;;

(* NOTE: Uncomment below for two stack testing *)
(* let initial_summary = Test_reachability.create_initial_summary test_graph;;
let final_summary = Test_reachability.step_to_closure initial_summary;;
let reachable = Test_reachability.reachable "a" "c" final_summary;;
print_endline "=====================";;
   print_endline (string_of_bool reachable);; *)

   let initial_summary = Test_three_stack_reachability.create_initial_summary test_graph;;
   let final_summary = Test_three_stack_reachability.step_to_closure initial_summary;;
let reachable = Test_three_stack_reachability.reachable "start" "start" final_summary;;
   print_endline "=====================";;
   print_endline (string_of_bool reachable);;

(* let test_graph =
  Generate_tests.Generated_test_graph.empty
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 0; target = 1; label = Push(Right(4))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 1; target = 2; label = Push(Left(10))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 2; target = 3; label = Push(Right(0))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 3; target = 4; label = Push(Left(0))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 4; target = 5; label = Pop(Left(0))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 5; target = 6; label = Push(Left(1))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 6; target = 7; label = Pop(Left(1))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 7; target = 8; label = Pop(Right(0))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 8; target = 9; label = Push(Left(2))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 9; target = 10; label = Push(Right(1))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 10; target = 11; label = Pop(Left(2))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 11; target = 12; label = Pop(Right(1))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 12; target = 13; label = Push(Right(2))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 13; target = 14; label = Push(Left(5))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 14; target = 15; label = Pop(Right(2))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 15; target = 16; label = Push(Right(3))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 16; target = 17; label = Push(Left(3))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 17; target = 18; label = Pop(Left(3))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 18; target = 19; label = Push(Left(4))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 19; target = 20; label = Pop(Right(3))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 20; target = 21; label = Pop(Right(4))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 21; target = 22; label = Pop(Left(4))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 22; target = 23; label = Pop(Left(5))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 23; target = 24; label = Push(Right(6))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 24; target = 25; label = Push(Right(5))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 25; target = 26; label = Push(Left(6))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 25; target = 27; label = Pop(Right(5))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 27; target = 28; label = Pop(Right(6))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 28; target = 29; label = Pop(Left(6))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 29; target = 30; label = Push(Left(7))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 30; target = 31; label = Pop(Left(7))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 31; target = 32; label = Push(Left(8))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 32; target = 33; label = Pop(Left(8))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 33; target = 34; label = Push(Left(9))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 34; target = 35; label = Pop(Left(9))}
  |> Generate_tests.Generated_test_graph.insert_edge
    {source = 35; target = 36; label = Pop(Left(10))}
;; *)

(*
Random.init 8;;

let (generated_test_graph, last_node) =
  Generate_tests.create_interleaving_graph_wrapper ()
   in
(* let _ = print_endline @@ string_of_bool @@ Generate_tests.Generated_test_graph.equal generated_test_graph test_graph in *)
(* let _ = print_endline "---interleaving graph created---" in *)
(* let _ = print_endline @@ Generate_tests.Generated_test_graph.show generated_test_graph in *)
let initial_summary = Test_reachability.create_initial_summary generated_test_graph in
let final_summary = Test_reachability.step_to_closure initial_summary in
let reachable = Test_reachability.reachable 0 last_node final_summary in
(* assert_bool "generated_test_fail" reachable *)
print_endline @@ string_of_bool reachable
;;
*)

(* want to generate a list of units and then write a function converting a unit
   to a test element (most likely following the first_generated_test)...
   then do list.map on that

*)
(* let tests = "Generated_tests" >:::
            [first_generated_test
            ]
;;

let () =
  run_test_tt_main ("Tests" >::: [tests])
;; *)
