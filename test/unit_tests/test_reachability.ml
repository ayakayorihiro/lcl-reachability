(**
   This test module performs a series of operations to test the PDA reachability
   functionality in the Odefa analysis library.
*)

(* open Batteries;;
   open Jhupllib;; *)
open OUnit2;;
open Lcl_reachability.Stack_utils;;

module Closure = Lcl_reachability.Closure;;
module Closure2 = Lcl_reachability.Closure_algorithm2;;
module New_closure = Lcl_reachability.New_closure;;
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

module Test_label =
struct
  type t = ((Test_stack_elm_1.t, Test_stack_elm_2.t) choice) stack_action
  [@@deriving eq, ord, show]
end;;

module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_reachability_1 =
  New_closure.Make
    (Test_stack_elm_1)(Test_stack_elm_2)
    (Test_graph);;

module Test_reachability =
  New_closure.Make
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
    let reachable = Test_reachability.reachable "u" "v" final_summary in
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

let two_crossing_reachability_test =
  "double_crossing_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Push(Right(2))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Pop(Left(1))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = Push(Left(3))}
      |> Test_graph.insert_edge
        {source = "e"; target = "f"; label = Pop(Right(2))}
      |> Test_graph.insert_edge
        {source = "f"; target = "g"; label = Pop(Left(3))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "g" final_summary in
    assert reachable
;;

let loop_base_case =
  "loop_base_case" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "a"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "a"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "a" final_summary in
    assert reachable
;;

let two_node_loop_fst =
  "two_node_loop_fst" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "a"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "b" final_summary in
    assert reachable
;;

let two_node_loop_snd =
  "loop_base_case" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "b"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "b" final_summary in
    assert reachable
;;

let triangle_reachable =
  "triangle_reachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Pop(Left(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Push(Right(10))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "c" final_summary in
    assert reachable
;;

(* This test is testing whether sth that is supposed to be UNREACHABLE actually is. *)
let triangle_unreachable =
  "triangle_unreachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Pop(Right(2))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "c" final_summary in
    assert (not reachable)
;;

let square_reachable =
  "square_reachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "d"; label = Pop(Left(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Push(Right(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Pop(Right(2))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert reachable
;;

(* This is an example of the improcision of the algorithm.
   This is because the two paths a --> d share result and target,
   and as an result it ends up conflating added edges.
*)
let square_unreachable =
  "square_unreachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "d"; label = Pop(Right(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Push(Right(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert (reachable)
;;

(* NOTE: refer to above *)
let non_square_unreachable =
  "non_square_unreachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Push(Left(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "e"; label = Pop(Right(1))}
      |> Test_graph.insert_edge
        {source = "e"; target = "d"; label = Pop(Right(100))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Push(Right(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Pop(Left(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert (reachable)
;;


let tests = "Test_reachability" >:::
            [
              single_reachability_test
            ; simple_double_reachability_test
            ; embedded_double_reachability_test
            ; crossing_double_reachability_test
            ; separate_triple_reachability_test
            ; two_crossing_reachability_test
            ; loop_base_case
            ; two_node_loop_fst
            ; two_node_loop_snd
            ; triangle_reachable
            ; triangle_unreachable
            ; square_reachable
            ; square_unreachable
; non_square_unreachable
            ]
;;
