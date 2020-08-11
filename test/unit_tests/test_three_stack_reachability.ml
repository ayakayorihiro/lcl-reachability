(**
   This test module performs a series of operations to test the PDA reachability
   functionality in the Odefa analysis library.
*)

(* open Batteries;;
   open Jhupllib;; *)
open OUnit2;;
open Lcl_reachability.Stack_utils;;

module Reachability = Lcl_reachability.Three_stack_reachability;;
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

module Test_stack_predicate_1 =
struct
  type t =
    | Negative
    | Search
    | Replace
  ;;
  module Grammar = Test_stack_elm_1
  let exec_pred (pred : t) (x : Grammar.t) =
    match pred with
    | Negative ->
      (x < 0)
    | Search -> x = 1000
    | Replace -> x = 2000
  ;;
  let equal p1 p2 = p1 = p2;;
  let compare p1 p2 =
    match p1 with
    | Negative ->
      begin
        match p2 with
        | Negative -> 0
        | Search -> -1
        | Replace -> -2
      end
    | Search ->
      begin
        match p2 with
        | Negative -> 1
        | Search -> 0
        | Replace -> -1
      end
    | Replace ->
      begin
        match p2 with
        | Negative -> 2
        | Search -> 1
        | Replace -> 0
      end
  let show p =
    match p with
    | Negative -> "Negative"
    | Search -> "Search"
    | Replace -> "Replace"
  ;;
  let pp formatter p =
    Format.pp_print_string formatter (show p)
  ;;
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

module Test_stack_predicate_2 : StackElementPredicates with module Grammar = Test_stack_elm_2
=
struct
  type t = ..;; (* FIXME: what is ..*)
  module Grammar = Test_stack_elm_2;;
  let exec_pred _ _ = false;;  (* dummy code which will never be executed *)
  let equal _ _ = false;;
  let compare _ _ = -1;;
  let show _ = "stack pred 2";;
  let pp _ _ = ();;
end;;

module Test_stack_elm_3 =
struct
  type t = int
  (* let alphabet = [1;2;3;4;5] *)
  let equal = (==)
  let compare = compare
  let pp = Format.pp_print_int
  let show = string_of_int
end;;

module Test_stack_predicate_3 : StackElementPredicates with module Grammar = Test_stack_elm_3
=
struct
  type t = ..;; (* FIXME: what is ..*)
  module Grammar = Test_stack_elm_3;;
  let exec_pred _ _ = false;;  (* dummy code which will never be executed *)
  let equal _ _ = false;;
  let compare _ _ = -1;;
  let show _ = "stack pred 2";;
  let pp _ _ = ();;
end;;


module Test_label =
struct
  type t =
    (((Test_stack_elm_1.t, Test_stack_predicate_1.t) stack_action),
     ((Test_stack_elm_2.t, Test_stack_predicate_2.t) stack_action),
     ((Test_stack_elm_3.t, Test_stack_predicate_3.t) stack_action)) trinary
  [@@deriving eq, ord, show]
end;;

module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_reachability =
  Reachability.Make
    (Test_stack_elm_1)(Test_stack_predicate_1)
    (Test_stack_elm_2)(Test_stack_predicate_2)
    (Test_stack_elm_3)(Test_stack_predicate_3)
    (Test_graph);;

let single_reachability_test =
  "single_reachability_test" >:: fun _ ->
    let open Test_graph in
    let test =
      Test_graph.empty
      |> insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> insert_edge
        {source = "b"; target = "c"; label = First(Pop(1))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = Second(Pop(2))}
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
        {source = "u"; target = "x"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "x"; target = "w"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "w"; target = "y"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "y"; target = "v"; label = Second(Pop(2))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "u" "v" final_summary in
    assert_equal reachable true
;;

let crossing_triple_reachability_test =
  "crossing_triple_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Third(Push(3))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "e"; target = "f"; label = Third(Pop(3))}
      |> Test_graph.insert_edge
        {source = "f"; target = "g"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "g" final_summary in
    assert_bool "↓A↓B↓C　↑B↑C↑A FAIL" reachable
;;

let only_stack_a_good_simple_test =
  "only_stack_a_good_simple_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(100))}
      (* |> Test_graph.insert_edge
         {source = "b"; target = "c"; label = Pop(StackC(2))} *)
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Pop(100))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert_bool "↓A↓B↑A FAIL" reachable
;;

let only_stack_a_good_simple_test_outer =
  "only_stack_a_good_simple_test_outer" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Push(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Pop(100))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert_bool "↓B↓A↑A FAIL" (reachable)
;;

let only_stack_a_good_simple_test_2 =
  "only_stack_a_good_simple_test_2" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "b"; label = First(Push(100))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Third(Pop(100))}
      |> Test_graph.insert_edge
        {source = "d"; target = "end"; label = First(Pop(100))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert_bool "↓A↓B↑C↑A FAIL" reachable
;;

let only_stack_a_good_simple_test_3 =
  "only_stack_a_good_simple_test_3" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "b"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Third(Pop(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Push(100))}
      |> Test_graph.insert_edge
        {source = "d"; target = "end"; label = First(Pop(100))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert_bool "↓B↑C↓A↑A FAIL" reachable
;;

let only_stack_b_good_simple_test_2 =
  "only_stack_b_good_simple_test_2" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "b"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Push(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Third(Pop(100))}
      |> Test_graph.insert_edge
        {source = "d"; target = "end"; label = Second(Pop(100))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert_bool "↓B↓A↑C↑B SUCCESS" (not reachable)
;;

let embedded_double_reachability_test =
  "embedded_double_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "e" final_summary in
    assert_equal reachable true
;;

let separate_two_stack_triple_reachability_test =
  "separate_two_stack_triple_reachability_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "e"; target = "f"; label = First(Push(3))}
      |> Test_graph.insert_edge
        {source = "f"; target = "g"; label = First(Pop(3))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Push(2))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = First(Push(3))}
      |> Test_graph.insert_edge
        {source = "e"; target = "f"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "f"; target = "g"; label = First(Pop(3))}
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
        {source = "a"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "a"; label = First(Pop(1))}
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
        {source = "a"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "b" final_summary in
    assert reachable
;;

let two_node_loop_snd =
  "two_node_loop_snd" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "b"; label = First(Pop(1))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Second(Push(10))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "c" final_summary in
    assert reachable
;;

let triangle_reachable2 =
  "triangle_reachable2" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "c" final_summary in
    assert (reachable)
;;

(* This test is testing whether sth that is supposed to be UNREACHABLE actually is. *)
let triangle_unreachable =
  "triangle_unreachable" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = Third(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = Second(Pop(2))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Third(Pop(1))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "d"; label = First(Pop(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Second(Push(100))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = Second(Pop(2))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "d"; label = Second(Pop(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Second(Push(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Pop(1))}
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
        {source = "a"; target = "b"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "e"; label = Second(Pop(1))}
      |> Test_graph.insert_edge
        {source = "e"; target = "d"; label = Second(Pop(100))}
      |> Test_graph.insert_edge
        {source = "a"; target = "c"; label = Second(Push(1))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "a" "d" final_summary in
    assert (reachable)
;;

let simple_peek_eq_test =
  "simple_peek_eq_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekEq(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert reachable
;;

let simple_peek_eq_test_fail =
  "simple_peek_eq_test_fail" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekEq(10))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (not reachable)
;;

let simple_peek_eq_pop_test =
  "simple_peek_eq_pop_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(PeekEq(1))}
      |> Test_graph.insert_edge
        {source = "b"; target = "end"; label = First(Pop(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert reachable
;;

let simple_peek_neq_test =
  "simple_peek_neq_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekNeq(2))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert reachable
;;

let simple_peek_neq_test_fail =
  "simple_peek_neq_test_fail" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(1))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekNeq(1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (not reachable)
;;

let simple_peek_pred_test =
  "simple_peek_pred_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(-100))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekPred([Negative]))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (reachable)
;;

let simple_peek_pred_test_fail =
  "simple_peek_pred_test_fail" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(100))}
      |> Test_graph.insert_edge
        {source = "a"; target = "end"; label = First(PeekPred([Negative]))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (not reachable)
;;

let simple_search_replace_test =
  "simple_search_replace_test" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "b"; label = First(Push(2000))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Push(1000))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Push(-1))}
      |> Test_graph.insert_edge
        {source = "d"; target = "end"; label = First(SearchAndReplace(Negative, Search, Replace))}
      |> Test_graph.insert_edge
        {source = "e"; target = "end"; label = First(Pop(-1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (reachable)
;;

let simple_search_replace_test_2 =
  "simple_search_replace_test_2" >:: fun _ ->
    let test =
      Test_graph.empty
      |> Test_graph.insert_edge
        {source = "start"; target = "a"; label = First(Push(2000))}
      |> Test_graph.insert_edge
        {source = "a"; target = "b"; label = First(Push(3))}
      |> Test_graph.insert_edge
        {source = "b"; target = "c"; label = First(Push(1000))}
      |> Test_graph.insert_edge
        {source = "c"; target = "d"; label = First(Push(-1))}
      |> Test_graph.insert_edge
        {source = "d"; target = "e"; label = First(SearchAndReplace(Negative, Search, Replace))}
      |> Test_graph.insert_edge
        {source = "e"; target = "f"; label = First(Pop(3))}
      |> Test_graph.insert_edge
        {source = "f"; target = "end"; label = First(Pop(-1))}
    in
    let initial_summary = Test_reachability.create_initial_summary test in
    let final_summary = Test_reachability.step_to_closure initial_summary in
    let reachable = Test_reachability.reachable "start" "end" final_summary in
    assert (reachable)
;;

let tests = "Test_reachability" >:::
            [
              single_reachability_test
            ; simple_double_reachability_test
            ; embedded_double_reachability_test
            ; crossing_double_reachability_test
            ; crossing_triple_reachability_test
            ; separate_two_stack_triple_reachability_test
            ; two_crossing_reachability_test
            ; only_stack_a_good_simple_test
            ; only_stack_a_good_simple_test_outer
            ; only_stack_a_good_simple_test_2
            ; only_stack_a_good_simple_test_3
            ; only_stack_b_good_simple_test_2
            ; loop_base_case
            ; two_node_loop_fst
            ; two_node_loop_snd
            ; triangle_reachable
            ; triangle_unreachable
            ; square_reachable
            ; square_unreachable
            ; non_square_unreachable
            ; simple_peek_eq_test
            ; simple_peek_eq_test_fail
            ; simple_peek_eq_pop_test
            ; simple_peek_neq_test
            ; simple_peek_neq_test_fail
            ; simple_peek_pred_test
            ; simple_peek_pred_test_fail
; simple_search_replace_test
            ]
;;
