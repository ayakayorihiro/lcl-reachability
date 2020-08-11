open Jhupllib.Logger_utils;;

(* open OUnit2;; *)
(* open Lcl_reachability_tests;; *)
open Lcl_reachability.Stack_utils;;
(* open Lcl_reachability.Utils;; *)

(* module Closure = Lcl_reachability.Closure;;
   module Closure2 = Lcl_reachability.Closure_algorithm2;;
   module New_closure = Lcl_reachability.New_closure;;
   module Three_stack_reachability = Lcl_reachability.Three_stack_reachability;;
   module Graph_types = Lcl_reachability.Graph_types;; *)

set_default_logging_level `trace;;

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

(* NOTE: Test_label and Test_graph for three stack testing *)
(* module Test_label =
struct
  type t = (((Test_stack_elm_1.t, Test_stack_predicate_1.t) stack_action),
            ((Test_stack_elm_1.t, Test_stack_predicate_1.t) stack_action),
            ((Test_stack_elm_1.t, Test_stack_predicate_1.t) stack_action)) trinary
  [@@deriving eq, ord, show]
  ;;
end;;

module Test_graph = Graph_types.Make(Test_node)(Test_label);;

module Test_three_stack_reachability =
  Three_stack_reachability.Make
    (Test_stack_elm_1)(Test_stack_predicate_1)
    (Test_stack_elm_1)(Test_stack_predicate_1)
    (Test_stack_elm_1)(Test_stack_predicate_1)
    (Test_graph);; *)


let test_graph =
  Test_graph.empty
  |> Test_graph.insert_edge
    {source = "a"; target = "b"; label = First(Push(2000))}
  |> Test_graph.insert_edge
    {source = "b"; target = "c"; label = First(Push(3))}
  |> Test_graph.insert_edge
    {source = "c"; target = "d"; label = First(Push(1000))}
  |> Test_graph.insert_edge
    {source = "d"; target = "e"; label = First(Push(-1))}
  |> Test_graph.insert_edge
    {source = "e"; target = "f"; label = First(SearchAndReplace(Negative, Search, Replace))}
  |> Test_graph.insert_edge
    {source = "f"; target = "g"; label = First(Pop(3))}
  |> Test_graph.insert_edge
    {source = "g"; target = "h"; label = First(Pop(-1))}
;;

(* NOTE: Uncomment below for two stack testing *)
(* let initial_summary = Test_reachability.create_initial_summary test_graph;;
   let final_summary = Test_reachability.step_to_closure initial_summary;;
   let reachable = Test_reachability.reachable "a" "c" final_summary;;
   print_endline "=====================";;
   print_endline (string_of_bool reachable);; *)

let initial_summary = Test_reachability.create_initial_summary test_graph;;
let final_summary = Test_reachability.step_to_closure initial_summary;;
let reachable = Test_reachability.reachable "a" "h" final_summary;;
print_endline "=====================";;
print_endline (string_of_bool reachable);;

(* let initial_summary = Test_three_stack_reachability.create_initial_summary test_graph;;
   let final_summary = Test_three_stack_reachability.step_to_closure initial_summary;;
   let reachable = Test_three_stack_reachability.reachable "start" "end" final_summary;;
   print_endline "=====================";;
   print_endline (string_of_bool reachable);; *)

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
