(* open Batteries;;
open Jhupllib;; *)
open OUnit2;;

Random.init 15;;

let all_tests =
  [
    Lcl_reachability_tests.Generate_tests.tests;
    Test_reachability.tests;
    (* Test_reachability_primes.tests *)
  ];;

let () =
  run_test_tt_main ("Tests" >::: all_tests)
;;
