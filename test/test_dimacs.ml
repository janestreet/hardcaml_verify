open Base
open Expect_test_helpers_base
open Hardcaml_verify

let a = Cnf.Literal.create "a" ~width:2
let b = Cnf.Literal.create1 "b"

let cnf =
  Cnf.(
    Conjunction.of_list
      [ Disjunction.of_list [ a.(0); a.(1); ~:b ]; Disjunction.of_list [ ~:(a.(1)); b ] ]
    |> create)
;;

let%expect_test "dimacs" =
  Dimacs.write_problem cnf Stdio.stdout;
  [%expect
    {|
    p cnf 3 2
    1 2 -3 0
    -2 3 0
    |}]
;;

let%expect_test "parse dimacs result" =
  let sexp_of_result result = [%sexp (result : int list Sat.t Or_error.t)] in
  let result = Dimacs.parse_result [] in
  print_s [%message (result : result)];
  [%expect {| (result (Error "No SAT result")) |}];
  let result = Dimacs.parse_result [ "foo" ] in
  print_s [%message (result : result)];
  [%expect {| (result (Error "Dont know how to parse SAT result")) |}];
  let result = Dimacs.parse_result [ "unsat" ] in
  print_s [%message (result : result)];
  [%expect {| (result (Ok Unsat)) |}];
  let result = Dimacs.parse_result [ "SATISFIABLE" ] in
  print_s [%message (result : result)];
  [%expect {| (result (Ok (Sat ()))) |}];
  let result = Dimacs.parse_result [ "sat"; "1 2 -3 "; " 1  7 4"; "v v"; "v 5 6" ] in
  print_s [%message (result : result)];
  [%expect {| (result (Ok (Sat (1 2 -3 1 7 4 5 6)))) |}];
  let result = Dimacs.parse_result [ "sat"; "x y zzz" ] in
  print_s [%message (result : result)];
  [%expect {| (result (Error "Failed to parse SAT output")) |}]
;;
