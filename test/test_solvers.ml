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

let cnf_unsat =
  Cnf.(
    Conjunction.of_list [ Disjunction.of_list [ b ]; Disjunction.of_list [ ~:b ] ]
    |> create)
;;

let%expect_test "z3" =
  let result = Solver.(solve ~solver:(z3 ~parallel:false ()) cnf) in
  print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name a) (value 00))
          ((name b) (value 0))))))
    |}];
  (* let result = Solver.(solve ~solver:(z3 ~parallel:true) cnf) in
   * print_s [%message (result : Solver.result)];
   * [%expect
   *   {|
   *   (result (
   *     Ok (
   *       Sat (
   *         ((name a) (value --))
   *         ((name b) (value -)))))) |}]; *)
  let result = Solver.(solve ~solver:(z3 ~parallel:false ()) cnf_unsat) in
  print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
  [%expect {| (result (Ok Unsat)) |}]
;;

(* let%expect_test "minisat" =
 *   let result = Solver.(solve ~solver:minisat cnf) in
 *   print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
 *   [%expect
 *     {|
 *     (result (
 *       Ok (
 *         Sat (
 *           ((name a) (value 01))
 *           ((name b) (value 0)))))) |}];
 *   let result = Solver.(solve ~solver:minisat cnf_unsat) in
 *   print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
 *   [%expect {| (result (Ok Unsat)) |}]
 * ;;
 *
 * let%expect_test "picosat" =
 *   let result = Solver.(solve ~solver:picosat cnf) in
 *   print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
 *   [%expect
 *     {|
 *     (result (
 *       Ok (
 *         Sat (
 *           ((name a) (value 01))
 *           ((name b) (value 1)))))) |}];
 *   let result = Solver.(solve ~solver:picosat cnf_unsat) in
 *   print_s [%message (result : Cnf.Model_with_vectors.input Solver.result)];
 *   [%expect {| (result (Ok Unsat)) |}]
 * ;; *)
