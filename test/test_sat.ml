open! Base
open Expect_test_helpers_base
open Hardcaml_verify
open Comb_gates

let%expect_test "single bit" =
  (* this tests a special case in the tseitin transformation *)
  let sat = Solver.solve (cnf (input "a" 1)) in
  print_s [%message (sat : Cnf.Model_with_vectors.input Solver.result)];
  [%expect
    {|
    (sat (
      Ok (
        Sat ((
          (name  a)
          (value 1))))))
    |}];
  let sat = Solver.solve (cnf ~:(input "a" 1)) in
  print_s [%message (sat : Cnf.Model_with_vectors.input Solver.result)];
  [%expect
    {|
    (sat (
      Ok (
        Sat ((
          (name  a)
          (value 0))))))
    |}]
;;

let%expect_test "2*a cannot be odd" =
  let a = input "a" 2 in
  let f = a +: a in
  let cnf = cnf f.:[0, 0] in
  let sat = Solver.solve cnf in
  print_s [%message (sat : Cnf.Model_with_vectors.input Solver.result)];
  [%expect {| (sat (Ok Unsat)) |}]
;;
