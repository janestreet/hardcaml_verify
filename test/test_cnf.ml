open Base
open Stdio
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

let%expect_test "empty" =
  let empty = Cnf.(Conjunction.of_list [] |> create) in
  print_s [%message (empty : Cnf.t)];
  [%expect
    {|
    (empty (
      (input_bits  ())
      (input_map   ())
      (int_map     ())
      (conjunction ())
      (number_of_variables 0)
      (number_of_clauses   0)))
    |}]
;;

let%expect_test "empty disjunction" =
  let empty = Cnf.(Conjunction.of_list [ Disjunction.of_list [] ] |> create) in
  print_s [%message (empty : Cnf.t)];
  [%expect
    {|
    (empty (
      (input_bits ())
      (input_map  ())
      (int_map    ())
      (conjunction (()))
      (number_of_variables 0)
      (number_of_clauses   1)))
    |}]
;;

let%expect_test "show data structure" =
  print_s [%message (cnf : Cnf.t)];
  [%expect
    {|
    (cnf (
      (input_bits (
        (a 0 1 false)
        (a 1 1 false)
        (b 0 2 false)))
      (input_map (
        (1 (a 0 1 false))
        (2 (a 1 1 false))
        (3 (b 0 2 false))))
      (int_map (
        ((a 0 1 false) 1)
        ((a 1 1 false) 2)
        ((b 0 2 false) 3)))
      (conjunction (
        ((P (a 0 1 false))
         (P (a 1 1 false))
         (N (b 0 2 false)))
        ((N (a 1 1 false))
         (P (b 0 2 false)))))
      (number_of_variables 3)
      (number_of_clauses   2)))
    |}]
;;

let%expect_test "print problem" =
  printf "vars=%i clauses=%i\n" (Cnf.number_of_variables cnf) (Cnf.number_of_clauses cnf);
  Cnf.iter cnf ~f:(fun disjunction ->
    Cnf.Disjunction.iter disjunction ~f:(fun literal ->
      printf "%s " (Cnf.Literal.to_string literal));
    printf "\n");
  [%expect
    {|
    vars=3 clauses=2
    a/0/1 a/1/1 -b/0/2
    -a/1/1 b/0/2
    |}];
  (* fancy pretty printer *)
  let cnf =
    Cnf.fold cnf ~init:[] ~f:(fun lst disjunction ->
      let terms =
        Cnf.Disjunction.fold ~init:[] disjunction ~f:(fun lst literal ->
          Cnf.Literal.to_string literal :: lst)
        |> List.rev
      in
      String.concat ~sep:"" [ "("; String.concat ~sep:" V " terms; ")" ] :: lst)
    |> List.rev
    |> String.concat ~sep:" . "
  in
  print_s [%message cnf];
  [%expect {| "(a/0/1 V a/1/1 V -b/0/2) . (-a/1/1 V b/0/2)" |}]
;;
