(* Solving Sudoku with a Hardcaml circuit.

   In this example we will build a circuit which implements the rules of sudoku and takes
   as input a proposed solution and returns a single bit which indicates if the solution
   is valid or not.

   We will then show how we can use this circuit with a SAT solver to actually solve
   sudoku puzzles.
*)

open Base
open Expect_test_helpers_base
open Hardcaml
open! Hardcaml_verify

(* The first thing we need to do is choose how we are going to represent the puzzle.

   We choose to represent the 9x9 grid as a single dimensional array. It will be indexed
   as follows

   [index = row*9 + col]

   How to represent the cells themselves? In sudoku we normally label them with the
   integers in the range 1-9. We could use a 4 bit number to represent the 9 possible
   values (plus another 7 redundant ones), however, it will be simpler to choose a more
   hardware friendly representation - onehot vectors.

   A onehot vector has one and only one bit set. The position of the bit is used to
   represent the number. Noting we generally write hardware vectors msb first, here are
   the values we will use to represent 1-9.

   {v
      1 000000001
      2 000000010
      3 000000100
      4 000001000
      5 000010000
      6 000100000
      7 001000000
      8 010000000
      9 100000000
   v}
*)
module I = struct
  type 'a t = { cells : 'a array [@bits 9] [@length 9 * 9] }
  [@@deriving hardcaml ~rtlmangle:false]
end

(* The output is simply a single bit which is [1] when the input solution is valid, and
   [0] otherwise. *)
module O = struct
  type 'a t = { is_valid_solution : 'a } [@@deriving hardcaml]
end

module Make (Comb : Comb.S) = struct
  open Comb
  module Is_one_hot = Is_one_hot.Make (Comb)

  (* The functions [row], [col] and [block] each return an array of the corresponding 9
     cells *)
  let row cells row = Array.init 9 ~f:(fun col -> cells.((row * 9) + col))
  let col cells col = Array.init 9 ~f:(fun row -> cells.((row * 9) + col))

  let block cells r c =
    List.init 3 ~f:(fun row ->
      let row = row + (r * 3) in
      Array.init 3 ~f:(fun col ->
        let col = col + (c * 3) in
        cells.((row * 9) + col)))
    |> Array.concat
  ;;

  (* [row_is_valid], [col_is_valid] and [block_is_valid] will create combinational logic
     that tests that the 9 given values contain each of the values 1-9.

     Given the onehot representation, this is done by simply or'ing together all the
     values and making sure the result is:

     [111111111]

     Given 9 input values, each with one bit set, the only way to produce this value is if
     they are all different. Therefore, they must cover the full required range of values.
  *)
  let row_is_valid cells r =
    Array.fold (row cells r) ~init:(zero 9) ~f:(fun acc c -> acc |: c) ==: ones 9
  ;;

  let col_is_valid cells r =
    Array.fold (col cells r) ~init:(zero 9) ~f:(fun acc c -> acc |: c) ==: ones 9
  ;;

  let block_is_valid cells r c =
    Array.fold (block cells r c) ~init:(zero 9) ~f:(fun acc c -> acc |: c) ==: ones 9
  ;;

  (* This create our puzzle checking circuit.

     1. Check all nine rows are valid
     2. Check all nine cols are valid
     3. Check all nine blocks are valid

     And just and together all the intermediate results. Easy!
  *)

  let create (i : _ I.t) =
    let rows_are_valid = List.init 9 ~f:(row_is_valid i.cells) |> reduce ~f:( &: ) in
    let cols_are_valid = List.init 9 ~f:(col_is_valid i.cells) |> reduce ~f:( &: ) in
    let blocks_are_valid =
      List.init 3 ~f:(fun r -> List.init 3 ~f:(block_is_valid i.cells r))
      |> List.concat
      |> reduce ~f:( &: )
    in
    let is_valid_solution = rows_are_valid &: cols_are_valid &: blocks_are_valid in
    { O.is_valid_solution }
  ;;

  (* Read a puzzle from a string. The string is [9*9] characters long and should only
     contain the numbers [1-9] and a [.].

     For numbers, it returns [`const onehot_vector]. For the [.] it returns
     [`input index].
  *)
  let read_puzzle puzzle =
    puzzle
    |> String.to_list
    |> List.mapi ~f:(fun idx c ->
      if Char.equal c '.'
      then `input idx
      else (
        let v = Char.to_int c - Char.to_int '1' in
        `const (of_int_trunc ~width:9 (1 lsl v))))
    |> Array.of_list
  ;;

  (* This functions reads the output of a SAT solver and the original puzzle and fills in
     the [.]s with the outputs of the solver. We will see shortly how this works. *)
  let get_solution puzzle (sat_solution : Cnf.Model_with_vectors.input Solver.result) =
    match sat_solution with
    | Error _ | Ok Unsat -> "oh no! failed to solve the puzzle :("
    | Ok (Sat sat_solution) ->
      let sat_solution =
        List.map sat_solution ~f:(fun { name; value } ->
          name, Bits.of_string value |> Bits.to_int_trunc |> Int.ceil_log2)
      in
      String.to_list puzzle
      |> List.mapi ~f:(fun i c ->
        match c with
        | '.' ->
          Char.of_int_exn
            (Char.to_int '1'
             + List.Assoc.find_exn
                 sat_solution
                 ("v" ^ Int.to_string i)
                 ~equal:String.equal)
        | c -> c)
      |> String.of_char_list
  ;;
end

(* Here we have 3 puzzles. The first is a good solution to a sudoku puzzle. For the second
   we aritrarily change the very first number from [2] to [1] to make it a bad solution.

   The third one erases a number of entries. The numbers left are still correct, but the
   solution is incomplete. *)

let good_puzzle =
  "216345789348197625579268314462519837183476592795823146821654973637982451954731268"
;;

let bad_puzzle =
  "116345789348197625579268314462519837183476592795823146821654973637982451954731268"
;;

let partial_puzzle =
  ".16.457.9..81976255..268.1446.5198.718...65927.5823.468.16...736.7..2451..4.3.2.8"
;;

(* The first thing we will do is just use the circuit to test the fully specified puzzles.

   Note by fully specified I mean that all the inputs have a known value. We can't
   evaluate the circuit unless we know all these values.
*)

let check puzzle =
  let module Sudoku_checker = Make (Bits) in
  let solution =
    Sudoku_checker.read_puzzle puzzle
    |> Array.map ~f:(function
      | `const c -> c
      | `input _ -> raise_s [%message "cant evaluate with inputs"])
  in
  let solution = Sudoku_checker.create { I.cells = solution } in
  print_s [%message (solution : Bits.t O.t)]
;;

let%expect_test "good puzzle" =
  check good_puzzle;
  [%expect {| (solution ((is_valid_solution 1))) |}]
;;

let%expect_test "bad puzzle" =
  check bad_puzzle;
  [%expect {| (solution ((is_valid_solution 0))) |}]
;;

(* Now we turn to the incomplete puzzle.

   The main difference is we now create [input] varaibles for the cells whose values we
   dont know. The expression;

   [is_valid_solution |> cnf |> Solver.solve]

   Takes the output valid bit, converts the circuit into Conjunctive Normal Form (which is
   "just" another way of expressing the boolean logic of the circuit) and runs a SAT
   solver to find values for the inputs we created which make the circuit output
   [valid=1].
*)

let solve puzzle =
  let module Sudoku_checker = Make (Comb_gates) in
  let open Comb_gates in
  let cells =
    Sudoku_checker.read_puzzle puzzle
    |> Array.map ~f:(function
      | `const c -> c
      | `input i -> input ("v" ^ Int.to_string i) 9)
  in
  let is_valid_solution = (Sudoku_checker.create { I.cells }).O.is_valid_solution in
  let sat = is_valid_solution |> cnf |> Solver.solve in
  print_s [%message (sat : Cnf.Model_with_vectors.input Solver.result)]
;;

(* Oops. This doesn't look right.

   First, the [-] symbols tell us the solver didn't even have to look at these bits to
   find the solution. Ok, but weird.

   The main problem, however, if these do not look like onehot vectors! A 9 bit onehot
   vector has 512 possible bit patterns, but only 9 of them are actually valid values. But
   we never told the solver about this constraint.
*)

let%expect_test "solve" =
  solve partial_puzzle;
  [%expect
    {|
    (sat (
      Ok (
        Sat (
          ((name v0)  (value 000--001-))
          ((name v10) (value 0-0-0110-))
          ((name v19) (value 1-0-0000-))
          ((name v20) (value 0-1--000-))
          ((name v24) (value 010---1-0))
          ((name v29) (value 0-----10-))
          ((name v3)  (value 010--110-))
          ((name v34) (value 0-0--011))
          ((name v38) (value 1-0--001-))
          ((name v39) (value 0-0--00--))
          ((name v40) (value 01-111--))
          ((name v46) (value 1-0-00001))
          ((name v51) (value 0-----1-0))
          ((name v55) (value 0-0-0000-))
          ((name v58) (value 000-00-00))
          ((name v59) (value 000-00-00))
          ((name v60) (value 1--011011))
          ((name v64) (value 000-0000-))
          ((name v66) (value 000-000-0))
          ((name v67) (value 110-001-0))
          ((name v7)  (value 0-0--00-))
          ((name v72) (value 1-000-100))
          ((name v73) (value 0-1010010))
          ((name v75) (value 1010000-0))
          ((name v77) (value 000011--1))
          ((name v79) (value 01010-1-0))
          ((name v9)  (value 0-0--000-))))))
    |}]
;;

(* This version fixes the problem.

   For each input we create an expression that asserts that inputs are indeed onehot.

   We could also add the onehot check to [Sudoku_checker.create]. If, however, we want to
   check solutions at a high clock rate (for example 500MHz) we want as lttle logic in
   what is already the critical path. It would be better to enforce the onehot property in
   the logic that create inputs (ie shift-registers).

   In terms of performance of the SAT solver, it's slightly better only onehot checking
   the actual inputs (i.e. non-constants) - though I expect something would end up
   simplifying the logic on constants anyway (i.e. the gate construction operations which
   form the problem as CNF, or simpification passes in the solver itself).
*)
let solve_with_input_constraints puzzle =
  let module Sudoku_checker = Make (Comb_gates) in
  let open Comb_gates in
  let solution =
    Sudoku_checker.read_puzzle puzzle
    |> Array.map ~f:(function
      | `const c -> `const c
      | `input i -> `input (input ("v" ^ Int.to_string i) 9))
  in
  let input_constraints =
    Array.filter_map solution ~f:(function
      | `const _ -> None
      | `input i -> Some Sudoku_checker.(Is_one_hot.create i).one_bit_set)
    |> Array.fold ~init:vdd ~f:( &: )
  in
  let cells =
    Array.map solution ~f:(function
      | `const c -> c
      | `input i -> i)
  in
  let is_valid_solution =
    input_constraints &: (Sudoku_checker.create { I.cells }).O.is_valid_solution
  in
  let sat = is_valid_solution |> cnf |> Solver.solve in
  print_s
    [%message
      (sat : Cnf.Model_with_vectors.input Solver.result)
        (Sudoku_checker.get_solution puzzle sat : string)]
;;

(* Now we get decent looking output.

   The values assigned to the inputs are all onehot, and the result we get back is
   actually exactly the same as the [good_puzzle] it was originally derived from.
*)

let%expect_test "solve properly" =
  solve_with_input_constraints partial_puzzle;
  [%expect
    {|
    ((sat (
       Ok (
         Sat (
           ((name v0)  (value 000000010))
           ((name v10) (value 000001000))
           ((name v19) (value 001000000))
           ((name v20) (value 100000000))
           ((name v24) (value 000000100))
           ((name v29) (value 000000010))
           ((name v3)  (value 000000100))
           ((name v34) (value 000000100))
           ((name v38) (value 000000100))
           ((name v39) (value 000001000))
           ((name v40) (value 001000000))
           ((name v46) (value 100000000))
           ((name v51) (value 000000001))
           ((name v55) (value 000000010))
           ((name v58) (value 000010000))
           ((name v59) (value 000001000))
           ((name v60) (value 100000000))
           ((name v64) (value 000000100))
           ((name v66) (value 100000000))
           ((name v67) (value 010000000))
           ((name v7)  (value 010000000))
           ((name v72) (value 100000000))
           ((name v73) (value 000010000))
           ((name v75) (value 001000000))
           ((name v77) (value 000000001))
           ((name v79) (value 000100000))
           ((name v9)  (value 000000100))))))
     ("Sudoku_checker.get_solution puzzle sat"
      216345789348197625579268314462519837183476592795823146821654973637982451954731268))
    |}]
;;
