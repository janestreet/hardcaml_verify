(* Solve sudoku puzzles directly in CNF form.

   For something humans might understand, see [Test_sudoku_circuit]. This is (probably
   much) more efficient in terms of SAT problem size though. *)

open Base
open Stdio
open Hardcaml_verify
open List.Let_syntax

let labels = Label.create ~width:1000 "v"
let literals = Cnf.Literal.of_labels labels
let p r c v = literals.((r * 100) + (c * 10) + v)
let n r c v = Cnf.( ~: ) (p r c v)
let rec r l h = if l > h then [] else l :: r (l + 1) h
let to_conjunction l = List.map l ~f:Cnf.Disjunction.of_list |> Cnf.Conjunction.of_list

(* [one_in_each] validates that every row and column has a digit asserted. *)
let one_in_each =
  to_conjunction
    (let%bind x = r 1 9 in
     let%bind y = r 1 9 in
     return (List.map (r 1 9) ~f:(fun z -> p x y z)))
;;

(* The [once_in_row] and [once_in_col] adds constraints that diallows a digit to show up
   multiple times within a single row or column respectively. This is achieved by De
   Morgan's principle

   Eg: (n x y z) OR (n i y z) means

   NOT ((p x y z) AND (p i y z))

   which semantically means

   NOT (grid[x][y] == z && grid[i][y] == z)
*)

let once_in_col =
  to_conjunction
    (let%bind y = r 1 9 in
     let%bind z = r 1 9 in
     let%bind x = r 1 8 in
     let%bind i = r (x + 1) 9 in
     return [ n x y z; n i y z ])
;;

let once_in_row =
  to_conjunction
    (let%bind x = r 1 9 in
     let%bind z = r 1 9 in
     let%bind y = r 1 8 in
     let%bind i = r (y + 1) 9 in
     return [ n x y z; n x i z ])
;;

(* [once_in_block] verifies every one of the nine 3x3 blocks contains every single digit.
*)
let once_in_block =
  let row_of_pos pos = 1 + (pos / 3) in
  let col_of_pos pos = 1 + (pos % 3) in
  to_conjunction
    (let%bind z = r 1 9 in
     let%bind i = r 0 2 in
     let%bind j = r 0 2 in
     let%bind pos_1 = r 0 8 in
     let%bind pos_2 = r (pos_1 + 1) 8 in
     let p1 = n ((3 * i) + row_of_pos pos_1) ((3 * j) + col_of_pos pos_1) z in
     let p2 = n ((3 * i) + row_of_pos pos_2) ((3 * j) + col_of_pos pos_2) z in
     return [ p1; p2 ])
;;

(* These constraints validate that each row / block / col contains no more than 1 of each
   number. Since a sudoku row / block / col can only contain 9 numbers, this automatically
   implies that the row / block / col will contain a unique set of digits.

   [one_in_each] prevents the solver from coming up with a trivial solution.
*)
let rules = [ one_in_each; once_in_row; once_in_col; once_in_block ]

let read f =
  let rec next () =
    match f () with
    | '1' .. '9' as c -> Char.to_int c - Char.to_int '0'
    | '_' | '0' | '.' -> 0
    | _ -> next ()
  in
  r 1 9
  >>= (fun x -> r 1 9 >>= fun y -> List.return (x, y))
  |> List.map ~f:(fun (x, y) -> x, y, next ())
  |> List.filter ~f:(fun (_, _, v) -> v <> 0)
  |> List.map ~f:(fun (x, y, v) -> [ p x y v ])
  |> to_conjunction
;;

let from_string s =
  let n = ref 0 in
  let from_string () =
    let x = s.[!n] in
    Int.incr n;
    x
  in
  from_string
;;

let print solution =
  List.iteri solution ~f:(fun i s ->
    if i <> 0 && i % 3 = 0 then printf "\n";
    List.iteri s ~f:(fun i x ->
      if i <> 0 && i % 3 = 0 then printf " ";
      printf "%i" x);
    printf "\n")
;;

let solve puzzle =
  let cnf = Cnf.Conjunction.concat (puzzle :: rules) |> Cnf.create in
  match Solver.solve_with_model (module Cnf.Model_with_bits) cnf with
  | Error _ | Ok Sat.Unsat -> raise_s [%message "failed to solve puzzle :("]
  | Ok (Sat soln) ->
    let soln =
      soln
      |> List.map ~f:(fun (l : Cnf.Model_with_bits.input) ->
        match l.value with
        | '1' -> Label.bit_pos l.label
        | _ -> -Label.bit_pos l.label)
      |> List.filter ~f:(( < ) 0)
      |> List.map ~f:(fun i -> (i / 100, i % 100 / 10), i % 10)
    in
    let soln =
      r 1 9
      >>= fun x ->
      return
        (r 1 9
         >>= fun y ->
         return (List.Assoc.find_exn soln (x, y) ~equal:[%compare.equal: int * int]))
    in
    print soln
;;

let sudoku puzzle = solve (read (from_string puzzle))

let%expect_test "sudoku 1" =
  sudoku
    {|
    ___ 75_ ___
    ___ ___ _94
    561 ___ __3

    _78 _1_ __2
    ___ _6_ ___
    6__ _4_ 98_

    3__ ___ 726
    95_ ___ ___
    ___ _36 ___
           |};
  [%expect
    {|
    849 753 261
    732 681 594
    561 924 873

    478 519 632
    295 368 147
    613 247 985

    384 195 726
    956 472 318
    127 836 459
    |}]
;;

let%expect_test "sudoku 2" =
  sudoku
    {|
    +-------+-------+-------+
    | 2 1 8 | . 5 . | 4 9 7 |
    | . 6 9 | 1 7 2 | 3 8 . |
    | 5 . . | . . . | . . 2 |
    +-------+-------+-------+
    | 1 8 . | 5 . 3 | . 2 9 |
    | . 2 . | . 9 . | . 5 . |
    | . 9 5 | . 6 . | 8 3 . |
    +-------+-------+-------+
    | . . . | . 2 . | . . . |
    | 9 . . | . . . | . . 3 |
    | 8 5 . | 9 3 4 | . 1 6 |
    +-------+-------+-------+
    |};
  [%expect
    {|
    218 356 497
    469 172 385
    573 489 162

    186 543 729
    324 897 651
    795 261 834

    631 725 948
    942 618 573
    857 934 216
    |}]
;;

let%expect_test "sudoku 3" =
  sudoku
    {|
    +-------+-------+-------+
    | 3 . 7 | . 5 . | 6 . 1 |
    | 1 2 . | 3 . 4 | . 7 9 |
    | . 6 . | . 7 . | . 3 . |
    +-------+-------+-------+
    | . . . | 4 . 6 | . . . |
    | . . 3 | . 9 . | 7 . . |
    | . . . | . . . | . . . |
    +-------+-------+-------+
    | 7 1 . | . . . | . 6 8 |
    | 9 . . | 6 . 2 | . . 7 |
    | 8 . 6 | . 1 . | 9 . 2 |
    +-------+-------+-------+
    |};
  [%expect
    {|
    347 259 681
    128 364 579
    569 178 234

    271 436 895
    483 591 726
    695 827 413

    712 945 368
    934 682 157
    856 713 942
    |}]
;;

let%expect_test "sudoku 4" =
  sudoku
    {|
000040709000100600500008004402000000103406502000000106800600003007002000904030000
|};
  [%expect
    {|
    216 345 789
    348 197 625
    579 268 314

    462 519 837
    183 476 592
    795 823 146

    821 654 973
    637 982 451
    954 731 268
    |}]
;;
