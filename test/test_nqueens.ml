open Base
open Stdio
open Hardcaml_verify

let nqueens size =
  (* generate rows/cols/diagonals *)
  let labels = Label.create ~width:(size * size) "v" in
  let literals = Cnf.Literal.of_labels labels in
  let idx (r, c) = literals.((r * size) + c) in
  let init n f = List.init n ~f in
  let row r = init size (fun c -> idx (r, c)) in
  let col c = init size (fun r -> idx (r, c)) in
  let rec diag1 (r, c) =
    if r >= size || c >= size then [] else idx (r, c) :: diag1 (r + 1, c + 1)
  in
  let rec diag2 (r, c) =
    if r >= size || c < 0 then [] else idx (r, c) :: diag2 (r + 1, c - 1)
  in
  (* generate contraints *)
  let at_most_one x =
    let rec pairs = function
      | [] -> []
      | [ _ ] -> []
      | h :: t ->
        let r = List.map t ~f:(fun t -> [ Cnf.( ~: ) h; Cnf.( ~: ) t ]) in
        r :: pairs t
    in
    List.concat (pairs x)
  in
  let only_one x = x :: at_most_one x in
  (* solve *)
  let cnf =
    List.init size ~f:(fun i ->
      [ only_one (row i)
      ; only_one (col i)
      ; at_most_one (diag1 (i, 0))
      ; at_most_one (diag1 (0, i))
      ; at_most_one (diag2 (i, size - 1))
      ; at_most_one (diag2 (0, i))
      ]
      |> List.concat
      |> List.map ~f:Cnf.Disjunction.of_list)
    |> List.concat
    |> Cnf.Conjunction.of_list
    |> Cnf.create
  in
  match Solver.solve_with_model (module Cnf.Model_with_bits) cnf with
  | Error _ | Ok Unsat -> printf "no solution\n"
  | Ok (Sat soln) ->
    for r = 0 to size - 1 do
      for c = 0 to size - 1 do
        let soln =
          List.map soln ~f:(fun s ->
            let pos = Label.bit_pos s.label in
            ( pos
            , match s.value with
              | '1' -> 'Q'
              | _ -> '.' ))
        in
        printf "%c" (List.Assoc.find_exn soln ((r * size) + c) ~equal:Int.equal)
      done;
      printf "\n"
    done
;;

let%expect_test "nqueens 5" =
  nqueens 5;
  [%expect
    {|
    ...Q.
    .Q...
    ....Q
    ..Q..
    Q....
    |}]
;;

let%expect_test "nqueens 10" =
  nqueens 10;
  [%expect
    {|
    .....Q....
    .......Q..
    ....Q.....
    .Q........
    ...Q......
    .........Q
    ......Q...
    ........Q.
    ..Q.......
    Q.........
    |}]
;;
