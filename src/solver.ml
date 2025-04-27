open Base
open Stdio
module Config = Hardcaml.Tools_config

type run_solver = dimacs_in:string -> result_out:string -> unit -> unit Or_error.t

let run ?(exit_codes = [ 0 ]) command =
  match Unix.system command with
  | WEXITED e when List.mem exit_codes e ~equal:Int.equal -> Ok ()
  | WEXITED exit_code ->
    Or_error.error_s [%message "SAT solver returned non-zero exit code" (exit_code : int)]
  | WSIGNALED _ | WSTOPPED _ ->
    Or_error.error_s [%message "SAT solver was signaled or stopped"]
;;

let swallow_stderr = "2>/dev/null"

let minisat ~dimacs_in ~result_out () =
  run
    ~exit_codes:[ 10; 20 ]
    (String.concat
       ~sep:" "
       [ Config.minisat; "-verb=0"; dimacs_in; result_out; ">/dev/null"; swallow_stderr ])
;;

let picosat ~dimacs_in ~result_out () =
  run
    ~exit_codes:[ 10; 20 ]
    (String.concat
       ~sep:" "
       [ Config.picosat; dimacs_in; ">" ^ result_out; swallow_stderr ])
;;

let z3 ?seed ~parallel () ~dimacs_in ~result_out () =
  (* Use the given seed if specified. Otherwise set to 0 which means the solver chooses -
     unless in tests when we force it to a specific value for repeatability. *)
  let seed =
    match seed with
    | Some seed -> seed
    | None -> if Exported_for_specific_uses.am_testing then 192452 else 0
  in
  run
    (String.concat
       ~sep:" "
       [ Config.z3
       ; "-dimacs"
       ; (if parallel then "parallel.enable=true" else "")
       ; "sat.random_seed=" ^ Int.to_string seed
       ; dimacs_in
       ; ">" ^ result_out
       ; swallow_stderr
       ])
;;

module Filename = Stdlib.Filename

type 'a result = 'a list Sat.t Or_error.t [@@deriving sexp_of]

let solve_with_model
  (type a)
  ?(solver = z3 ~parallel:false ())
  ?(print_model = false)
  (module Model : Cnf.Model with type input = a)
  cnf
  : a list Sat.t Or_error.t
  =
  let dimacs_file = Filename.temp_file "cnf" "dimacs" in
  let result_file = Filename.temp_file "cnf" "result" in
  let dimacs_out = Out_channel.create dimacs_file in
  Dimacs.write_problem cnf dimacs_out;
  Out_channel.close dimacs_out;
  let solver_result = solver ~dimacs_in:dimacs_file ~result_out:result_file () in
  match solver_result with
  | Ok () ->
    let file = In_channel.create result_file in
    let dimacs_result = Dimacs.read_result file in
    In_channel.close file;
    Unix.unlink dimacs_file;
    Unix.unlink result_file;
    let model = Or_error.map dimacs_result ~f:(Model.get cnf) in
    if print_model then Model.print Stdio.stdout model;
    model
  | Error e ->
    Unix.unlink dimacs_file;
    Error e
;;

let solve ?solver ?print_model cnf =
  solve_with_model ?solver ?print_model (module Cnf.Model_with_vectors) cnf
;;
