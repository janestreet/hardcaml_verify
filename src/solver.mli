open Base

type run_solver = dimacs_in:string -> result_out:string -> unit -> unit Or_error.t

(** Minisat solver *)
val minisat : run_solver

(** Picosat solver *)
val picosat : run_solver

(** Z3 solver in DIMACs mode. [parallel:true] enableds parallel solving, however, as of
    V4.8.5 Z3 does not return a proper model. *)
val z3 : ?seed:int -> parallel:bool -> unit -> run_solver

type 'a result = 'a list Sat.t Or_error.t [@@deriving sexp_of]

(** Create intermediate files, run the given solver and return a model if satisfiable. *)
val solve_with_model
  :  ?solver:run_solver
  -> ?print_model:bool
  -> (module Cnf.Model with type input = 'input)
  -> Cnf.t
  -> 'input result

val solve
  :  ?solver:run_solver
  -> ?print_model:bool
  -> Cnf.t
  -> Cnf.Model_with_vectors.input result
