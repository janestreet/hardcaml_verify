open Base
open Stdio

(** Write a DIMACS formatted CNF file suitable for input into SAT solvers. *)
val write_problem : Cnf.t -> Out_channel.t -> unit

(** Parse the result of a SAT solver. Different solves use different formats, so the
    parsing is quie relaxed and works with minisat, picosat and z3. *)
val parse_result : string list -> int list Sat.t Or_error.t

(** Read the result of a SAT solver. *)
val read_result : In_channel.t -> int list Sat.t Or_error.t
