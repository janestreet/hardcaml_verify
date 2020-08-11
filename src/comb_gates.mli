(** Hardcaml combinational logic API using lists of [Basic_gate.t]s. *)

open Base
include Hardcaml.Comb.S with type t = Basic_gates.t list

(** [input "name" width] creates an input with ["name"] and given [width] in bits. *)
val input : string -> int -> t

(** [cofactor ~var p ~f] computes the cofactor of each bit of [f] wrt to each bit of
    [var]. [p] must be a constant and represents the value of [var] which which to perform
    the cofactor. *)
val cofactor : var:t -> t -> f:t -> t

(** universal quantification *)
val forall : t -> f:t -> t

(** existential quantification *)
val exists : t -> f:t -> t

(** Create CNF for each bit of the given vector. In the resulting CNF the bits are
    logically AND'd. *)
val cnf : ?show_hidden:bool -> t -> Cnf.t
