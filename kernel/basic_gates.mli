(* Simple 1 and 2 input boolean logic .

   Basic consant propogation is perform in the constructor functions. *)

open Base
module Uid : Uid.S

type t [@@deriving compare ~localize, sexp]

include%template Comparable.S [@mode local] with type t := t

val optimise_muxs : bool
val constant_only : bool
val to_char : t -> char
val of_char : char -> t
val uid : t -> Uid.t
val vdd : t
val gnd : t
val is_vdd : t -> bool
val is_gnd : t -> bool
val var : Label.t -> t
val ( ~: ) : t -> t
val ( |: ) : t -> t -> t
val ( ^: ) : t -> t -> t
val ( &: ) : t -> t -> t

(** [cofactor ~var p ~f] computes the cofactor of [f] wrt to [var]. [p=vdd] for positive
    cofactor and [p=gnd] for negative cofactor *)
val cofactor : var:t -> t -> f:t -> t

(** boolean difference *)
val difference : t -> f:t -> t

(** universal quantification *)
val forall : t -> f:t -> t

(** existential quantification *)
val exists : t -> f:t -> t

(** [F = xF_x + x'F_x'] *)
val shannon_expansion : t -> f:t -> t

(** Gate inputs *)
val deps : t -> t list

(** Visit all nodes in the list of functions and call [f]. Nodes are visited once only. *)
val depth_first_search : t list -> init:'a -> f:('a -> t -> 'a) -> 'a

(** Create CNF for each given equation. In the resulting CNF the equations are logically
    AND'd. *)
val cnf : ?show_hidden:bool -> t list -> Cnf.t
