(** Type to represent a counter example trace. *)

open Hardcaml

type t [@@deriving sexp_of]

val of_states : (string * Bits.t) list list -> t
val to_states : t -> (string * Bits.t) list list
