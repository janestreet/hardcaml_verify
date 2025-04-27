open Base
open Hardcaml

type property =
  | LTL of Property.LTL.path
  | CTL of Property.CTL.state
[@@deriving sexp_of]

type t [@@deriving sexp_of]

(** [create ?outputs ~name properties] creates a NuSMV model with the provided name.

    [properties] is a list of LTL and/or CTL formula that should be satified by the
    circuit. During construction all [atomic_propositions] (which are the signals in the
    design used to build the temporal formula) are created as outputs. They are given the
    prefix ["__ap_"] which should not otherwise be used to name signals.

    The important part of the circuit is traced back from the [atomic_propositions].
    However, it is possible to include the complete circuit if required by passing
    [outputs]. *)
val create : ?outputs:Signal.t list -> name:string -> property list -> t

(** Return the circuit generated for the NuSMV model. *)
val circuit : t -> Circuit.t

(** Generate the NuSMV model. *)
val to_rope : t -> Rope.t

module Counter_example_trace : sig
  type t [@@deriving sexp_of]

  val to_trace : t -> (string * Bits.t) list list
end

module Proof_result : sig
  type t =
    | Tautology
    | Exists_counter_example of Counter_example_trace.t
  [@@deriving sexp_of]
end

module Output_parser : sig
  (* Parse a NUSMV 'word constant' to a Bits.t *)
  val parse_word_constant : string -> Bits.t

  (* Parse list of strings representing output of NUSMV *)
  val parse : string list -> Proof_result.t list
end

val run : t -> Proof_result.t list

module Circuit_properties : sig
  type ('i, 'o) t

  val inputs : ('i, 'o) t -> 'i
  val outputs : ('i, 'o) t -> 'o
end

module With_interface (I : Hardcaml.Interface.S) (O : Hardcaml.Interface.S) : sig
  type model := t
  type t
  type ltl := Property.LTL.path
  type ctl := Property.CTL.state

  val create : name:string -> Interface.Create_fn(I)(O).t -> t
  val ltl : t -> (ltl array I.t, ltl array O.t) Circuit_properties.t
  val ctl : t -> (ctl array I.t, ctl array O.t) Circuit_properties.t
  val create_specification : t -> property list -> model
end
