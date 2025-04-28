(** Sequential equivalence checking.

    This module will take 2 circuits, and perform a SAT check on the combinational logic.
    Stateful logic must be the same between the 2 circuits - this is not a true
    equivalence check, but much simpler to implement.

    It will return [Unsat] if the two circuits are equivalent, or [Sat] otherwise.

    It may be useful when optimising the combinational logic of a circuit, or when porting
    code to hardcaml with [Hardcaml_of_verilog]. *)

open! Base
open! Hardcaml

(** Control comparison of instantiation inputs and outputs.

    They should either be equal or the left should be a subset of the right.

    This is allowed to help comparing with verilog designs. In verilog an input or output
    may be specified without a signal, and when converting with [Hardcaml_of_verilog] they
    will not exist in the instantiated sub-circuit. Care should be taken to ensure the
    undriven ports do not effect the operation of the design ie. try to avoid it, but it
    is unfortunately somewhat inevitable with some external verilog code. *)
module Instantiation_ports_match : sig
  type t =
    | Exactly
    | Left_is_subset_of_right
  [@@deriving sexp_of]
end

type t [@@deriving sexp_of]

(** A proposition derived from the circuits being compared. *)
module Proposition : sig
  type t [@@deriving sexp_of]
end

(** Result of a proposition check. *)
module Equivalence_result : sig
  type t = Cnf.Model_with_vectors.input list Sat.t [@@deriving sexp_of]
end

(** Construct the logic for comparing two circuits via their outputs, registers and
    instantiations.

    [instantiation_ports_match] allows the left (first passed) circuit to contain
    instantiations which have a subset of the ports on instantiations in the right (second
    passed) circuit. This comes up when comparing with a circuit that was converted from
    verilog and has floating ports. *)
val create
  :  ?instantiation_ports_match:Instantiation_ports_match.t
  -> Hardcaml.Circuit.t
  -> Hardcaml.Circuit.t
  -> t Or_error.t

(** All circuit outputs match *)
val circuit_outputs_proposition : t -> Proposition.t

(** Get the proposition for a single circuit output *)
val find_circuit_output_port_proposition : t -> port_name:string -> Proposition.t option

(** Get the proposition for a the inputs to a register. *)
val find_register_inputs_proposition : t -> name:string -> Proposition.t option

(** Get the proposition for a single input port of an instantiation *)
val find_instantiation_input_port_proposition
  :  t
  -> instantiation_name:string
  -> port_name:string
  -> Proposition.t option

(** Get the proposition for all inputs to an instantiation. *)
val find_instantiation_inputs_proposition : t -> name:string -> Proposition.t option

(** Check equivalence of the given proposition. *)
val equivalent : Proposition.t list -> Equivalence_result.t Or_error.t

(** Check circuit equivlance (all propositions included). *)
val circuits_equivalent : t -> Equivalence_result.t Or_error.t
