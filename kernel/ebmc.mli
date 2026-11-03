open Base

module Ebmc_result : sig
  type t =
    | Assumed
    | Proved
    | Proved_with_trace of Counter_example_trace.t
    | Refuted
    | Refuted_with_trace of Counter_example_trace.t
    (* When EBMC outputs "FAILURE" (or, a result that isn't "PROVED" or "REFUTED") the raw
       parsed data is dumped. *)
    | Failure of Sexp.t
  [@@deriving sexp_of]
end

val solve
  :  ?reset:[ `High of string | `Low of string ]
       (* Specifying [tmpdir] will write the emitted verilog and EBMC output at the given
          directory, along with a shell script to invoke EBMC. These files will not be
          automatically deleted. *)
  -> ?tmpdir:string
  -> ?rtl_output_mode:[ `Full_hierarchy | `Top_level_and_blackboxes ]
       (** How to emit RTL for EBMC. Defaults to [`Full_hierarchy]. *)
  -> ?verilog_preamble:string
       (** Verilog text to emit before the Hardcaml-generated RTL. *)
  -> ?trace:bool
       (** Whether to request traces in EBMC's JSON output. Defaults to [true]. This is
           ignored in public releases. *)
  -> circuit_database:Hardcaml.Circuit_database.t option
       (** [circuit_database] needs to be provided for circuits that perform
           instantiations. If the circuit instantiates submodules, but [circuit_database]
           is [None], this function will raise. *)
  -> bound:int
  -> Hardcaml.Circuit.t
  -> Ebmc_result.t Map.M(String).t
