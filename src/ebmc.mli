open Hardcaml_formal_verification_kernel
include module type of Hardcaml_formal_verification_kernel.Ebmc

(** Compile the circuit, run EBMC, read the result and display the verdict for each
    property. If a counterexample trace is found, the [on_trace] callback is applied with
    the trace. *)
val expect_all_properties
  :  ?reset:[ `High of string | `Low of string ]
  -> ?tmpdir:string
  -> ?circuit_database:Hardcaml.Circuit_database.t
  -> ?rtl_output_mode:[ `Full_hierarchy | `Top_level_and_blackboxes ]
       (** How to emit RTL for EBMC. Defaults to [`Full_hierarchy]. *)
  -> ?trace:bool
       (** Whether to request traces in EBMC's JSON output. Defaults to [true]. This is
           ignored in public releases. *)
  -> ?on_trace:(Counter_example_trace.t -> unit)
  -> bound:int
  -> Hardcaml.Circuit.t
  -> unit
