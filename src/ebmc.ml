open! Base
open Stdio
include Hardcaml_formal_verification_kernel.Ebmc

let expect_all_properties
  ?reset
  ?tmpdir
  ?circuit_database
  ?rtl_output_mode
  ?trace
  ?(on_trace = Fn.const ())
  ~bound
  circuit
  =
  let result =
    solve ?reset ?tmpdir ~circuit_database ?rtl_output_mode ?trace ~bound circuit
  in
  Map.iteri result ~f:(fun ~key ~data ->
    match data with
    | Ebmc_result.Assumed -> print_s [%message "Assumed" key]
    | Proved -> print_s [%message "Proved" key]
    | Refuted -> print_s [%message "Refuted" key]
    | Refuted_with_trace trace ->
      print_s [%message "Refuted_with_trace" key];
      on_trace trace
    | Proved_with_trace trace ->
      print_s [%message "Proved_with_trace" key];
      on_trace trace
    | Failure data -> print_s [%message "Failed" (data : Sexp.t)])
;;
