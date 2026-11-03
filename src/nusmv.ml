open! Base
include Hardcaml_formal_verification_kernel.Nusmv

let to_waveform nusmv counter_example_trace =
  Trace_to_waveform.convert (circuit nusmv) counter_example_trace
;;
