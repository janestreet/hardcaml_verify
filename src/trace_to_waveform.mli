open Hardcaml
open Hardcaml_formal_verification_kernel

val convert : Circuit.t -> Counter_example_trace.t -> Hardcaml_waveterm.Waveform.t
