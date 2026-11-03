include module type of Hardcaml_formal_verification_kernel.Nusmv

val to_waveform
  :  t
  -> Hardcaml_formal_verification_kernel.Counter_example_trace.t
  -> Hardcaml_waveterm.Waveform.t
