include module type of Hardcaml_verify_kernel.Nusmv

module Counter_example_trace : sig
  type nusmv := t

  include module type of Counter_example_trace

  val to_waveform : nusmv -> t -> Hardcaml_waveterm.Waveform.t
end
