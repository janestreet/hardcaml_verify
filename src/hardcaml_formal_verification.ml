include (
  Hardcaml_formal_verification_kernel :
    module type of Hardcaml_formal_verification_kernel
    with module Nusmv := Hardcaml_formal_verification_kernel.Nusmv
     and module Ebmc := Hardcaml_formal_verification_kernel.Ebmc)

module Nusmv = Nusmv
module Trace_to_waveform = Trace_to_waveform
module Ebmc = Ebmc
