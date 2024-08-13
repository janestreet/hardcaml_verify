include (
  Hardcaml_verify_kernel :
    module type of Hardcaml_verify_kernel
    with module Nusmv := Hardcaml_verify_kernel.Nusmv)

module Nusmv = Nusmv
