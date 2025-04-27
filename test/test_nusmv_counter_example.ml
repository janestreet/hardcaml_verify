open Base
open Expect_test_helpers_base
open Hardcaml
open Hardcaml_verify

module Delayed_adder = struct
  open Signal

  module I = struct
    type 'a t =
      { clock : 'a
      ; clear : 'a
      ; foo : 'a [@bits 16]
      ; bar : 'a [@bits 16]
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t = { baz : 'a [@bits 16] } [@@deriving hardcaml]
  end

  let create (input : _ I.t) =
    let spec_with_clear = Reg_spec.create ~clock:input.clock ~clear:input.clear () in
    let foo_reg = reg spec_with_clear ~enable:vdd input.foo in
    let bar_reg = reg spec_with_clear ~enable:vdd input.bar in
    { O.baz = input.foo ^: input.bar ^: foo_reg ^: bar_reg }
  ;;
end

let parse_word_constant = Nusmv.Output_parser.parse_word_constant

let%expect_test "parse word constant" =
  Stdio.print_s [%message (parse_word_constant "0uh4_f" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "0so3_3" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "0d10_254" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "0sb8_10101010" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "0uh32_fb73da62" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "- 0b8_1" : Bits.t)];
  Stdio.print_s [%message (parse_word_constant "- 0h16_7fff" : Bits.t)];
  [%expect
    {|
    ("parse_word_constant \"0uh4_f\"" 1111)
    ("parse_word_constant \"0so3_3\"" 011)
    ("parse_word_constant \"0d10_254\"" 0011111110)
    ("parse_word_constant \"0sb8_10101010\"" 10101010)
    ("parse_word_constant \"0uh32_fb73da62\"" 11111011011100111101101001100010)
    ("parse_word_constant \"- 0b8_1\"" 11111111)
    ("parse_word_constant \"- 0h16_7fff\"" 1000000000000001)
    |}]
;;

let%expect_test "dont parse decimal constant without size" =
  require_does_raise (fun () -> parse_word_constant "0d_10");
  [%expect {| ("Decimal word constants must specify a size" 0d_10) |}]
;;

let%expect_test "dont parse if size lower than constant" =
  require_does_raise (fun () -> parse_word_constant "0b2_1011");
  require_does_raise (fun () -> parse_word_constant "0o4_37");
  require_does_raise (fun () -> parse_word_constant "0d4_16023");
  require_does_raise (fun () -> parse_word_constant "0h4_ff");
  [%expect
    {|
    ("Parsed word constant is wider than its specified width" 0b2_1011)
    ("Parsed word constant is wider than its specified width" 0o4_37)
    ("Parsed word constant is wider than its specified width" 0d4_16023)
    ("Parsed word constant is wider than its specified width" 0h4_ff)
    |}]
;;

let%expect_test "clear resets registers" =
  let open Delayed_adder in
  let module Model = Nusmv.With_interface (I) (O) in
  let model = Model.create ~name:"delayed_adder" Delayed_adder.create in
  let inputs = Model.ltl model |> Nusmv.Circuit_properties.inputs in
  let outputs = Model.ltl model |> Nusmv.Circuit_properties.outputs in
  let properties =
    let clear = inputs.clear.(0) in
    let open Property.LTL in
    [ Nusmv.LTL (G (clear ==>: X (inputs.foo.(0) ^: inputs.bar.(0) ==: outputs.baz.(0))))
    ; Nusmv.LTL (G (clear ==>: X (inputs.foo.(0) ^: inputs.bar.(0) ==: outputs.baz.(0))))
    ]
  in
  let model = Model.create_specification model properties in
  let proofs = Nusmv.run model in
  Stdio.print_s [%message (proofs : Nusmv.Proof_result.t list)];
  [%expect {| (proofs (Tautology Tautology)) |}]
;;

let%expect_test "example NuSMV failure trace" =
  let open Delayed_adder in
  let module Model = Nusmv.With_interface (I) (O) in
  let model = Model.create ~name:"delayed_adder" Delayed_adder.create in
  let inputs = Model.ltl model |> Nusmv.Circuit_properties.inputs in
  let outputs = Model.ltl model |> Nusmv.Circuit_properties.outputs in
  let properties =
    let open Property.LTL in
    [ Nusmv.LTL (inputs.foo.(0) ==: inputs.bar.(0))
    ; Nusmv.LTL (inputs.foo.(0) ==: outputs.baz.(0))
    ]
  in
  let model = Model.create_specification model properties in
  let proofs = Nusmv.run model in
  Stdio.print_s [%message (proofs : Nusmv.Proof_result.t list)];
  List.iter proofs ~f:(fun proof ->
    match proof with
    | Nusmv.Proof_result.Tautology -> Stdio.print_endline "Tautology"
    | Nusmv.Proof_result.Exists_counter_example cet ->
      let waveform = Nusmv.Counter_example_trace.to_waveform model cet in
      Hardcaml_waveterm.Waveform.expect waveform);
  [%expect
    {|
    (proofs
     ((Exists_counter_example
       ((states
         (((clear 0) (clock 0) (bar 0000000000000001) (foo 0000000000000000)
           (_16 0000000000000000) (_14 0000000000000000) (_15 0000000000000000)
           (_13 0000000000000000) (_2 0) (_4 0) (_17 0000000000000000)
           (_5 0000000000000001) (_18 0000000000000001) (_6 0000000000000000)
           (_19 0000000000000001) (_20 1) (_21 1) (_22 0) (baz 0000000000000001))
          ((clear 1) (bar 0000000000000000) (_16 0000000000000001) (_2 1)
           (_17 0000000000000001) (_5 0000000000000000) (_21 0))
          ((clear 0) (bar 0000000000000001) (_16 0000000000000000) (_2 0)
           (_17 0000000000000000) (_5 0000000000000001) (_21 1))))))
      (Exists_counter_example
       ((states
         (((clear 0) (clock 0) (bar 0000000000000001) (foo 0000000000000000)
           (_16 0000000000000000) (_14 0000000000000000) (_15 0000000000000000)
           (_13 0000000000000000) (_2 0) (_4 0) (_17 0000000000000000)
           (_5 0000000000000001) (_18 0000000000000001) (_6 0000000000000000)
           (_19 0000000000000001) (_20 1) (_21 1) (_22 0) (baz 0000000000000001))
          ((clear 1) (bar 0000000000000000) (_16 0000000000000001) (_2 1)
           (_17 0000000000000001) (_5 0000000000000000) (_21 0))
          ((clear 0) (bar 0000000000000001) (_16 0000000000000000) (_2 0)
           (_17 0000000000000000) (_5 0000000000000001) (_21 1))))))))
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │clock          ││                                                   │
    │               ││────────────────────────                           │
    │clear          ││        ┌───────┐                                  │
    │               ││────────┘       └───────                           │
    │               ││────────┬───────┬───────                           │
    │bar            ││ 0001   │0000   │0001                              │
    │               ││────────┴───────┴───────                           │
    │               ││────────────────────────                           │
    │foo            ││ 0000                                              │
    │               ││────────────────────────                           │
    │               ││────────────────────────                           │
    │baz            ││ 0001                                              │
    │               ││────────────────────────                           │
    └───────────────┘└───────────────────────────────────────────────────┘
    b6de3882028ace1cf6833ac46d4bebd7
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │clock          ││                                                   │
    │               ││────────────────────────                           │
    │clear          ││        ┌───────┐                                  │
    │               ││────────┘       └───────                           │
    │               ││────────┬───────┬───────                           │
    │bar            ││ 0001   │0000   │0001                              │
    │               ││────────┴───────┴───────                           │
    │               ││────────────────────────                           │
    │foo            ││ 0000                                              │
    │               ││────────────────────────                           │
    │               ││────────────────────────                           │
    │baz            ││ 0001                                              │
    │               ││────────────────────────                           │
    └───────────────┘└───────────────────────────────────────────────────┘
    b6de3882028ace1cf6833ac46d4bebd7
    |}]
;;
