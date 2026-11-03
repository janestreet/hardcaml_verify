open Base
open Expect_test_helpers_base
open Hardcaml
open Hardcaml_formal_verification

module Delayed_adder = struct
  open Signal

  module I = struct
    type 'a t =
      { clocking : 'a Clocking.t
      ; foo : 'a [@bits 16]
      ; bar : 'a [@bits 16]
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t = { baz : 'a [@bits 16] } [@@deriving hardcaml]
  end

  let create (input : _ I.t) =
    let spec_with_clear = Clocking.to_spec input.clocking in
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
    let clear = inputs.clocking.clear.(0) in
    let open Property.LTL.Formula in
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
    let open Property.LTL.Formula in
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
      let waveform = Nusmv.to_waveform model cet in
      Hardcaml_waveterm.Waveform.expect ~wave_scale:7 waveform);
  [%expect
    {|
    (proofs
     ((Exists_counter_example
       ((states
         (((clear 0) (clock 0) (bar 0000000000000001) (foo 0000000000000000)
           (_150 0000000000000000) (_148 0000000000000000)
           (_149 0000000000000000) (_147 0000000000000000) (_144 0) (_143 0)
           (_151 0000000000000000) (_146 0000000000000001)
           (_152 0000000000000001) (_145 0000000000000000)
           (_153 0000000000000001) (_218 1) (_202 1) (_186 0)
           (baz 0000000000000001))
          ((clear 1) (bar 0000000000000000) (_150 0000000000000001) (_144 1)
           (_151 0000000000000001) (_146 0000000000000000) (_202 0))
          ((clear 0) (bar 0000000000000001) (_150 0000000000000000) (_144 0)
           (_151 0000000000000000) (_146 0000000000000001) (_202 1))))))
      (Exists_counter_example
       ((states
         (((clear 0) (clock 0) (bar 0000000000000001) (foo 0000000000000000)
           (_150 0000000000000000) (_148 0000000000000000)
           (_149 0000000000000000) (_147 0000000000000000) (_144 0) (_143 0)
           (_151 0000000000000000) (_146 0000000000000001)
           (_152 0000000000000001) (_145 0000000000000000)
           (_153 0000000000000001) (_218 1) (_202 1) (_186 0)
           (baz 0000000000000001))
          ((clear 1) (bar 0000000000000000) (_150 0000000000000001) (_144 1)
           (_151 0000000000000001) (_146 0000000000000000) (_202 0))
          ((clear 0) (bar 0000000000000001) (_150 0000000000000000) (_144 0)
           (_151 0000000000000000) (_146 0000000000000001) (_202 1))))))))
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │clock          ││                                                   │
    │               ││────────────────────────────────────────────────   │
    │clear          ││                ┌───────────────┐                  │
    │               ││────────────────┘               └───────────────   │
    │               ││────────────────┬───────────────┬───────────────   │
    │bar            ││ 0001           │0000           │0001              │
    │               ││────────────────┴───────────────┴───────────────   │
    │               ││────────────────────────────────────────────────   │
    │foo            ││ 0000                                              │
    │               ││────────────────────────────────────────────────   │
    │               ││────────────────────────────────────────────────   │
    │baz            ││ 0001                                              │
    │               ││────────────────────────────────────────────────   │
    └───────────────┘└───────────────────────────────────────────────────┘
    9806f319ff55a34b323dd0c3f7799074
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │clock          ││                                                   │
    │               ││────────────────────────────────────────────────   │
    │clear          ││                ┌───────────────┐                  │
    │               ││────────────────┘               └───────────────   │
    │               ││────────────────┬───────────────┬───────────────   │
    │bar            ││ 0001           │0000           │0001              │
    │               ││────────────────┴───────────────┴───────────────   │
    │               ││────────────────────────────────────────────────   │
    │foo            ││ 0000                                              │
    │               ││────────────────────────────────────────────────   │
    │               ││────────────────────────────────────────────────   │
    │baz            ││ 0001                                              │
    │               ││────────────────────────────────────────────────   │
    └───────────────┘└───────────────────────────────────────────────────┘
    9806f319ff55a34b323dd0c3f7799074
    |}]
;;
