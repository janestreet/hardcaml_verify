open! Base
open! Expect_test_helpers_base
open Hardcaml_formal_verification
open Hardcaml
open Hardcaml.Signal

let clock = input "clock" 1
let clear = input "clear" 1
let spec = Reg_spec.create ~clock ~clear ()
let reg ?(enable = vdd) d = reg spec ~enable d

let retime0 a b =
  let r0 = reg (a +: b) -- "r0" in
  let r1 = reg r0 -- "r1" in
  r1
;;

let retime1 a b =
  let a0 = reg a -- "a0" in
  let b0 = reg b -- "b0" in
  let s1 = reg (a0 +: b0) -- "s1" in
  s1
;;

let retimer =
  let a, b = input "a" 7, input "b" 7 in
  output "prop" (retime0 a b ==: retime1 a b)
;;

let display_waveform circuit trace =
  let waveform = Trace_to_waveform.convert circuit trace in
  Hardcaml_waveterm.Waveform.expect ~wave_scale:7 waveform
;;

let%expect_test "retime" =
  let properties = Property_manager.create () in
  let config =
    { Circuit.Config.default with
      property_manager = Some properties
    ; trace_properties = Property_manager.Trace_properties.all
    }
  in
  let () =
    let add name ltl =
      Property_manager.add_sva properties name Property.Sva.(asserts (Formula.of_ltl ltl))
    in
    add "prop_correct_in_two_cycles" (X (X (P retimer)));
    add "prop_correct_in_one_cycle" (X (P retimer))
  in
  let circuit = Circuit.create_exn ~config ~name:"retime" [ retimer ] in
  Ebmc.expect_all_properties ~on_trace:(display_waveform circuit) ~bound:10 circuit;
  [%expect
    {|
    (Refuted_with_trace prop_correct_in_one_cycle)
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │clock          ││                                                   │
    │               ││────────────────────────────────                   │
    │clear          ││                                                   │
    │               ││────────────────────────────────                   │
    │               ││────────────────────────────────                   │
    │a              ││ 00                                                │
    │               ││────────────────────────────────                   │
    │               ││────────────────┬───────────────                   │
    │b              ││ 10             │00                                │
    │               ││────────────────┴───────────────                   │
    │prop           ││                                                   │
    │               ││────────────────────────────────                   │
    │               ││────────────────────────────────                   │
    │a0             ││ 00                                                │
    │               ││────────────────────────────────                   │
    │               ││────────────────┬───────────────                   │
    │b0             ││ 01             │10                                │
    │               ││────────────────┴───────────────                   │
    │               ││────────────────┬───────────────                   │
    │r0             ││ 05             │10                                │
    │               ││────────────────┴───────────────                   │
    │               ││────────────────┬───────────────                   │
    │r1             ││ 00             │05                                │
    │               ││────────────────┴───────────────                   │
    │               ││────────────────────────────────                   │
    │s1             ││ 01                                                │
    │               ││────────────────────────────────                   │
    └───────────────┘└───────────────────────────────────────────────────┘
    e1585c70ab8eae9d6337c46bb888da1e
    (Proved prop_correct_in_two_cycles)
    |}]
;;

let pop_circuit () =
  let properties = Property_manager.create () in
  let config =
    { Circuit.Config.default with
      property_manager = Some properties
    ; trace_properties = Property_manager.Trace_properties.all
    }
  in
  let x = input "x" 64 in
  let t = of_int_trunc ~width:7 30 -- "thresh" in
  let y = output "y" (popcount x <=: t) in
  Property_manager.add_sva
    properties
    "prop_falsify_me"
    (Property.Sva.of_ltl (Property.LTL.asserts (P y)));
  Circuit.create_exn ~config ~name:"pop" [ y ]
;;

let%expect_test "long bit vector with trace" =
  let circuit = pop_circuit () in
  Ebmc.expect_all_properties ~on_trace:(display_waveform circuit) ~bound:10 circuit;
  [%expect
    {|
    (Refuted_with_trace prop_falsify_me)
    ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
    │               ││────────────────                                   │
    │x              ││ 00000000FFFFFF.                                   │
    │               ││────────────────                                   │
    │y              ││                                                   │
    │               ││────────────────                                   │
    │               ││────────────────                                   │
    │thresh         ││ 1E                                                │
    │               ││────────────────                                   │
    └───────────────┘└───────────────────────────────────────────────────┘
    a3cc30bdae25e1625313419d9dcb9539
    |}]
;;

module Always_one = struct
  module I = struct
    type 'a t = { i : 'a } [@@deriving hardcaml]
  end

  module O = struct
    type 'a t = { o : 'a } [@@deriving hardcaml]
  end

  let create _scope (_ : _ I.t) = { O.o = vdd }

  let hierarchical scope i =
    let module H = Hierarchy.In_scope (I) (O) in
    H.hierarchical ~scope ~name:"always_one" create i
  ;;
end

let blackbox_test_circuit () =
  let scope = Scope.create () in
  let properties = Property_manager.create () in
  let child = Always_one.hierarchical scope { i = input "i" 1 } in
  let prop = output "prop" child.o in
  Property_manager.add_sva
    properties
    "blackbox_output_is_one"
    (Property.Sva.of_ltl (Property.LTL.asserts (P prop)));
  let config =
    { Circuit.Config.default with
      property_manager = Some properties
    ; trace_properties = Property_manager.Trace_properties.all
    }
  in
  Circuit.create_exn ~config ~name:"blackbox_top" [ prop ], Scope.circuit_database scope
;;

let status_without_trace = function
  | Ebmc.Ebmc_result.Assumed -> "assumed"
  | Proved | Proved_with_trace _ -> "proved"
  | Refuted | Refuted_with_trace _ -> "refuted"
  | Failure _ -> "failure"
;;

let%expect_test "top-level-and-blackboxes makes child outputs unconstrained" =
  let check rtl_output_mode =
    let circuit, database = blackbox_test_circuit () in
    let results =
      Ebmc.solve ~circuit_database:(Some database) ~rtl_output_mode ~bound:1 circuit
    in
    print_s
      [%message
        (rtl_output_mode : [ `Full_hierarchy | `Top_level_and_blackboxes ])
          ~status:
            (Map.find_exn results "blackbox_output_is_one" |> status_without_trace
             : string)]
  in
  check `Full_hierarchy;
  check `Top_level_and_blackboxes;
  [%expect
    {|
    ((rtl_output_mode Full_hierarchy)
     (status          proved))
    ((rtl_output_mode Top_level_and_blackboxes)
     (status          refuted))
    |}]
;;
