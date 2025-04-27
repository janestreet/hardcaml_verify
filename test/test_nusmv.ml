open! Base
open! Expect_test_helpers_base
open Hardcaml_verify
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
  let s1 = reg (a0 +: b0) in
  s1
;;

let retimer () =
  let a, b = input "a" 8, input "b" 8 in
  output "prop" (retime0 a b ==: retime1 a b)
;;

let print nusmv = Nusmv.to_rope nusmv |> Rope.to_string |> Stdio.Out_channel.print_string

let%expect_test "retime" =
  let nusmv = Nusmv.create ~name:"retime" [ LTL Property.LTL.(g (p (retimer ()))) ] in
  print nusmv;
  [%expect
    {|
    MODULE main

    -- inputs
    VAR clear : unsigned word [1];
    VAR clock : unsigned word [1];
    VAR b : unsigned word [8];
    VAR a : unsigned word [8];

    -- registers
    VAR b0 : unsigned word [8];
    VAR a0 : unsigned word [8];
    VAR _18 : unsigned word [8];
    VAR r0 : unsigned word [8];
    VAR r1 : unsigned word [8];

    -- combinatorial logic
    DEFINE _17 := 0h8_00;
    DEFINE _14 := 0h8_00;
    DEFINE _12 := 0h8_00;
    DEFINE _16 := a0 + b0;
    DEFINE _10 := 0h8_00;
    DEFINE _8 := 0h8_00;
    DEFINE _7 := a + b;
    DEFINE _19 := word1(r1 = _18);
    DEFINE prop := _19;

    -- register updates
    ASSIGN init(b0) := 0h8_00;
    ASSIGN next(b0) := (bool(clear)?_14:b);
    ASSIGN init(a0) := 0h8_00;
    ASSIGN next(a0) := (bool(clear)?_12:a);
    ASSIGN init(_18) := 0h8_00;
    ASSIGN next(_18) := (bool(clear)?_17:_16);
    ASSIGN init(r0) := 0h8_00;
    ASSIGN next(r0) := (bool(clear)?_8:_7);
    ASSIGN init(r1) := 0h8_00;
    ASSIGN next(r1) := (bool(clear)?_10:r0);

    -- outputs
    DEFINE __ap_prop := prop;

    -- SPECS
    LTLSPEC (G bool(__ap_prop));
    |}]
;;

let%expect_test "register output == register input at previous cycle, if enabled" =
  let module P = Property.LTL in
  let enable = input "enable" 1 in
  let d = input "d" 1 in
  let q = reg ~enable d in
  let q = output "q" q in
  let d_is_next_q = P.(p d ==: X (p q)) in
  let prop = P.(g (~:(p clear) &: p enable ==>: d_is_next_q)) in
  let nusmv = Nusmv.create ~name:"retime" [ LTL prop ] in
  print nusmv;
  [%expect
    {|
    MODULE main

    -- inputs
    VAR clock : unsigned word [1];
    VAR d : unsigned word [1];
    VAR enable : unsigned word [1];
    VAR clear : unsigned word [1];

    -- registers
    VAR _11 : unsigned word [1];

    -- combinatorial logic
    DEFINE _10 := 0h1_0;
    DEFINE q := _11;

    -- register updates
    ASSIGN init(_11) := 0h1_0;
    ASSIGN next(_11) := (bool(clear)?_10:(bool(enable)?d:_11));

    -- outputs
    DEFINE __ap_clear := clear;
    DEFINE __ap_enable := enable;
    DEFINE __ap_d := d;
    DEFINE __ap_q := q;

    -- SPECS
    LTLSPEC (G ((!((!bool(__ap_clear)) & bool(__ap_enable))) | (!((bool(__ap_d) & (!(X bool(__ap_q)))) | ((!bool(__ap_d)) & (X bool(__ap_q)))))));
    |}]
;;

let%expect_test "Due to circuit rewriting, internal signals get new uids. If they were \
                 not named, the property generation code would not work correctly. This \
                 is now fixed and the following works - in particular the expression to \
                 create the clear/enable logic can not be done in hardcaml and doesn't \
                 need to be lifted into the temporal logic."
  =
  let module P = Property.LTL in
  let enable = input "enable" 1 in
  let d = input "d" 1 in
  let q = reg ~enable d in
  let q = output "q" q in
  let d_is_next_q = P.(p d ==: X (p q)) in
  let not_clear_and_enable = ~:clear &: enable in
  let prop = P.(g (p not_clear_and_enable ==>: d_is_next_q)) in
  let nusmv = Nusmv.create ~name:"retime" [ LTL prop ] in
  print nusmv;
  [%expect
    {|
    MODULE main

    -- inputs
    VAR enable : unsigned word [1];
    VAR clear : unsigned word [1];
    VAR clock : unsigned word [1];
    VAR d : unsigned word [1];

    -- registers
    VAR _12 : unsigned word [1];

    -- combinatorial logic
    DEFINE _9 := !clear;
    DEFINE _10 := _9 & enable;
    DEFINE _11 := 0h1_0;
    DEFINE q := _12;

    -- register updates
    ASSIGN init(_12) := 0h1_0;
    ASSIGN next(_12) := (bool(clear)?_11:(bool(enable)?d:_12));

    -- outputs
    DEFINE __ap_d := d;
    DEFINE __ap_q := q;
    DEFINE __ap_1 := _10;

    -- SPECS
    LTLSPEC (G ((!bool(__ap_1)) | (!((bool(__ap_d) & (!(X bool(__ap_q)))) | ((!bool(__ap_d)) & (X bool(__ap_q)))))));
    |}]
;;

let%expect_test "muxs" =
  let module P = Property.LTL in
  let sel = input "sel" 2 in
  let d = List.init 4 ~f:(fun i -> input [%string "d%{i#Int}"] 4) in
  let q = mux sel d in
  let prop = P.(g (p (q ==:. 0))) in
  let nusmv = Nusmv.create ~name:"foo" [ LTL prop ] in
  print nusmv;
  [%expect
    {|
    MODULE main

    -- inputs
    VAR d3 : unsigned word [4];
    VAR d2 : unsigned word [4];
    VAR d1 : unsigned word [4];
    VAR d0 : unsigned word [4];
    VAR sel : unsigned word [2];

    -- registers

    -- combinatorial logic
    DEFINE _8 := 0h4_0;
    DEFINE _7 :=
      case
        sel=0h2_0: d0;
        sel=0h2_1: d1;
        sel=0h2_2: d2;
        TRUE: d3;
      esac;
    DEFINE _9 := word1(_7 = _8);

    -- register updates

    -- outputs
    DEFINE __ap_1 := _9;

    -- SPECS
    LTLSPEC (G bool(__ap_1));
    |}]
;;

let%expect_test "cases" =
  let module P = Property.LTL in
  let q =
    cases
      ~default:(input "default" 8)
      (input "select" 32)
      (List.init 16 ~f:(fun i -> random ~width:32, input [%string "v%{i#Int}"] 8))
  in
  let prop = P.(g (p (q ==:. 0))) in
  let nusmv = Nusmv.create ~name:"foo" [ LTL prop ] in
  print nusmv;
  [%expect
    {|
    MODULE main

    -- inputs
    VAR default : unsigned word [8];
    VAR v15 : unsigned word [8];
    VAR v14 : unsigned word [8];
    VAR v13 : unsigned word [8];
    VAR v12 : unsigned word [8];
    VAR v11 : unsigned word [8];
    VAR v10 : unsigned word [8];
    VAR v9 : unsigned word [8];
    VAR v8 : unsigned word [8];
    VAR v7 : unsigned word [8];
    VAR v6 : unsigned word [8];
    VAR v5 : unsigned word [8];
    VAR v4 : unsigned word [8];
    VAR v3 : unsigned word [8];
    VAR v2 : unsigned word [8];
    VAR v1 : unsigned word [8];
    VAR v0 : unsigned word [8];
    VAR select : unsigned word [32];

    -- registers

    -- combinatorial logic
    DEFINE _37 := 0h8_00;
    DEFINE _36 :=
      case
        select=0h32_0bd44b2d: v0;
        select=0h32_3f664094: v1;
        select=0h32_e8316bb2: v2;
        select=0h32_ffa8e768: v3;
        select=0h32_24c87e26: v4;
        select=0h32_386f7da0: v5;
        select=0h32_25177962: v6;
        select=0h32_233fa986: v7;
        select=0h32_7f3d252a: v8;
        select=0h32_efac79a0: v9;
        select=0h32_498cda36: v10;
        select=0h32_05e8cd61: v11;
        select=0h32_8ced26fc: v12;
        select=0h32_e20f2a93: v13;
        select=0h32_4e8ec765: v14;
        select=0h32_98f8d4c3: v15;
        TRUE: default;
      esac;
    DEFINE _38 := word1(_36 = _37);

    -- register updates

    -- outputs
    DEFINE __ap_1 := _38;

    -- SPECS
    LTLSPEC (G bool(__ap_1));
    |}]
;;
