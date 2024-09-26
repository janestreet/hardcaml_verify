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

let%expect_test "retime" =
  let nusmv = Nusmv.create ~name:"retime" [ LTL Property.LTL.(g (p (retimer ()))) ] in
  Nusmv.write Stdio.stdout nusmv;
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
  Nusmv.write Stdio.stdout nusmv;
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
                 not named, the propery generation code would not work correctly. This \
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
  Nusmv.write Stdio.stdout nusmv;
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
