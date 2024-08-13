open! Base
open Expect_test_helpers_base
open Hardcaml_verify
open Basic_gates

let%expect_test "basic gate constructors" =
  print_s [%message (vdd : t) (gnd : t)];
  [%expect
    {|
    ((vdd Vdd)
     (gnd Gnd))
    |}];
  let a, b = var (Label.create1 "foo"), var (Label.create1 "bar") in
  print_s [%message (a : t) (b : t)];
  [%expect
    {|
    ((a (Var (uid 3) (label (foo 0 2 false))))
     (b (Var (uid 2) (label (bar 0 1 false)))))
    |}];
  print_s [%message (~:a : t)];
  [%expect {| ("~: a" (Not (uid 4) (arg (Var (uid 3) (label (foo 0 2 false)))))) |}];
  print_s [%message (a &: b : t)];
  [%expect
    {|
    ("a &: b" (
      And
      (uid 5)
      (arg1 (Var (uid 3) (label (foo 0 2 false))))
      (arg2 (Var (uid 2) (label (bar 0 1 false))))))
    |}];
  print_s [%message (a |: b : t)];
  [%expect
    {|
    ("a |: b" (
      Or
      (uid 6)
      (arg1 (Var (uid 3) (label (foo 0 2 false))))
      (arg2 (Var (uid 2) (label (bar 0 1 false))))))
    |}];
  print_s [%message (a ^: b : t)];
  [%expect
    {|
    ("a ^: b" (
      Xor
      (uid 7)
      (arg1 (Var (uid 3) (label (foo 0 2 false))))
      (arg2 (Var (uid 2) (label (bar 0 1 false))))))
    |}]
;;

let%expect_test "constant propogation (~:)" =
  let a = var (Label.create1 "a") in
  print_s [%message (~:gnd : t) (~:vdd : t)];
  [%expect
    {|
    (("~: gnd" Vdd)
     ("~: vdd" Gnd))
    |}];
  print_s [%message (~:(~:a) : t)];
  [%expect {| ("~: (~: a)" (Var (uid 8) (label (a 0 3 false)))) |}]
;;

let%expect_test "constant propogation (&:)" =
  let a, b = var (Label.create1 "a"), var (Label.create1 "b") in
  print_s [%message (gnd &: gnd : t) (gnd &: vdd : t) (vdd &: gnd : t) (vdd &: vdd : t)];
  [%expect
    {|
    (("gnd &: gnd" Gnd)
     ("gnd &: vdd" Gnd)
     ("vdd &: gnd" Gnd)
     ("vdd &: vdd" Vdd))
    |}];
  print_s [%message (a &: gnd : t)];
  [%expect {| ("a &: gnd" Gnd) |}];
  print_s [%message (gnd &: b : t)];
  [%expect {| ("gnd &: b" Gnd) |}];
  print_s [%message (a &: vdd : t)];
  [%expect {| ("a &: vdd" (Var (uid 11) (label (a 0 5 false)))) |}];
  print_s [%message (vdd &: b : t)];
  [%expect {| ("vdd &: b" (Var (uid 10) (label (b 0 4 false)))) |}]
;;

let%expect_test "constant propogation (|:)" =
  let a, b = var (Label.create1 "a"), var (Label.create1 "b") in
  print_s [%message (gnd |: gnd : t) (gnd |: vdd : t) (vdd |: gnd : t) (vdd |: vdd : t)];
  [%expect
    {|
    (("gnd |: gnd" Gnd)
     ("gnd |: vdd" Vdd)
     ("vdd |: gnd" Vdd)
     ("vdd |: vdd" Vdd))
    |}];
  print_s [%message (a |: gnd : t)];
  [%expect {| ("a |: gnd" (Var (uid 13) (label (a 0 7 false)))) |}];
  print_s [%message (gnd |: b : t)];
  [%expect {| ("gnd |: b" (Var (uid 12) (label (b 0 6 false)))) |}];
  print_s [%message (a |: vdd : t)];
  [%expect {| ("a |: vdd" Vdd) |}];
  print_s [%message (vdd |: b : t)];
  [%expect {| ("vdd |: b" Vdd) |}]
;;

let%expect_test "constant propogation (^:)" =
  let a, b = var (Label.create1 "a"), var (Label.create1 "b") in
  print_s [%message (gnd ^: gnd : t) (gnd ^: vdd : t) (vdd ^: gnd : t) (vdd ^: vdd : t)];
  [%expect
    {|
    (("gnd ^: gnd" Gnd)
     ("gnd ^: vdd" Vdd)
     ("vdd ^: gnd" Vdd)
     ("vdd ^: vdd" Gnd))
    |}];
  print_s [%message (a ^: gnd : t)];
  [%expect {| ("a ^: gnd" (Var (uid 15) (label (a 0 9 false)))) |}];
  print_s [%message (gnd ^: b : t)];
  [%expect {| ("gnd ^: b" (Var (uid 14) (label (b 0 8 false)))) |}];
  print_s [%message (a ^: vdd : t)];
  [%expect {| ("a ^: vdd" (Not (uid 16) (arg (Var (uid 15) (label (a 0 9 false)))))) |}];
  print_s [%message (vdd ^: b : t)];
  [%expect {| ("vdd ^: b" (Not (uid 17) (arg (Var (uid 14) (label (b 0 8 false)))))) |}]
;;
