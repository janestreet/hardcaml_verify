open! Base
open Expect_test_helpers_base
open Hardcaml_verify
open Comb_gates

let%expect_test "input" =
  let a = input "a" 2 in
  print_s [%message (a : t)];
  [%expect
    {| (a ((Var (uid 2) (label (a 1 3 false))) (Var (uid 3) (label (a 0 3 false))))) |}]
;;

let%expect_test "addition" =
  let a = input "a" 2 in
  let b = input "b" 2 in
  let f = a +: b in
  print_s [%message (f : t)];
  (* boolean circuit *)
  [%expect
    {|
    (f (
      (Xor
        (uid 11)
        (arg1 (
          Xor
          (uid 10)
          (arg1 (Var (uid 4) (label (a 1 4 false))))
          (arg2 (Var (uid 6) (label (b 1 5 false))))))
        (arg2 (
          And
          (uid 9)
          (arg1 (Var (uid 5) (label (a 0 4 false))))
          (arg2 (Var (uid 7) (label (b 0 5 false)))))))
      (Xor
        (uid 8)
        (arg1 (Var (uid 5) (label (a 0 4 false))))
        (arg2 (Var (uid 7) (label (b 0 5 false)))))))
    |}];
  (* evaluate - this is done via cofactor all inputs and relying on constant propogation
     to reduce all outputs to constants. *)
  let eval a' b' =
    let f = cofactor ~var:a (of_int_trunc ~width:2 a') ~f in
    cofactor ~var:b (of_int_trunc ~width:2 b') ~f
  in
  let all = Array.init 4 ~f:(fun a -> Array.init 4 ~f:(eval a)) in
  print_s [%message (all : t array array)];
  [%expect
    {|
    (all (
      ((Gnd Gnd)
       (Gnd Vdd)
       (Vdd Gnd)
       (Vdd Vdd))
      ((Gnd Vdd)
       (Vdd Gnd)
       (Vdd Vdd)
       (Gnd Gnd))
      ((Vdd Gnd)
       (Vdd Vdd)
       (Gnd Gnd)
       (Gnd Vdd))
      ((Vdd Vdd)
       (Gnd Gnd)
       (Gnd Vdd)
       (Vdd Gnd))))
    |}]
;;
