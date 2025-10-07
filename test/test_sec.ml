open! Base
open Hardcaml
open Hardcaml_verify
open Expect_test_helpers_base
open Signal

let test_or1 () =
  Circuit.create_exn ~name:"foo" [ output "c" (input "a" 1 |: input "b" 1) ]
;;

let test_or2 () =
  Circuit.create_exn ~name:"foo" [ output "c" (input "x" 1 |: input "b" 1) ]
;;

let test_or3 () =
  Circuit.create_exn ~name:"foo" [ output "x" (input "a" 1 |: input "b" 1) ]
;;

let test_and () =
  Circuit.create_exn ~name:"foo" [ output "c" (input "a" 1 &: input "b" 1) ]
;;

let equivalent ?(verbose = false) ?instantiation_ports_match c1 c2 =
  let%bind.Or_error t = Sec.create ?instantiation_ports_match c1 c2 in
  if verbose then print_s [%message (c1 : Circuit.t) (c2 : Circuit.t) (t : Sec.t)];
  Sec.circuits_equivalent t
;;

let%expect_test "input and output port checks" =
  let result = equivalent (test_or1 ()) (test_or1 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}];
  let result = equivalent (test_or1 ()) (test_or2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        "[Sec.pair_signals_by_name] left and right circuits contain different names"
        (context input)
        (only_in_left  (a))
        (only_in_right (x)))))
    |}];
  let result = equivalent (test_or1 ()) (test_or3 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        "[Sec.pair_signals_by_name] left and right circuits contain different names"
        (context output)
        (only_in_left  (c))
        (only_in_right (x)))))
    |}];
  let result = equivalent (test_or1 ()) (test_and ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$a) (value 0))
          ((name input$b) (value 1))))))
    |}]
;;

(* Inputs and output swap (no logic involved) *)

let test_swap1 () =
  Circuit.create_exn ~name:"foo" [ output "x" (input "a" 1); output "y" (input "b" 1) ]
;;

let test_swap2 () =
  Circuit.create_exn ~name:"bar" [ output "y" (input "a" 1); output "x" (input "b" 1) ]
;;

let%expect_test "swap wires" =
  let result = equivalent (test_swap1 ()) (test_swap2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$a) (value 1))
          ((name input$b) (value 0))))))
    |}]
;;

(* Simple register based test.

   Note: These adders are logically the same: [(a+b)+c], [a+(b+c)] *)

let spec () = Reg_spec.create ~clock:(input "clock" 1) ()

let test_add_reg1 () =
  Circuit.create_exn
    ~name:"foo"
    [ output "x" (reg (spec ()) (input "a" 2 +: input "b" 2 +: input "c" 2) -- "reg1") ]
;;

let test_add_reg2 () =
  Circuit.create_exn
    ~name:"bar"
    [ output "x" (reg (spec ()) (input "a" 2 +: (input "b" 2 +: input "c" 2)) -- "reg1") ]
;;

let%expect_test "prove with registers" =
  let result = equivalent (test_add_reg1 ()) (test_add_reg2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}]
;;

(* Differing clocks are detected in circuits that are otherwise the same *)

let spec1 () = Reg_spec.create ~clock:(input "clock1" 1) ()
let spec2 () = Reg_spec.create ~clock:(input "clock2" 1) ()

let test_add_reg spec1 spec2 =
  Circuit.create_exn
    ~name:"foo"
    [ output
        "x"
        (reg spec1 (reg spec2 (input "a" 2 +: input "b" 2 +: input "c" 2) -- "reg1")
         -- "reg2")
    ]
;;

let test_add_reg1 () = test_add_reg (spec1 ()) (spec2 ())
let test_add_reg2 () = test_add_reg (spec2 ()) (spec1 ())

let%expect_test "show different clocks are detected" =
  (* multiple clocks, but correctly connected *)
  let result = equivalent ~verbose:false (test_add_reg1 ()) (test_add_reg1 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}];
  (* incorrectly connected clocks *)
  let result = equivalent ~verbose:false (test_add_reg1 ()) (test_add_reg2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$a)       (value 00))
          ((name input$b)       (value 00))
          ((name input$c)       (value 00))
          ((name input$clock1)  (value 1))
          ((name input$clock2)  (value 0))
          ((name register$reg1) (value 01))
          ((name register$reg2) (value 10))))))
    |}]
;;

(* Edge/Level of clock, reset *)

let test_spec1 () =
  let spec =
    Reg_spec.create
      ~clock:(input "clock" 1)
      ~reset:(input "reset" 1)
      ~clock_edge:Rising
      ~reset_edge:Rising
      ()
  in
  Circuit.create_exn ~name:"foo" [ output "x" (reg spec (input "a" 2) -- "reg1") ]
;;

let test_spec2 () =
  let spec =
    Reg_spec.create
      ~clock:(input "clock" 1)
      ~reset:(input "reset" 1)
      ~clock_edge:Falling
      ~reset_edge:Falling
      ()
  in
  Circuit.create_exn ~name:"foo" [ output "x" (reg spec (input "a" 2) -- "reg1") ]
;;

let%expect_test "edges and levels" =
  let result = equivalent (test_spec1 ()) (test_spec2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        ("Edge specifications do not match"
          (context clock_edge)
          (e (
            (left  Rising)
            (right Falling)))
          (name reg1))
        ("Edge specifications do not match"
          (context reset_edge)
          (e (
            (left  Rising)
            (right Falling)))
          (name reg1)))))
    |}]
;;

(* Counter logic with feedback. This shows the need for scheduling (topological sorting
   the circuit nodes) *)

let test_counter incr =
  let spec = spec () in
  let clear = input "clear" 1 in
  let counter =
    Signal.reg_fb spec ~width:8 ~f:(fun d -> mux2 clear (zero 8) (d +:. incr)) -- "cnt"
  in
  Circuit.create_exn ~name:"foo" [ output "counter" counter ]
;;

let%expect_test "logic with feedback" =
  let result = equivalent (test_counter 1) (test_counter 1) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}];
  let result = equivalent (test_counter 1) (test_counter 2) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$clear)  (value 0))
          ((name input$clock)  (value 1))
          ((name register$cnt) (value 00000000))))))
    |}]
;;

(* Simple instantiations *)

let inst1 n a b =
  let inst =
    Instantiation.create
      ~name:"foo"
      ~instance:("foo" ^ Int.to_string n)
      ~inputs:[ "a", a; "b", b ]
      ~outputs:[ "c", 3 ]
      ()
  in
  Instantiation.output inst "c"
;;

let inst2 n a =
  let inst =
    Instantiation.create
      ~name:"bar"
      ~instance:("bar" ^ Int.to_string n)
      ~inputs:[ "a", a ]
      ~outputs:[ "c", 5; "d", 5 ]
      ()
  in
  Instantiation.output inst "c", Instantiation.output inst "d"
;;

let test_inst1 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst1 1 a b in
  let d, e = inst2 1 a in
  Circuit.create_exn ~name:"top" [ output "c" c; output "d" d; output "e" e ]
;;

let test_inst2 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst1 1 b a in
  let d, e = inst2 1 a in
  Circuit.create_exn ~name:"top" [ output "c" c; output "d" d; output "e" e ]
;;

let test_inst3 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst1 1 a b in
  let d, e = inst2 1 a in
  Circuit.create_exn ~name:"top" [ output "c" c; output "d" e; output "e" d ]
;;

let test_inst4 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst1 1 a b in
  let d, e = inst2 2 a in
  Circuit.create_exn ~name:"top" [ output "c" c; output "d" d; output "e" e ]
;;

let%expect_test "instantiation" =
  let result = equivalent (test_inst1 ()) (test_inst1 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}];
  (* Inputs differ *)
  let result = equivalent (test_inst1 ()) (test_inst2 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$x)              (value 0))
          ((name input$y)              (value 1))
          ((name instantiation$bar1$c) (value 01111))
          ((name instantiation$bar1$d) (value 00011))
          ((name instantiation$foo1$c) (value 010))))))
    |}];
  (* Outputs of inst are wired differently *)
  let result = equivalent (test_inst1 ()) (test_inst3 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$x)              (value 0))
          ((name input$y)              (value 1))
          ((name instantiation$bar1$c) (value 10111))
          ((name instantiation$bar1$d) (value 01010))
          ((name instantiation$foo1$c) (value 100))))))
    |}];
  (* Instantiations names dont match *)
  let result = equivalent (test_inst1 ()) (test_inst4 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        "[Sec.pair_signals_by_name] left and right circuits contain different names"
        (context instantiation)
        (only_in_left  (bar1))
        (only_in_right (bar2)))))
    |}]
;;

let test_inst_with_cycle e_bit =
  let a = input "x" 1 in
  let b = wire 1 in
  let c = inst1 1 a b in
  let d, e = inst2 1 c in
  b <-- e.:(e_bit);
  Circuit.create_exn ~name:"top" [ output "d" d; output "e" e ]
;;

let%expect_test "cycle through instantiation" =
  let result = equivalent (test_inst_with_cycle 0) (test_inst_with_cycle 0) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}];
  let result = equivalent (test_inst_with_cycle 1) (test_inst_with_cycle 0) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Ok (
        Sat (
          ((name input$x)              (value 1))
          ((name instantiation$bar1$c) (value 10010))
          ((name instantiation$bar1$d) (value 10110))
          ((name instantiation$foo1$c) (value 011))))))
    |}]
;;

(* We allow instantiations to have different port sets. The following has differing inputs
   and outputs, but is still considered equivalent. *)

let inst3 n a =
  let inst =
    Instantiation.create
      ~name:"foo"
      ~instance:("foo" ^ Int.to_string n)
      ~inputs:[ "a", a ]
      ~outputs:[ "c", 3 ]
      ()
  in
  Instantiation.output inst "c"
;;

let inst4 n a b =
  let inst =
    Instantiation.create
      ~name:"foo"
      ~instance:("foo" ^ Int.to_string n)
      ~inputs:[ "a", a; "b", b ]
      ~outputs:[ "c", 3; "d", 12 ]
      ()
  in
  Instantiation.output inst "c"
;;

let test_inst5 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst3 1 a in
  let c = c |: repeat b ~count:3 in
  Circuit.create_exn ~name:"top" [ output "c" c ]
;;

let test_inst6 () =
  let a = input "x" 1 in
  let b = input "y" 1 in
  let c = inst4 1 a b in
  let c = c |: repeat b ~count:3 in
  Circuit.create_exn ~name:"top" [ output "c" c ]
;;

let%expect_test "instantiation port subsets" =
  let result =
    equivalent
      ~instantiation_ports_match:Left_is_subset_of_right
      (test_inst5 ())
      (test_inst6 ())
  in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect {| (result (Ok Unsat)) |}]
;;

(* Instantiation inputs and output must be the same width *)

let inst6 a b_width =
  let inst =
    Instantiation.create
      ~name:"foo"
      ~instance:"foo"
      ~inputs:[ "a", a ]
      ~outputs:[ "b", b_width ]
      ()
  in
  Instantiation.output inst "b"
;;

let test_inst7 () =
  let a = input "x" 1 in
  let b = inst6 a 1 in
  Circuit.create_exn ~name:"top" [ output "b" b ]
;;

let test_inst8 () =
  let a = input "x" 1 in
  let b = inst6 (repeat a ~count:2) 1 in
  Circuit.create_exn ~name:"top" [ output "b" b ]
;;

let test_inst9 () =
  let a = input "x" 1 in
  let b = inst6 a 2 in
  Circuit.create_exn ~name:"top" [ output "b" b.:(0) ]
;;

let%expect_test "instantiation input port width mismatch" =
  let result = equivalent (test_inst7 ()) (test_inst8 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        "[Sec.check_instantiation] input ports do not match"
        (instantiation_ports_match Exactly)
        (instantiation_signal (
          (left (
            instantiation
            (width 1)
            ("work.foo(rtl){foo}"
              (parameters ())
              (inputs  ((a x)))
              (outputs ((b 1))))))
          (right (
            instantiation
            (width 1)
            ("work.foo(rtl){foo}"
              (parameters ())
              (inputs  ((a cat)))
              (outputs ((b 1))))))))
        (unmatched_on_left ((a (wire (names (x)) (width 1)))))
        (unmatched_on_right ((a (cat (width 2) (arguments (x x)))))))))
    |}]
;;

let%expect_test "instantiation output port width mismatch" =
  let result = equivalent (test_inst7 ()) (test_inst9 ()) in
  print_s [%message (result : Sec.Equivalence_result.t Or_error.t)];
  [%expect
    {|
    (result (
      Error (
        "[Sec.check_instantiation] output ports do not match"
        (instantiation_ports_match Exactly)
        (s (
          (left (
            instantiation
            (width 1)
            ("work.foo(rtl){foo}"
              (parameters ())
              (inputs  ((a x)))
              (outputs ((b 1))))))
          (right (
            instantiation
            (width 2)
            ("work.foo(rtl){foo}"
              (parameters ())
              (inputs  ((a x)))
              (outputs ((b 2))))))))
        (p ((left ((b (1 0)))) (right ((b (2 0)))))))))
    |}]
;;
