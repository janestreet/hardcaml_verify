open Base
open Hardcaml_verify

let print_is_proved ?(verbose = true) eqn =
  ignore (Solver.solve ~print_model:verbose Comb_gates.(cnf ~:eqn) : _ Or_error.t)
;;

let%expect_test "check onehot" =
  let open Comb_gates in
  let module Is_one_hot = Is_one_hot.Make (Comb_gates) in
  let vec = input "vec" 8 in
  let count = popcount vec in
  let is_one_hot = Is_one_hot.create vec in
  print_is_proved (is_one_hot.no_bit_set ==: (count ==:. 0));
  [%expect
    {|
       ____    __________
      / __ \  / ____/ __ \
     / / / / / __/ / / / /
    / /_/ / / /___/ /_/ /
    \___\_\/_____/_____/
    |}];
  print_is_proved (is_one_hot.one_bit_set ==: (count ==:. 1));
  [%expect
    {|
       ____    __________
      / __ \  / ____/ __ \
     / / / / / __/ / / / /
    / /_/ / / /___/ /_/ /
    \___\_\/_____/_____/
    |}];
  print_is_proved (is_one_hot.many_bits_set ==: (count >:. 1));
  [%expect
    {|
       ____    __________
      / __ \  / ____/ __ \
     / / / / / __/ / / / /
    / /_/ / / /___/ /_/ /
    \___\_\/_____/_____/
    |}]
;;
