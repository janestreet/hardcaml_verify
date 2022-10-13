open Base
open Hardcaml
include Bits_list.Make (Basic_gates)

let input name width =
  let label = Label.create name ~width in
  List.init width ~f:(fun bit -> Basic_gates.var label.(bit)) |> List.rev
;;

let cofactor ~var v ~f =
  let cofactor_f f =
    List.fold2_exn var v ~init:f ~f:(fun f var v -> Basic_gates.cofactor ~var v ~f)
  in
  List.map f ~f:cofactor_f
;;

let forall x ~f =
  let forall_f f =
    List.fold_right x ~init:f ~f:(fun var f -> Basic_gates.forall var ~f)
  in
  List.map f ~f:forall_f
;;

let exists x ~f =
  let exists_f f =
    List.fold_right x ~init:f ~f:(fun var f -> Basic_gates.exists var ~f)
  in
  List.map f ~f:exists_f
;;

let cnf = Basic_gates.cnf
