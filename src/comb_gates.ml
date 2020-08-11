open Base
open Hardcaml

module Gates = struct
  (* msb first *)
  type t = Basic_gates.t list [@@deriving compare, sexp_of]

  let equal = [%compare.equal: t]
  let empty = []
  let is_empty = List.is_empty
  let width x = List.length x

  let of_constant b =
    Constant.to_bit_list b
    |> List.map ~f:(function
      | 0 -> Basic_gates.gnd
      | 1 -> Basic_gates.vdd
      | _ -> raise_s [%message "[of_constant]"])
  ;;

  let to_constant b =
    List.map b ~f:(fun b ->
      if Basic_gates.is_vdd b
      then 1
      else if Basic_gates.is_gnd b
      then 0
      else raise_s [%message "[to_constant]"])
    |> Constant.of_bit_list
  ;;

  let concat_msb l = List.concat l

  let select s h l =
    let rec sel b i =
      match b with
      | [] -> []
      | hd :: tl ->
        if i > h then [] else if i >= l then hd :: sel tl (i + 1) else sel tl (i + 1)
    in
    List.rev (sel (List.rev s) 0)
  ;;

  let ( &: ) = List.map2_exn ~f:Basic_gates.( &: )
  let ( |: ) = List.map2_exn ~f:Basic_gates.( |: )
  let ( ^: ) = List.map2_exn ~f:Basic_gates.( ^: )
  let ( ~: ) = List.map ~f:Basic_gates.( ~: )
  let to_string b = Sexp.to_string_hum (sexp_of_t b)
  let ( -- ) a _ = a
end

include Hardcaml.Comb.Make (Hardcaml.Comb.Make_primitives (Gates))

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
