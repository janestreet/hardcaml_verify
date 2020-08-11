open Base
open Hardcaml

module Make (Comb : Comb.S) = struct
  open Comb

  type nonrec t =
    { no_bit_set : t
    ; one_bit_set : t
    ; many_bits_set : t
    }

  let create vec =
    let any_bit_set, many_bits_set =
      List.fold (bits_msb vec) ~init:(gnd, gnd) ~f:(fun (any_bit_set, overflow) bit ->
        any_bit_set |: bit, overflow |: (any_bit_set &: bit))
    in
    let no_bit_set = ~:any_bit_set in
    let one_bit_set = any_bit_set &: ~:many_bits_set in
    { no_bit_set; one_bit_set; many_bits_set }
  ;;
end
