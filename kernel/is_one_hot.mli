(** Computes information about the one-hotness of a vector. In addition it can compute if
    no bits are set or more than 1 bit is set.

    In actual hardware using [popcount] might be better as it can be formulated as a tree
    with log depth. This implementation has depth O(width vector) but is small and simple.

    It's primary purpose is as an efficient check for proving SAT properties. *)

open Hardcaml

module Make (Comb : Comb.S) : sig
  type nonrec t =
    { no_bit_set : Comb.t
    ; one_bit_set : Comb.t
    ; many_bits_set : Comb.t
    }

  val create : Comb.t -> t
end
