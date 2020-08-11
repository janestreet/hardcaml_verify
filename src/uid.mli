open Base

module type S = sig
  type t [@@deriving sexp_of]

  include Comparable.S with type t := t
  include Stringable.S with type t := t

  val create : int -> (unit -> t) Staged.t
end

(** 63 bit UIDs backed by [Int.t]s. *)
module Int : S
