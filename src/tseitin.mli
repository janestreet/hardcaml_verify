open Base

module type S = sig
  type t

  val ( ~: ) : t -> t
end

(** Conversion functions from boolean gates to Tseitin form. The first argument to each
    function is the newly introduced sat literal for this gate, which should be referenced
    by its fanouts. The return value is the corresponding CNF. *)
module Make (B : S) : sig
  open B

  (** constant false *)
  val bfalse : t -> t list list

  (** constant true *)
  val btrue : t -> t list list

  (** not *)
  val bnot : t -> t -> t list list

  (** wire (copy input to output) *)
  val bwire : t -> t -> t list list

  (** n-input not-or *)
  val bnor : t -> t list -> t list list

  (** n-input or *)
  val bor : t -> t list -> t list list

  (** n-input not-and *)
  val bnand : t -> t list -> t list list

  (** n-input and *)
  val band : t -> t list -> t list list

  (** 2-input xor *)
  val bxor : t -> t -> t -> t list list
end
