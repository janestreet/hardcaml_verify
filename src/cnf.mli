(** Data structure for creating CNF formulae.

    Literals are mapped to integer indexes internally so they can be easily converted to
    DIMACs format for input to a SAT solver, and a model constructed from the output. *)

open Base

(** A literal is an input bit to the CNF. They are constructed with the [vector] and [bit]
    functions, negated with [(~:)] and managed as a group within a [Disjunction.t]. *)
module Literal : sig
  type t [@@deriving sexp_of]

  val to_string : t -> string
  val of_labels : Label.t array -> t array
  val create : ?width:int -> ?hidden:bool -> string -> t array
  val create1 : ?hidden:bool -> string -> t
end

(** A collection of literals which are OR'd together. *)
module Disjunction : sig
  type t [@@deriving sexp_of]

  val create : unit -> t
  val add : t -> Literal.t -> t
  val of_list : Literal.t list -> t
  val fold : t -> init:'a -> f:('a -> Literal.t -> 'a) -> 'a
  val iter : t -> f:(Literal.t -> unit) -> unit
end

(** A collection of disjunctions which are AND'd together. *)
module Conjunction : sig
  type t [@@deriving sexp_of]

  val create : unit -> t
  val add : t -> Disjunction.t -> t
  val of_list : Disjunction.t list -> t
  val concat : t list -> t
end

type t [@@deriving sexp_of]

(** Not of a literal. *)
val ( ~: ) : Literal.t -> Literal.t

(** Create CNF from a [Conjunction.t]. *)
val create : Conjunction.t -> t

(** Fold over each disjunction in CNF *)
val fold : t -> init:'a -> f:('a -> Disjunction.t -> 'a) -> 'a

(** Iter over each disjunction in CNF *)
val iter : t -> f:(Disjunction.t -> unit) -> unit

(** Get an integer representing the literal. It is negative if the literal is negated.
    Returns [None] if the literal is not in the CNF. *)
val to_int_literal : t -> Literal.t -> int option

(** Total number of variables in the CNF *)
val number_of_variables : t -> int

(** Total number of clauses in the CNF. *)
val number_of_clauses : t -> int

module type Model = sig
  type input [@@deriving sexp_of]

  val get : ?show_hidden:bool -> t -> int list Sat.t -> input list Sat.t
  val print : Stdio.Out_channel.t -> input list Sat.t Or_error.t -> unit
end

module Model_with_bits : sig
  type input =
    { label : Label.t
    ; value : char
    }
  [@@deriving sexp_of]

  include Model with type input := input
end

module Model_with_vectors : sig
  type input =
    { name : string
    ; value : string
    }
  [@@deriving sexp_of]

  include Model with type input := input
end
