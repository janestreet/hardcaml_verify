(** Labels represent named variables. They contain a [uid] (unique identifier) which is
    constructed when the label is created. The name is not used for comparison.

    We need to represent vectors, even though the core variable type is a single bit. As
    such labels also refer to their bit position. The pair [(uid,bit_pos)] is used for
    comparison in order to distinguish labels. *)

open Base
module Uid : Uid.S

type t [@@deriving compare ~localize, sexp]

val to_string : t -> string

include%template Comparable.S [@mode local] with type t := t

val create : ?width:int -> ?hidden:bool -> string -> t array
val create1 : ?hidden:bool -> string -> t
val uid : t -> Uid.t
val bit_pos : t -> int
val name : t -> string
val hidden : t -> bool
