open Base
open Hardcaml

type t = { states : (string * Bits.t) list list } [@@deriving sexp_of]

let of_states states = { states }
let to_states t = t.states
