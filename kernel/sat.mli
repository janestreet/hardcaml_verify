type 'model t =
  | Sat of 'model
  | Unsat
[@@deriving sexp_of]
