open Base
module Uid = Uid.Int

module T = struct
  type t =
    { name : string
    ; bit_pos : int
    ; uid : Uid.t
    ; hidden : bool
    }
  [@@deriving fields ~getters, sexp]

  let to_string t =
    String.concat ~sep:"/" [ t.name; Int.to_string t.bit_pos; Uid.to_string t.uid ]
    ^ if t.hidden then "?" else ""
  ;;

  let%template compare (a @ m) (b @ m) =
    let uid = Uid.compare a.uid b.uid in
    if uid <> 0 then uid else Int.compare a.bit_pos b.bit_pos
  [@@mode m = (local, global)]
  ;;

  module Compact_sexp : sig
    type s [@@deriving sexp]

    val to_t : s -> t
    val of_t : t -> s
  end = struct
    type s = string * int * Uid.t * bool [@@deriving sexp]

    let of_t t = t.name, t.bit_pos, t.uid, t.hidden
    let to_t (name, bit_pos, uid, hidden) = { name; bit_pos; uid; hidden }
  end

  let sexp_of_t t = Compact_sexp.(sexp_of_s (of_t t))
  let t_of_sexp t = Compact_sexp.(to_t (s_of_sexp t))
end

include T

let new_uid = Staged.unstage (Uid.create 1)

let create ?(width = 1) ?(hidden = false) name =
  assert (width > 0);
  let uid = new_uid () in
  Array.init width ~f:(fun bit_pos -> { name; bit_pos; uid; hidden })
;;

let create1 ?hidden name = (create ?hidden name).(0)

include%template Comparable.Make [@mode local] (T)
