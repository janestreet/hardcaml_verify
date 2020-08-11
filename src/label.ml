open Base
module Uid = Uid.Int

module T = struct
  type t =
    { name : string
    ; bit_pos : int
    ; uid : Uid.t
    ; hidden : bool
    }
  [@@deriving fields]

  let to_string t =
    String.concat ~sep:"/" [ t.name; Int.to_string t.bit_pos; Uid.to_string t.uid ]
    ^ if t.hidden then "?" else ""
  ;;

  let compare a b =
    let uid = Uid.compare a.uid b.uid in
    if uid <> 0 then uid else Int.compare a.bit_pos b.bit_pos
  ;;

  let sexp_of_t t = sexp_of_string (to_string t)
end

include T

let new_uid = Staged.unstage (Uid.create 1)

let create ?(width = 1) ?(hidden = false) name =
  assert (width > 0);
  let uid = new_uid () in
  Array.init width ~f:(fun bit_pos -> { name; bit_pos; uid; hidden })
;;

let create1 ?hidden name = (create ?hidden name).(0)

include Comparable.Make (T)
