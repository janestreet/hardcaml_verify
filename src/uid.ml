open Base

module type S = sig
  type t : immediate [@@deriving sexp]

  include%template Comparable.S [@mode local] with type t := t

  include Stringable.S with type t := t

  val create : int -> (unit -> t) Staged.t
end

module Int = struct
  include Int

  let create starts_at =
    let uid = ref starts_at in
    Staged.stage (fun () ->
      let ret = !uid in
      Int.incr uid;
      ret)
  ;;
end
