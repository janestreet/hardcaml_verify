open Base

module type S = sig
  type t

  val ( ~: ) : t -> t
end

module Make (B : S) = struct
  open B

  let bfalse z = [ [ ~:z ] ]
  let btrue z = [ [ z ] ]
  let bnot z x = [ [ x; z ]; [ ~:x; ~:z ] ]
  let bwire z x = [ [ ~:z; x ]; [ z; ~:x ] ]

  let bnor z x =
    let sum = List.fold_right x ~init:[ z ] ~f:(fun x a -> x :: a) in
    List.fold_right x ~init:[ sum ] ~f:(fun x a -> [ ~:x; ~:z ] :: a)
  ;;

  let bor z x =
    let sum = List.fold_right x ~init:[ ~:z ] ~f:(fun x a -> x :: a) in
    List.fold_right x ~init:[ sum ] ~f:(fun x a -> [ ~:x; z ] :: a)
  ;;

  let bnand z x =
    let sum = List.fold_right x ~init:[ ~:z ] ~f:(fun x a -> ~:x :: a) in
    List.fold_right x ~init:[ sum ] ~f:(fun x a -> [ x; z ] :: a)
  ;;

  let band z x =
    let sum = List.fold_right x ~init:[ z ] ~f:(fun x a -> ~:x :: a) in
    List.fold_right x ~init:[ sum ] ~f:(fun x a -> [ x; ~:z ] :: a)
  ;;

  let bxor z a b = [ [ ~:z; ~:a; ~:b ]; [ ~:z; a; b ]; [ z; ~:a; b ]; [ z; a; ~:b ] ]
end
