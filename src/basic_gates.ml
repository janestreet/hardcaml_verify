open Base
module Uid = Uid.Int

module T = struct
  type t =
    | Vdd
    | Gnd
    | Var of
        { uid : Uid.t
        ; label : Label.t
        }
    | Not of
        { uid : Uid.t
        ; arg : t
        }
    | Or of
        { uid : Uid.t
        ; arg1 : t
        ; arg2 : t
        }
    | Xor of
        { uid : Uid.t
        ; arg1 : t
        ; arg2 : t
        }
    | And of
        { uid : Uid.t
        ; arg1 : t
        ; arg2 : t
        }
  [@@deriving compare ~localize, sexp]
end

include T
module%template Comparable = Comparable.Make [@mode local] (T)

let optimise_muxs = false
let constant_only = false

let to_char = function
  | Vdd -> '1'
  | Gnd -> '0'
  | c -> raise_s [%message "[Basic_gates.to_char] not a constant" (c : t)]
;;

let of_char = function
  | '1' -> Vdd
  | '0' -> Gnd
  | c -> raise_s [%message "[Basic_gates.of_char] invalid char" (c : char)]
;;

let new_uid = Staged.unstage (Uid.create 0)
let gnd_uid = new_uid ()
let vdd_uid = new_uid ()

let uid = function
  | Gnd -> gnd_uid
  | Vdd -> vdd_uid
  | Var { uid; label = _ }
  | Not { uid; arg = _ }
  | Or { uid; arg1 = _; arg2 = _ }
  | Xor { uid; arg1 = _; arg2 = _ }
  | And { uid; arg1 = _; arg2 = _ } -> uid
;;

let vdd = Vdd
let gnd = Gnd

let is_vdd = function
  | Vdd -> true
  | _ -> false
;;

let is_gnd = function
  | Gnd -> true
  | _ -> false
;;

let var label = Var { uid = new_uid (); label }

let ( ~: ) arg =
  match arg with
  | Vdd -> Gnd
  | Gnd -> Vdd
  | Not x -> x.arg
  | _ -> Not { uid = new_uid (); arg }
;;

let ( |: ) arg1 arg2 =
  match arg1, arg2 with
  | Vdd, _ | _, Vdd -> Vdd
  | Gnd, _ -> arg2
  | _, Gnd -> arg1
  | _ -> Or { uid = new_uid (); arg1; arg2 }
;;

let ( &: ) arg1 arg2 =
  match arg1, arg2 with
  | Gnd, _ | _, Gnd -> Gnd
  | Vdd, _ -> arg2
  | _, Vdd -> arg1
  | _ -> And { uid = new_uid (); arg1; arg2 }
;;

let ( ^: ) arg1 arg2 =
  match arg1, arg2 with
  | _, Gnd -> arg1
  | Gnd, _ -> arg2
  | _, Vdd -> ~:arg1
  | Vdd, _ -> ~:arg2
  | _ -> Xor { uid = new_uid (); arg1; arg2 }
;;

let cofactor ~var v ~f =
  let n =
    match var with
    | Var { uid; label = _ } -> uid
    | _ -> raise_s [%message "must take cofactor wrt a variable" (var : t)]
  in
  let v =
    match v with
    | Vdd -> Vdd
    | Gnd -> Gnd
    | _ -> raise_s [%message "neither +ve nor -ve cofactor"]
  in
  let rec fn b =
    match b with
    | Var { uid; label = _ } when Uid.compare n uid = 0 -> v
    | Var v -> Var v
    | Vdd -> Vdd
    | Gnd -> Gnd
    | And { uid = _; arg1; arg2 } -> fn arg1 &: fn arg2
    | Or { uid = _; arg1; arg2 } -> fn arg1 |: fn arg2
    | Xor { uid = _; arg1; arg2 } -> fn arg1 ^: fn arg2
    | Not { uid = _; arg } -> ~:(fn arg)
  in
  fn f
;;

let shannon_expansion var ~f =
  let p = cofactor ~var Vdd ~f in
  let n = cofactor ~var Gnd ~f in
  var &: p |: (~:var &: n)
;;

let difference var ~f = cofactor ~var Vdd ~f ^: cofactor ~var Gnd ~f
let forall var ~f = cofactor ~var Vdd ~f &: cofactor ~var Gnd ~f
let exists var ~f = cofactor ~var Vdd ~f |: cofactor ~var Gnd ~f

let deps = function
  | And { uid = _; arg1; arg2 } -> [ arg1; arg2 ]
  | Or { uid = _; arg1; arg2 } -> [ arg1; arg2 ]
  | Xor { uid = _; arg1; arg2 } -> [ arg1; arg2 ]
  | Not { uid = _; arg } -> [ arg ]
  | Vdd | Gnd | Var _ -> []
;;

let depth_first_search t ~init ~f =
  let rec search1 signal ~set acc =
    if Set.mem set (uid signal)
    then acc, set
    else (
      let set = Set.add set (uid signal) in
      let acc, set = search (deps signal) acc ~set in
      let acc = f acc signal in
      acc, set)
  and search t acc ~set =
    List.fold t ~init:(acc, set) ~f:(fun (arg, set) s -> search1 s ~set arg)
  in
  fst (search t init ~set:(Set.empty (module Uid)))
;;

module Tseitin = Tseitin.Make (struct
    type t = Cnf.Literal.t

    let ( ~: ) = Cnf.( ~: )
  end)

let cnf ?(show_hidden = false) fn =
  let _map, cnf, final_term =
    depth_first_search
      fn
      ~init:(Map.empty (module Uid), [], None)
      ~f:(fun (map, cnf, _) fn ->
        let find f =
          match Map.find map (uid f) with
          | None -> raise_s [%message "Unable to lookup tseitin input"]
          | Some x -> x
        in
        let to_conjunction l =
          List.map l ~f:Cnf.Disjunction.of_list |> Cnf.Conjunction.of_list
        in
        let create_hidden = Cnf.Literal.create1 ~hidden:(not show_hidden) in
        match fn with
        | Vdd ->
          let input = create_hidden "__vdd_in" in
          let cnf' = Tseitin.btrue input |> to_conjunction in
          Map.add_exn map ~key:(uid fn) ~data:input, cnf' :: cnf, Some input
        | Gnd ->
          let input = create_hidden "__gnd_in" in
          let cnf' = Tseitin.bfalse input |> to_conjunction in
          Map.add_exn map ~key:(uid fn) ~data:input, cnf' :: cnf, Some input
        | Var { uid; label } ->
          let input = Cnf.Literal.of_labels [| label |] in
          (* I think this is safe - it should only be used if the only thing in the
             circuit is a single literal - and that would produce something like [a&a]
             which is fine. Seems to be ok in the tests. *)
          let final_term = Some input.(0) in
          Map.add_exn map ~key:uid ~data:input.(0), cnf, final_term
        | And { uid; arg1; arg2 } ->
          let arg1, arg2 = find arg1, find arg2 in
          let input = create_hidden "__and_in" in
          let cnf' = Tseitin.band input [ arg1; arg2 ] |> to_conjunction in
          Map.add_exn map ~key:uid ~data:input, cnf' :: cnf, Some input
        | Or { uid; arg1; arg2 } ->
          let arg1, arg2 = find arg1, find arg2 in
          let input = create_hidden "__or_in" in
          let cnf' = Tseitin.bor input [ arg1; arg2 ] |> to_conjunction in
          Map.add_exn map ~key:uid ~data:input, cnf' :: cnf, Some input
        | Xor { uid; arg1; arg2 } ->
          let arg1, arg2 = find arg1, find arg2 in
          let input = create_hidden "__xor_in" in
          let cnf' = Tseitin.bxor input arg1 arg2 |> to_conjunction in
          Map.add_exn map ~key:uid ~data:input, cnf' :: cnf, Some input
        | Not { uid; arg } ->
          let arg = find arg in
          let input = create_hidden "__not_in" in
          let cnf' = Tseitin.bnot input arg |> to_conjunction in
          Map.add_exn map ~key:uid ~data:input, cnf' :: cnf, Some input)
  in
  let final_term =
    match final_term with
    | None ->
      raise_s [%message "Cannot convert circuit with tseitin transmformation (no gates?)"]
    | Some final_term ->
      Cnf.Conjunction.of_list [ Cnf.Disjunction.of_list [ final_term ] ]
  in
  Cnf.Conjunction.concat (final_term :: cnf) |> Cnf.create
;;

include Comparable
