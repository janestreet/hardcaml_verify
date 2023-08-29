open Base

module Literal = struct
  type t =
    | P of Label.t
    | N of Label.t
  [@@deriving sexp_of]

  let ( ~: ) = function
    | P i -> N i
    | N i -> P i
  ;;

  let get_input_bit = function
    | P i -> i
    | N i -> i
  ;;

  let to_string = function
    | P i -> Label.to_string i
    | N i -> "-" ^ Label.to_string i
  ;;

  let of_labels labels = Array.map labels ~f:(fun l -> P l)
  let create ?width ?hidden name = Label.create ?width ?hidden name |> of_labels
  let create1 ?hidden name = P (Label.create1 ?hidden name)
end

module Disjunction = struct
  type t = Literal.t list [@@deriving sexp_of]

  let create () = []
  let add t term = term :: t
  let of_list literal_terms = literal_terms

  let to_set t =
    List.fold
      t
      ~init:(Set.empty (module Label))
      ~f:(fun set i -> Set.add set (Literal.get_input_bit i))
  ;;

  let fold = List.fold
  let iter = List.iter
end

module Conjunction = struct
  type t = Disjunction.t list [@@deriving sexp_of]

  let create () = []
  let add t term = term :: t
  let of_list disjunctions = disjunctions

  let to_set t =
    List.fold
      t
      ~init:(Set.empty (module Label))
      ~f:(fun set d -> Set.union set (Disjunction.to_set d))
  ;;

  let concat = List.concat
end

type t =
  { input_bits : Set.M(Label).t
  ; input_map : Label.t Map.M(Int).t
  ; int_map : Int.t Map.M(Label).t
  ; conjunction : Conjunction.t
  ; number_of_variables : int
  ; number_of_clauses : int
  }
[@@deriving fields ~getters, sexp_of]

let ( ~: ) = Literal.( ~: )

let create conjunction =
  let input_bits = Conjunction.to_set conjunction in
  let input_map, int_map, max_index =
    Set.fold
      input_bits
      ~init:(Map.empty (module Int), Map.empty (module Label), 1)
      ~f:(fun (input_map, int_map, index) input_bit ->
        ( Map.add_exn input_map ~key:index ~data:input_bit
        , Map.add_exn int_map ~key:input_bit ~data:index
        , index + 1 ))
  in
  { input_bits
  ; input_map
  ; int_map
  ; conjunction
  ; number_of_variables = max_index - 1
  ; number_of_clauses = List.length conjunction
  }
;;

let fold t ~init ~f = List.fold t.conjunction ~init ~f
let iter t ~f = List.iter t.conjunction ~f

let to_int_literal t (literal : Literal.t) =
  match literal with
  | P bit -> Map.find t.int_map bit
  | N bit -> Option.map (Map.find t.int_map bit) ~f:(fun i -> -i)
;;

module type Model = sig
  type input [@@deriving sexp_of]

  val get : ?show_hidden:bool -> t -> int list Sat.t -> input list Sat.t
  val print : Stdio.Out_channel.t -> input list Sat.t Or_error.t -> unit
end

let qed =
  {|   ____    __________
  / __ \  / ____/ __ \
 / / / / / __/ / / / /
/ /_/ / / /___/ /_/ /
\___\_\/_____/_____/  |}
;;

module Model_with_bits = struct
  type input =
    { label : Label.t
    ; value : char
    }
  [@@deriving sexp_of]

  let get ?(show_hidden = false) cnf model =
    match model with
    | Sat.Unsat -> Sat.Unsat
    | Sat.Sat model ->
      let find_and_add map value =
        match Map.find cnf.input_map (Int.abs value) with
        | None -> map
        | Some input_bit ->
          Map.set map ~key:input_bit ~data:(if value < 0 then `n else `p)
      in
      let literals = List.fold model ~init:(Map.empty (module Label)) ~f:find_and_add in
      let input_bits = Set.to_list cnf.input_bits in
      let input_bits =
        if show_hidden
        then input_bits
        else List.filter input_bits ~f:(fun b -> not (Label.hidden b))
      in
      Sat
        (List.map input_bits ~f:(fun (label : Label.t) ->
           { label
           ; value =
               (match Map.find literals label with
                | None -> '-'
                | Some `p -> '1'
                | Some `n -> '0')
           })
         |> List.sort ~compare:(fun a b -> Label.compare a.label b.label))
  ;;

  let print out_chan (model : input list Sat.t Or_error.t) =
    let open Stdio.Out_channel in
    match model with
    | Error e -> fprintf out_chan "ERROR: %s" (Sexp.to_string_hum [%sexp (e : Error.t)])
    | Ok Unsat -> fprintf out_chan "%s\n" qed
    | Ok (Sat sat) ->
      List.iter sat ~f:(fun input ->
        fprintf out_chan "%s = '%c'\n" (Label.to_string input.label) input.value)
  ;;
end

module Model_with_vectors = struct
  type input =
    { name : string
    ; value : string
    }
  [@@deriving sexp_of]

  let get ?show_hidden cnf model =
    let model = Model_with_bits.get ?show_hidden cnf model in
    match model with
    | Sat.Unsat -> Sat.Unsat
    | Sat.Sat (model : Model_with_bits.input list) ->
      let models =
        List.group model ~break:(fun (a : Model_with_bits.input) b ->
          Label.Uid.compare (Label.uid a.label) (Label.uid b.label) <> 0)
      in
      Sat.Sat
        (List.map models ~f:(fun vector ->
           let width =
             1 + List.fold vector ~init:0 ~f:(fun a b -> max a (Label.bit_pos b.label))
           in
           let str = Bytes.init width ~f:(Fn.const '-') in
           List.iter vector ~f:(fun b -> Bytes.set str (Label.bit_pos b.label) b.value);
           let name =
             match List.hd vector with
             | None -> "?"
             | Some l -> Label.name l.label
           in
           let value = Bytes.to_string str |> String.rev in
           { name; value })
         |> List.sort ~compare:(fun { name = n1; _ } { name = n2; _ } ->
           String.compare n1 n2))
  ;;

  let print out_chan (model : input list Sat.t Or_error.t) =
    let open Stdio.Out_channel in
    match model with
    | Error e -> fprintf out_chan "ERROR: %s" (Sexp.to_string_hum [%sexp (e : Error.t)])
    | Ok Unsat -> fprintf out_chan "%s\n" qed
    | Ok (Sat sat) ->
      List.iter sat ~f:(fun input ->
        fprintf out_chan "%s = '%s'\n" input.name input.value)
  ;;
end
