open Base
open Hardcaml
open Signal

type property =
  | LTL of Property.LTL.path
  | CTL of Property.CTL.state
[@@deriving sexp_of]

type t =
  { circuit : Circuit.t
  ; properties : property list
  ; atomic_propositions_map : Signal.t Map.M(Signal.Type.Uid).t
  }
[@@deriving sexp_of, fields ~getters]

let create ?(outputs = []) ~name properties =
  let module Signal_compare = struct
    module T = struct
      type t = Signal.t [@@deriving sexp_of]

      let%template compare (a @ m) (b @ m) =
        (Signal.Type.Uid.compare [@mode local])
          ((uid [@mode local]) a)
          ((uid [@mode local]) b) [@nontail]
      [@@mode m = (local, global)]
      ;;
    end

    include T

    include%template Comparable.Make [@mode local] (T)
  end
  in
  let atomic_propositions =
    List.fold
      properties
      ~init:(Set.empty (module Signal_compare))
      ~f:(fun set prop ->
        let ap =
          match prop with
          | LTL prop -> Property.LTL.atomic_propositions prop
          | CTL prop -> Property.CTL.atomic_propositions prop
        in
        List.fold_left ap ~init:set ~f:(fun set ap -> Set.add set ap))
  in
  let atomic_propositions =
    let count = ref 0 in
    let prop_name s =
      "__ap_"
      ^
      match Signal.names s with
      | name :: _ -> name
      | [] ->
        Int.incr count;
        Int.to_string !count
    in
    Set.elements atomic_propositions
    |> List.map ~f:(fun ap -> Signal.uid ap, Signal.output (prop_name ap) ap)
  in
  { circuit =
      Circuit.create_exn
        ~name
        (List.concat [ List.map atomic_propositions ~f:snd; outputs ])
  ; properties
  ; atomic_propositions_map =
      (match Map.of_alist (module Signal.Type.Uid) atomic_propositions with
       | `Duplicate_key _ ->
         raise_s [%message "Failed to construct atomic propositions output map"]
       | `Ok m -> m)
  }
;;

let of_circuit ?(outputs = false) circuit properties =
  create
    ~outputs:(if outputs then Circuit.outputs circuit else [])
    ~name:(Circuit.name circuit)
    properties
;;

let to_rope { circuit = circ; properties = props; atomic_propositions_map } =
  let inputs, outputs = Circuit.inputs circ, Circuit.outputs circ in
  let is_internal s =
    (not (Circuit.is_input circ s))
    && (not (Circuit.is_output circ s))
    && not (Signal.equal s empty)
  in
  let internal_signals =
    Signal_graph.filter
      ~deps:(module Signal_graph.Deps_without_case_matches)
      (Circuit.signal_graph circ)
      ~f:is_internal
  in
  let internal_signals, registers =
    List.partition_tf internal_signals ~f:(function
      | Reg _ -> false
      | _ -> true)
  in
  let name s =
    match List.hd (names s) with
    | Some x -> [%rope "%{x#String}"]
    | None -> [%rope "_%{(uid s)#Signal.Type.Uid}"]
  in
  let word_spec s = [%rope "unsigned word [%{(width s)#Int}]"] in
  let const_string_of_const const =
    let width = Constant.width const in
    let hex = Constant.to_hex_string ~signedness:Unsigned const in
    [%rope "0h%{width#Int}_%{hex#String}"]
  in
  let const_string_of_bits bits = const_string_of_const (Bits.to_constant bits) in
  let const_string_of_signal signal = const_string_of_const (Signal.to_constant signal) in
  let const_string_of_int ~width i = const_string_of_bits (Bits.of_int_trunc ~width i) in
  let sel s h l = [%rope "%{name s}[%{h#Int}:%{l#Int}]"] in
  let define s x = [%rope "DEFINE %{name s} := %{x};\n"] in
  let output_cases dst select cases =
    let select = name select in
    let rec f n = function
      | [] -> Rope.empty
      | `Default value :: tl -> [%rope "    TRUE: %{name value};\n%{f (n+1) tl}"]
      | `Match (match_with, value) :: tl ->
        [%rope "    %{select}=%{match_with}: %{name value};\n%{f (n+1) tl}"]
    in
    [%rope "DEFINE %{name dst} := \n  case\n%{f 0 cases}  esac;\n"]
  in
  let comb s =
    match s with
    | Type.Empty -> raise_s [%message "NuSMV - unexpected empty signal"]
    | Wire { driver = None; _ } -> raise_s [%message "NuSMV - unexpected undriven wire"]
    | Inst _ -> raise_s [%message "NuSMV - instantiation not supported"]
    | Reg _ | Multiport_mem _ | Mem_read_port _ ->
      raise_s [%message "NuSMV error - reg or mem not expected here"]
    | Const _ -> define s (const_string_of_signal s)
    | Wire { driver = Some driver; _ } -> define s (name driver)
    | Select { arg; high; low; _ } -> define s (sel arg high low)
    | Not { arg; _ } ->
      let not_ _ = [%rope "!%{name arg}"] in
      define s (not_ s)
    | Cat { args; _ } ->
      let cat = Rope.concat ~sep:[%rope "::"] (List.map args ~f:name) in
      define s cat
    | Mux { select; cases; _ } ->
      let num_cases = List.length cases in
      output_cases
        s
        select
        (List.mapi cases ~f:(fun idx case ->
           if idx = num_cases - 1
           then `Default case
           else `Match (const_string_of_int ~width:(width select) idx, case)))
    | Cases { select; cases; default; _ } ->
      output_cases
        s
        select
        (List.map cases ~f:(fun (match_with, value) ->
           `Match (const_string_of_signal match_with, value))
         @ [ `Default default ])
    | Op2 { op; arg_a; arg_b; _ } ->
      let op2 op = Rope.concat [ name arg_a; Rope.of_string op; name arg_b ] in
      let wrap s t = [%rope "%{s#String}(%{t})"] in
      let signed, unsigned = wrap "signed", wrap "unsigned" in
      let extend n s = wrap "extend" [%rope "%{s}, %{n#Int}"] in
      let _, word1 = wrap "bool", wrap "word1" in
      let mop2 sgn op =
        let a, b = arg_a, arg_b in
        let w = width a + width b in
        let ewa, ewb = w - width a, w - width b in
        let signed, unsigned =
          (if sgn then signed else fun s -> s), if sgn then unsigned else fun s -> s
        in
        let arg w a = unsigned @@ extend w @@ signed @@ name a in
        Rope.concat [ arg ewa a; Rope.of_string op; arg ewb b ]
      in
      let comp op = word1 (op2 op) in
      (match op with
       | Add -> define s (op2 " + ")
       | Sub -> define s (op2 " - ")
       | Mulu -> define s (mop2 false " * ")
       | Muls -> define s (mop2 true " * ")
       | And -> define s (op2 " & ")
       | Or -> define s (op2 " | ")
       | Xor -> define s (op2 " xor ")
       | Eq -> define s (comp " = ")
       | Lt -> define s (comp " < "))
  in
  let register_update (current : Signal.t) =
    match current with
    | Reg { register; d; _ } ->
      let next =
        let mux2 sel on_true on_false = [%rope "(bool(%{sel})?%{on_true}:%{on_false})"] in
        let nxt =
          let d = name d in
          Option.value_map register.enable ~default:d ~f:(fun enable ->
            mux2 (name enable) d (name current))
        in
        let nxt =
          Option.value_map register.clear ~default:nxt ~f:(fun { clear; clear_to } ->
            mux2 (name clear) (name clear_to) nxt)
        in
        let nxt =
          Option.value_map
            register.reset
            ~default:nxt
            ~f:(fun { reset; reset_edge; reset_to } ->
              match reset_edge with
              | Rising -> mux2 (name reset) (name reset_to) nxt
              | Falling -> mux2 (name reset) nxt (name reset_to))
        in
        nxt
      in
      let init =
        (* Choose

           - reset value
           - initial value
           - or zeros

           in that order for the initial value of the register.
        *)
        let default =
          Option.value_map
            register.initialize_to
            ~default:(const_string_of_int ~width:(width current) 0)
            ~f:(fun initial -> const_string_of_bits initial)
        in
        Option.value_map
          register.reset
          ~default
          ~f:(fun { reset = _; reset_edge = _; reset_to } ->
            const_string_of_signal reset_to)
      in
      Rope.concat
        [ [%rope "ASSIGN init(%{name current}) := %{init};\n"]
        ; [%rope "ASSIGN next(%{name current}) := %{next};\n"]
        ]
    | _ -> raise_s [%message "NuSMV - expecting a register"]
  in
  let prop spec =
    let rewrite s =
      match Map.find atomic_propositions_map (Signal.uid s) with
      | None -> raise_s [%message "failed to rewrite atomic proposition"]
      | Some s -> s
    in
    match spec with
    | CTL prop ->
      let module CTL = Property.CTL in
      [%rope "CTLSPEC %{CTL.map_atomic_propositions prop ~f:rewrite#CTL};\n"]
    | LTL prop ->
      let module LTL = Property.LTL in
      [%rope "LTLSPEC %{LTL.map_atomic_propositions prop ~f:rewrite#LTL};\n"]
  in
  let inputs =
    List.map inputs ~f:(fun s -> [%rope "VAR %{ name s } : %{ word_spec s };\n"])
    |> Rope.concat
  in
  let register_definitions =
    List.map registers ~f:(fun s -> [%rope "VAR %{name s} : %{word_spec s};\n"])
    |> Rope.concat
  in
  let comb_logic = List.map internal_signals ~f:comb |> Rope.concat in
  let register_updates = List.map registers ~f:register_update |> Rope.concat in
  let outputs = List.map outputs ~f:comb |> Rope.concat in
  let props = List.map props ~f:prop |> Rope.concat in
  [%rope
    {|MODULE main

-- inputs
%{inputs}
-- registers
%{register_definitions}
-- combinatorial logic
%{comb_logic}
-- register updates
%{register_updates}
-- outputs
%{outputs}
-- SPECS
%{props}
|}]
;;

module Counter_example_trace = struct
  type t = { states : (string * Bits.t) list list } [@@deriving sexp_of]

  let to_trace t = t.states
end

module Proof_result = struct
  type t =
    | Tautology
    | Exists_counter_example of Counter_example_trace.t
  [@@deriving sexp_of]
end

module Output_parser = struct
  let assignment_re = Re.Perl.(re "    ([\\w]+) = ((?:-\\s+)?\\S+)\\s*" |> compile)
  let specification_re = Re.Perl.(re "-- specification .* is (true|false)\\s*" |> compile)

  let word_constant_re =
    Re.Perl.(re "^((?:-\\s+)?)0([us]?)([bodh])(\\d*)_([0-9a-fA-F]+)$" |> compile)
  ;;

  let re_exec_exn re str =
    try Re.exec re str with
    | e ->
      raise_s [%message "failed to parse regular expression" (str : string) (e : exn)]
  ;;

  let parse_word_constant word_constant =
    let matches = re_exec_exn word_constant_re word_constant in
    let is_negated = String.equal (Re.Group.get matches 1) "" |> not in
    let _is_signed = String.equal (Re.Group.get matches 2) "s" in
    let base = Re.Group.get matches 3 in
    let width_str = Re.Group.get matches 4 in
    let value_str = Re.Group.get matches 5 in
    let bits_wrong_size =
      match base with
      | "b" -> Bits.of_bit_string value_str
      | "o" -> Bits.of_octal ~width:(String.length value_str * 3) value_str
      | "d" -> Bits.of_decimal_string ~width:(String.length value_str * 4) value_str
      | "h" -> Bits.of_hex ~width:(String.length value_str * 4) value_str
      | _ -> raise_s [%message "Unrecognised base" word_constant]
    in
    let bits_resized =
      match width_str, base with
      | "", "d" ->
        raise_s [%message "Decimal word constants must specify a size" word_constant]
      | "", _ -> bits_wrong_size
      | _, _ ->
        (* Check specified width can represent the value *)
        let specified_width = Int.of_string width_str in
        let num_leading_zeroes =
          Int.max 0 (Bits.width bits_wrong_size - specified_width)
        in
        let fits_within_size =
          if num_leading_zeroes = 0
          then true
          else (
            let leading_zeroes = Bits.sel_top bits_wrong_size ~width:num_leading_zeroes in
            Bits.(leading_zeroes ==:. 0) |> Bits.to_bool)
        in
        if fits_within_size
        then Bits.uresize bits_wrong_size ~width:(Int.of_string width_str)
        else
          raise_s
            [%message
              "Parsed word constant is wider than its specified width" word_constant]
    in
    if is_negated then Bits.negate bits_resized else bits_resized
  ;;

  let parse_one_state lines =
    let lines = List.drop lines 1 in
    let assign_lines, lines =
      List.split_while lines ~f:(String.is_prefix ~prefix:"    ")
    in
    let assignments =
      List.map assign_lines ~f:(fun line ->
        let matches = re_exec_exn assignment_re line in
        let var_name = Re.Group.get matches 1 in
        let word_constant = Re.Group.get matches 2 in
        let bits = parse_word_constant word_constant in
        var_name, bits)
    in
    assignments, lines
  ;;

  let rec parse_states ~acc:states = function
    | [] -> List.rev states
    | ls ->
      let state, ls' = parse_one_state ls in
      parse_states ~acc:(state :: states) ls'
  ;;

  let parse_counterexample lines =
    match lines with
    | hd :: tl ->
      let lines =
        if String.is_prefix hd ~prefix:"  -- Loop starts here" then tl else hd :: tl
      in
      let states = parse_states ~acc:[] lines in
      { Counter_example_trace.states }
    | _ -> raise_s [%message "Unexpected end of input" (lines : string list)]
  ;;

  let parse_one_proof lines =
    let outcome, lines =
      match lines with
      | spec_is_ :: lines ->
        let matches = re_exec_exn specification_re spec_is_ in
        let outcome = Bool.of_string (Re.Group.get matches 1) in
        outcome, lines
      | _ -> raise_s [%message "Unexpected end of input"]
    in
    match outcome, lines with
    | false, _as_demonstrated :: _trace_desc :: trace_type :: lines ->
      if String.is_prefix trace_type ~prefix:"Trace Type: Counterexample"
      then (
        let counter_lines, lines =
          List.split_while lines ~f:(String.is_prefix ~prefix:"  ")
        in
        let counter = parse_counterexample counter_lines in
        Proof_result.Exists_counter_example counter, lines)
      else raise_s [%message "Unsupported trace type" trace_type]
    | true, lines -> Proof_result.Tautology, lines
    | _ -> raise_s [%message "Unexpected end of input" (lines : string list)]
  ;;

  let parse =
    let rec loop ~acc = function
      | [] -> List.rev acc
      | lines ->
        let proof, lines = parse_one_proof lines in
        loop ~acc:(proof :: acc) lines
    in
    fun lines -> loop ~acc:[] lines
  ;;
end

let nusmv_path = Tools_config.nusmv

let run (t : t) =
  let tmp_file = Stdlib.Filename.temp_file "hardcaml_verify_nusmv" "txt" in
  let oc = Stdio.Out_channel.create tmp_file in
  let rope = to_rope t in
  Stdio.Out_channel.output_string oc (Rope.to_string rope);
  Stdio.Out_channel.close oc;
  let command =
    [ nusmv_path
    ; (* [-quiet] is a secret command line argument that suppresses the initial banner's
         printing. *)
      "-quiet"
    ; tmp_file
    ]
    |> String.concat ~sep:" "
  in
  let cmd_output = Unix.open_process_in command in
  let lines = Stdio.In_channel.input_lines cmd_output in
  Output_parser.parse lines
;;

module Circuit_properties = struct
  type ('i, 'o) t =
    { inputs : 'i
    ; outputs : 'o
    }
  [@@deriving fields ~getters]
end

module With_interface (I : Hardcaml.Interface.S) (O : Hardcaml.Interface.S) = struct
  type t =
    { inputs : Signal.t I.t
    ; outputs : Signal.t O.t
    ; circuit : Circuit.t
    }

  let name_exn signal =
    match Signal.names signal with
    | [ hd ] -> hd
    | _ -> assert false
  ;;

  let to_alist signals = List.map signals ~f:(fun s -> name_exn s, s)

  let create ~name create =
    let module C = Hardcaml.Circuit.With_interface (I) (O) in
    let circuit = C.create_exn ~name create in
    let inputs =
      I.Unsafe_assoc_by_port_name.of_alist (to_alist (Hardcaml.Circuit.inputs circuit))
    in
    let outputs =
      O.Unsafe_assoc_by_port_name.of_alist (to_alist (Hardcaml.Circuit.outputs circuit))
    in
    { inputs; outputs; circuit }
  ;;

  let ltl t =
    let p signal =
      Signal.bits_lsb signal |> List.map ~f:Property.LTL.p |> Array.of_list
    in
    { Circuit_properties.inputs = I.map t.inputs ~f:p; outputs = O.map t.outputs ~f:p }
  ;;

  let ctl t =
    let p signal =
      Signal.bits_lsb signal |> List.map ~f:Property.CTL.p |> Array.of_list
    in
    { Circuit_properties.inputs = I.map t.inputs ~f:p; outputs = O.map t.outputs ~f:p }
  ;;

  let create_specification (t : t) properties =
    of_circuit ~outputs:true t.circuit properties
  ;;
end
