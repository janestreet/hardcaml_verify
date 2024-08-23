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
  ; atomic_propositions_map : Signal.t Map.M(Signal.Uid).t
  }
[@@deriving sexp_of, fields ~getters]

let create ?(outputs = []) ~name properties =
  let module Signal_compare = struct
    module T = struct
      type t = Signal.t [@@deriving sexp_of]

      let compare a b = Uid.compare (uid a) (uid b)
    end

    include T
    include Comparable.Make (T)
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
      (match Map.of_alist (module Signal.Uid) atomic_propositions with
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

let write chan { circuit = circ; properties = props; atomic_propositions_map } =
  let os = Stdio.Out_channel.output_string chan in
  let inputs, outputs = Circuit.inputs circ, Circuit.outputs circ in
  let is_internal s =
    (not (Circuit.is_input circ s))
    && (not (Circuit.is_output circ s))
    && not (Signal.equal s empty)
  in
  let internal_signals = Signal_graph.filter (Circuit.signal_graph circ) ~f:is_internal in
  let internal_signals, registers =
    List.partition_tf internal_signals ~f:(function
      | Reg _ -> false
      | _ -> true)
  in
  let name s =
    match List.hd (names s) with
    | Some x -> x
    | None -> "_" ^ Signal.Uid.to_string (uid s)
  in
  let word_spec s = "unsigned word [" ^ Int.to_string (width s) ^ "]" in
  let const' w s =
    "0h"
    ^ Int.to_string w
    ^ "_"
    ^ (Constant.of_binary_string s |> Constant.to_hex_string ~signedness:Unsigned)
  in
  let const s = const' (width s) (Type.const_value s |> Bits.to_bstr) in
  let consti w i = const' w (Constant.of_int ~width:w i |> Constant.to_binary_string) in
  let sel s h l = name s ^ "[" ^ Int.to_string h ^ ":" ^ Int.to_string l ^ "]" in
  let define s x =
    os "DEFINE ";
    os (name s);
    os " := ";
    os x;
    os ";\n"
  in
  os "MODULE main\n";
  os "\n-- inputs\n";
  List.iter inputs ~f:(fun s -> os ("VAR " ^ name s ^ " : " ^ word_spec s ^ ";\n"));
  os "\n-- registers\n";
  List.iter registers ~f:(fun s -> os ("VAR " ^ name s ^ " : " ^ word_spec s ^ ";\n"));
  (* os ("-- memories\n"); *)
  (* simple naming *)
  os "\n-- combinatorial logic\n";
  let define s =
    match s with
    | Type.Empty -> failwith "NuSMV - unexpected empty signal"
    | Inst _ -> failwith "NuSMV - instantiation not supported"
    | Reg _ | Multiport_mem _ | Mem_read_port _ ->
      failwith "NuSMV error - reg or mem not expected here"
    | Const _ -> define s (const s)
    | Wire { driver; _ } -> define s (name !driver)
    | Select { arg; high; low; _ } -> define s (sel arg high low)
    | Not { arg; _ } ->
      let not_ _ = "!" ^ name arg in
      define s (not_ s)
    | Cat { args; _ } ->
      let cat = String.concat ~sep:"::" (List.map args ~f:name) in
      define s cat
    | Mux { select; cases; _ } ->
      let mux _ =
        os "DEFINE ";
        os (name s);
        os " := \n";
        os "  case\n";
        let nsel = name select in
        let rec f n = function
          | [] -> ()
          | [ a ] ->
            os "    TRUE: ";
            os (name a);
            os ";\n"
          | h :: t ->
            let w = width select in
            os "    ";
            os nsel;
            os "=";
            os (consti w n);
            os ": ";
            os (name h);
            os ";\n";
            f (n + 1) t
        in
        f 0 cases;
        os "  esac;\n"
      in
      mux s
    | Op2 { op; arg_a; arg_b; _ } ->
      let op2 op _ = name arg_a ^ op ^ name arg_b in
      let wrap s t = s ^ "(" ^ t ^ ")" in
      let signed, unsigned = wrap "signed", wrap "unsigned" in
      let extend n s = wrap "extend" (s ^ ", " ^ Int.to_string n) in
      let _, word1 = wrap "bool", wrap "word1" in
      let mop2 sgn op _ =
        let a, b = arg_a, arg_b in
        let w = width a + width b in
        let ewa, ewb = w - width a, w - width b in
        let signed, unsigned =
          (if sgn then signed else fun s -> s), if sgn then unsigned else fun s -> s
        in
        let arg w a = unsigned @@ extend w @@ signed @@ name a in
        arg ewa a ^ op ^ arg ewb b
      in
      let comp op s = word1 (op2 op s) in
      (match op with
       | Signal_add -> define s (op2 " + " s)
       | Signal_sub -> define s (op2 " - " s)
       | Signal_mulu -> define s (mop2 false " * " s)
       | Signal_muls -> define s (mop2 true " * " s)
       | Signal_and -> define s (op2 " & " s)
       | Signal_or -> define s (op2 " | " s)
       | Signal_xor -> define s (op2 " xor " s)
       | Signal_eq -> define s (comp " = " s)
       | Signal_lt -> define s (comp " < " s))
  in
  List.iter internal_signals ~f:define;
  os "\n-- register updates\n";
  List.iter registers ~f:(fun s ->
    match s with
    | Reg { register = r; d = din; _ } ->
      let next s =
        let mux2 s t f = "(bool(" ^ s ^ ")?" ^ t ^ ":" ^ f ^ ")" in
        let mux2_enable s t f =
          if Signal.is_empty s || Signal.is_vdd s
          then t
          else if Signal.is_gnd s
          then f
          else mux2 (name s) t f
        in
        let mux2_clear s t f =
          if Signal.is_vdd s
          then t
          else if Signal.is_empty s || Signal.is_gnd s
          then f
          else mux2 (name s) t f
        in
        let mux2_reset s (e : Edge.t) t f =
          if Signal.is_empty s
          then f
          else (
            match e with
            | Rising -> mux2 (name s) t f
            | Falling -> mux2 (name s) f t)
        in
        let nxt = mux2_enable r.enable (name din) (name s) in
        let nxt = mux2_clear r.spec.clear (name r.clear_to) nxt in
        let nxt = mux2_reset r.spec.reset r.spec.reset_edge (name r.reset_to) nxt in
        nxt
      in
      let init s =
        if Signal.is_empty r.spec.reset
        then
          if Signal.is_empty r.reset_to
          then consti (width s) 0 (* default to zero *)
          else const r.reset_to (* treat as a default value *)
        else const r.reset_to
      in
      os ("ASSIGN init(" ^ name s ^ ") := " ^ init s ^ ";\n");
      os ("ASSIGN next(" ^ name s ^ ") := " ^ next s ^ ";\n")
    | _ -> failwith "NuSMV - expecting a register");
  os "\n-- outputs\n";
  List.iter outputs ~f:define;
  os "\n-- SPECS\n";
  List.iter props ~f:(fun spec ->
    let rewrite s =
      match Map.find atomic_propositions_map (Signal.uid s) with
      | None -> raise_s [%message "failed to rewrite atomic proposition"]
      | Some s -> s
    in
    match spec with
    | CTL prop ->
      os
        ("CTLSPEC "
         ^ Property.CTL.(to_string (map_atomic_propositions prop ~f:rewrite))
         ^ ";\n")
    | LTL prop ->
      os
        ("LTLSPEC "
         ^ Property.LTL.(to_string (map_atomic_propositions prop ~f:rewrite))
         ^ ";\n"))
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

let nusmv_path = Config.nusmv

let run (t : t) =
  let tmp_file = Stdlib.Filename.temp_file "hardcaml_verify_nusmv" "txt" in
  let oc = Stdio.Out_channel.create tmp_file in
  write oc t;
  Stdio.Out_channel.close oc;
  let command =
    [ nusmv_path
    ; (* [-quiet] is a secret command line argument that suppresses the initial
         banner's printing. *)
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
