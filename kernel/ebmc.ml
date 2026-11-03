open Base
open Hardcaml
open Stdio
module Filename = Stdlib.Filename

module Ebmc_output = struct
  open Jsonaf_kernel.Conv

  type var_state =
    { base_name : string
    ; display_name : string
    ; identifier : string
    ; lhs : string
    ; lhs_type : string
    ; mode : string
    ; state_var : bool
    ; value : string
    }
  [@@deriving of_jsonaf, sexp_of]

  type trace_info =
    { mode : string
    ; states : var_state list list
    }
  [@@deriving of_jsonaf, sexp_of]

  type property_status =
    { identifier : string
    ; status : string
    ; trace : trace_info option [@jsonaf.option]
    }
  [@@deriving of_jsonaf, sexp_of]

  type t = { properties : property_status list } [@@deriving of_jsonaf, sexp_of]
end

module Ebmc_result = struct
  type t =
    | Assumed
    | Proved
    | Proved_with_trace of Counter_example_trace.t
    | Refuted
    | Refuted_with_trace of Counter_example_trace.t
    | Failure of Sexp.t
  [@@deriving sexp_of]

  let get_trace (trace : Ebmc_output.trace_info) =
    let get_bits_from_state (state : Ebmc_output.var_state) =
      let width =
        (* Parse type strings of form "bool" or "[N-1:0]"*)
        match String.split_on_chars state.lhs_type ~on:[ ':'; '['; ']' ] with
        | [ "bool" ] -> 1
        | [ ""; bound; "0"; "" ] -> Int.of_string bound + 1
        | _ -> raise_s [%message "Could not parse type from trace" state.lhs_type]
      in
      let bits =
        (* Parse bit strings of form X, 'hX or W'bX *)
        match String.split state.value ~on:'\'' with
        | [ "" ] ->
          (* Sometimes we get an empty value when the state in question is the clock *)
          Bits.zero width
        | [ number ] -> Bits.of_int_trunc ~width (Int.of_string number)
        | [ ""; _ ] -> Bits.of_string (Int.to_string width ^ state.value)
        | [ _; _ ] -> Bits.of_string state.value
        | _ -> raise_s [%message "Could not parse value from trace" state.value]
      in
      state.base_name, bits
    in
    List.map ~f:(List.map ~f:get_bits_from_state) trace.states
    |> Counter_example_trace.of_states
  ;;

  let of_property_status ~circuit_name (property_status : Ebmc_output.property_status) =
    let trimmed_id =
      String.chop_prefix_exn
        ~prefix:[%string "Verilog::%{circuit_name}."]
        property_status.identifier
    in
    let failure =
      trimmed_id, Failure (Ebmc_output.sexp_of_property_status property_status)
    in
    match property_status.trace with
    | None ->
      if String.is_prefix property_status.status ~prefix:"PROVED"
      then trimmed_id, Proved
      else if String.is_prefix property_status.status ~prefix:"REFUTED"
      then trimmed_id, Refuted
      else if String.is_prefix property_status.status ~prefix:"ASSUMED"
      then trimmed_id, Assumed
      else failure
    | Some trace_info ->
      let trace = get_trace trace_info in
      if String.is_prefix property_status.status ~prefix:"PROVED"
      then trimmed_id, Proved_with_trace trace
      else if String.is_prefix property_status.status ~prefix:"REFUTED"
      then trimmed_id, Refuted_with_trace trace
      else if String.is_prefix property_status.status ~prefix:"ASSUMED"
      then trimmed_id, Assumed
      else failure
  ;;
end

let output_verilog
  ?database
  ?(verilog_preamble = "")
  ~(rtl_output_mode : [ `Full_hierarchy | `Top_level_and_blackboxes ])
  channel
  circuit
  =
  Out_channel.output_string channel verilog_preamble;
  let circuits = Rtl.create ?database Verilog [ circuit ] in
  (match rtl_output_mode with
   | `Full_hierarchy -> Rtl.full_hierarchy circuits
   | `Top_level_and_blackboxes -> Rtl.top_levels_and_blackboxes circuits)
  |> Rope.to_string
  |> Out_channel.output_string channel
;;

let quote_command args = String.concat ~sep:" " (List.map args ~f:Filename.quote)

let run_ebmc args =
  let command =
    quote_command (Hardcaml_tools_config.ebmc5 :: args) ^ " >/dev/null 2>/dev/null"
  in
  match Unix.system command with
  | WEXITED (0 | 10) -> ()
  | WEXITED exit_code ->
    raise_s [%message "EBMC returned non-zero exit code" (exit_code : int)]
  | WSIGNALED signal | WSTOPPED signal ->
    raise_s [%message "EBMC was signaled or stopped" (signal : int)]
;;

let remove_file_if_exists filename =
  try Unix.unlink filename with
  | Unix.Unix_error (ENOENT, _, _) -> ()
;;

let rec mkdir_p dir =
  if (not (String.is_empty dir))
     && (not (String.equal dir "."))
     && not (String.equal dir "/")
  then (
    mkdir_p (Filename.dirname dir);
    try Unix.mkdir dir 0o755 with
    | Unix.Unix_error (EEXIST, _, _) -> ())
;;

let solve_impl
  ?reset
  ?tmpdir
  ~circuit_database
  ?(trace = true)
  ?(verilog_preamble = "")
  ~(rtl_output_mode : [ `Full_hierarchy | `Top_level_and_blackboxes ])
  ~in_filename
  ~out_filename
  ~bound
  circuit
  =
  Out_channel.with_file in_filename ~f:(fun verilog_file ->
    output_verilog
      ?database:circuit_database
      ~verilog_preamble
      ~rtl_output_mode
      verilog_file
      circuit);
  let circuit_name = Circuit.name circuit in
  let check_name name =
    let signal_opt =
      List.find (Circuit.inputs circuit) ~f:(fun signal ->
        List.mem (Signal.names signal) name ~equal:String.equal)
    in
    match signal_opt with
    | Some (Wire { driver; _ }) when Option.is_none driver -> name
    | Some signal ->
      raise_s [%message "Reset signal must be an input" (signal : Signal.t)]
    | None -> raise_s [%message "Signal not found" (name : string)]
  in
  let args =
    [ in_filename
    ; "--top"
    ; circuit_name
    ; "--bound"
    ; Int.to_string bound
    ; "--json-result"
    ; out_filename
    ]
    @ (ignore (trace : bool);
       [])
    @ Option.value_map reset ~default:[] ~f:(function
      | `High name -> [ "--reset"; check_name name ^ "==1" ]
      | `Low name -> [ "--reset"; check_name name ^ "==0" ])
  in
  let () =
    (* If tmpdir is specified, dump the run command to a file *)
    Option.iter tmpdir ~f:(fun name ->
      let data = quote_command (Hardcaml_tools_config.ebmc5 :: args) in
      Out_channel.write_all (name ^ "/run_ebmc.sh") ~data)
  in
  run_ebmc args;
  let ebmc_output =
    In_channel.read_all out_filename |> Jsonaf.of_string |> Ebmc_output.t_of_jsonaf
  in
  List.map ebmc_output.properties ~f:(fun status ->
    Ebmc_result.of_property_status ~circuit_name status)
  |> Map.of_alist_exn (module String)
;;

let solve
  ?reset
  ?tmpdir
  ?(rtl_output_mode : [ `Full_hierarchy | `Top_level_and_blackboxes ] = `Full_hierarchy)
  ?(verilog_preamble = "")
  ?trace
  ~circuit_database
  ~bound
  circuit
  =
  let file_path =
    match tmpdir with
    | Some name ->
      mkdir_p name;
      name ^ "/ebmc"
    | None -> Filename.temp_file "ebmc" ""
  in
  let in_filename = file_path ^ ".in.sv" in
  let out_filename = file_path ^ ".out.json" in
  Exn.protect
    ~f:(fun () ->
      solve_impl
        ?reset
        ?tmpdir
        ~circuit_database
        ?trace
        ~verilog_preamble
        ~rtl_output_mode
        ~in_filename
        ~out_filename
        ~bound
        circuit)
    ~finally:(fun () ->
      match tmpdir with
      | Some _ -> ()
      | None ->
        remove_file_if_exists file_path;
        remove_file_if_exists in_filename;
        remove_file_if_exists out_filename)
;;
