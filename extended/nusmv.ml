open Base
open Hardcaml
open Hardcaml_waveterm_kernel
open Hardcaml_waveterm_cyclesim
include Hardcaml_verify_kernel.Nusmv

module Counter_example_trace = struct
  include Counter_example_trace

  let to_waveform nusmv counter_example_trace =
    let states = to_trace counter_example_trace in
    let data_map =
      match states with
      | hd :: tl ->
        let buffer_map =
          Map.of_alist_exn (module String) hd
          |> Map.map ~f:(fun bits ->
            let data = Data.create (Bits.width bits) in
            Data.set data 0 bits;
            data)
        in
        List.iteri tl ~f:(fun index_minus_one state_map ->
          let index = index_minus_one + 1 in
          let state_map = Map.of_alist_exn (module String) state_map in
          Map.iteri buffer_map ~f:(fun ~key ~data ->
            let bits =
              (* Check if this state has a new value for each variable *)
              match Map.find state_map key with
              | Some bits -> bits
              | None -> Data.get data (index - 1)
            in
            Data.set data index bits));
        buffer_map
      | [] -> raise_s [%message "Cannot visualize an empty counter example trace!"]
    in
    let signals_to_names signals =
      signals
      |> List.filter ~f:(fun s -> not (Signal.is_empty s))
      |> List.concat_map ~f:Signal.names
      |> Set.of_list (module String)
    in
    let input_names = Circuit.inputs (circuit nusmv) |> signals_to_names in
    let output_names = Circuit.outputs (circuit nusmv) |> signals_to_names in
    let all_names = Circuit.signal_map (circuit nusmv) |> Map.data |> signals_to_names in
    let waves_and_ports =
      Map.to_alist data_map
      |> List.filter ~f:(fun (name, _) -> not (String.is_prefix name ~prefix:"_"))
      |> List.filter ~f:(fun (name, _) -> Set.mem all_names name)
      |> List.map ~f:(fun (name, data) ->
        let width = Bits.width (Data.get data 0) in
        let wave =
          match width with
          | 1 -> Wave.Binary { name; data; style = { style = Style.default } }
          | _ ->
            Wave.Data
              { name
              ; data
              ; wave_format = { current = Hex; default = Hex }
              ; text_alignment = Left
              ; style = { style = Style.default }
              }
        in
        let port =
          let type_ =
            if Set.mem input_names name
            then Port.Type.Input
            else if Set.mem output_names name
            then Port.Type.Output
            else Port.Type.Internal
            (* We already filtered to ensure it's in all_names *)
          in
          { Port.type_; port_name = Port_name.of_string name; width }
        in
        wave, port)
    in
    let waves, ports = List.unzip waves_and_ports in
    Waveform.create_from_data ~waves ~ports
  ;;
end
