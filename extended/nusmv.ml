open Base
open Hardcaml
include Hardcaml_verify_kernel.Nusmv

module Counter_example_trace = struct
  include Counter_example_trace
  module Data = Hardcaml.Wave_data_in_cycles

  let to_cyclesim_waveform nusmv counter_example_trace =
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
    let waves =
      Map.to_alist data_map
      |> List.filter ~f:(fun (name, _) -> not (String.is_prefix name ~prefix:"_"))
      |> List.filter ~f:(fun (name, _) -> Set.mem all_names name)
      |> List.map ~f:(fun (name, data) ->
        let width = Bits.width (Data.get data 0) in
        let wave =
          { Wave_data.Wave.name
          ; width
          ; typ =
              (if Set.mem input_names name
               then Input
               else if Set.mem output_names name
               then Output
               else Internal)
          ; is_pseudo_clock = false
          ; wave_data = data
          ; wave_format = Bit_or Hex
          }
        in
        wave)
    in
    Wave_data.By_cycle (Array.of_list waves)
  ;;

  let to_waveform nusmv counter_example_trace =
    to_cyclesim_waveform nusmv counter_example_trace
  ;;
end
