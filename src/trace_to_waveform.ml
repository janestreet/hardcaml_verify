open Base
open Hardcaml
open Hardcaml_formal_verification_kernel
module Data = Hardcaml.Wave_data_in_mutable_events

(* Waveform consumers assume the cyclesim convention of two time steps per cycle - e.g.
   the waveform server's [Server_query] reports [num_cycles] over two-step cycles and
   samples cycle [c] at time [2 * c] - so place each trace state on a cycle boundary and
   span the full final cycle. *)
let time_steps_per_cycle = 2

let convert circuit counter_example_trace =
  let states = Counter_example_trace.to_states counter_example_trace in
  let data_map =
    match states with
    | hd :: tl ->
      let max_time = ref ((time_steps_per_cycle * List.length states) - 1) in
      let buffer_map =
        Map.of_alist_exn (module String) hd
        |> Map.map ~f:(fun bits ->
          let data = Data.create (Bits.width bits) max_time in
          Data.insert data 0 bits;
          data)
      in
      List.iteri tl ~f:(fun index_minus_one state_map ->
        let time = time_steps_per_cycle * (index_minus_one + 1) in
        let state_map = Map.of_alist_exn (module String) state_map in
        Map.iteri buffer_map ~f:(fun ~key ~data ->
          (* Check if this state has a new value for each variable. Missing values hold
             the previous value in the mutable-event representation. *)
          match Map.find state_map key with
          | None -> ()
          | Some bits ->
            if not (Bits.equal bits (Data.get data (time - 1)))
            then Data.insert data time bits));
      buffer_map
    | [] -> raise_s [%message "Cannot visualize an empty counter example trace!"]
  in
  let signals_to_names signals =
    signals
    |> List.filter ~f:(fun s -> not (Signal.is_empty s))
    |> List.concat_map ~f:Signal.names
    |> Set.of_list (module String)
  in
  let input_names = Circuit.inputs circuit |> signals_to_names in
  let output_names = Circuit.outputs circuit |> signals_to_names in
  let all_names = Circuit.signal_map circuit |> Map.data |> signals_to_names in
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
        ; wave_data = data
        ; wave_format = Bit_or Hex
        }
      in
      wave)
  in
  Wave_data.By_mutable_event (Array.of_list waves)
;;
