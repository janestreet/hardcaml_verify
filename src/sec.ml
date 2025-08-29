open! Base
open! Hardcaml

(* Given 2 circuits, show that they are equivalent. We are restricted to circuits which
   contain exactly the same registers, memories and instantiations (lets call this state).

   The circuits are transformed by logically removing the state, leaving only the
   combinational logic. The inputs for each bit of state become new circuit outputs. The
   outputs of each bit of state become new inputs.

   The 2 transformed circuits are connected so they share inputs. Outputs (including the
   new state outputs) are compared for equality.

   Then a sat solver is run to prove the circuits are the same.

   We use names to identify state which is the same in each circuit. In particular
   registers must have a unique name, while instantiations are identified by their module
   instance name (not module name). *)

module Instantiation_ports_match = struct
  type t =
    | Exactly
    | Left_is_subset_of_right
  [@@deriving sexp_of]
end

(* Get the (single) name of a signal. Returns an error if it contains 0 or more than 1
   name. This enforces the main restriction of this style of checking - we must very
   carefully identify state in each circuit being checked. *)
let get_unique_name context (s : Signal.t) =
  match s with
  | Inst { instantiation = { instance_label; _ }; _ } -> Ok instance_label
  | _ ->
    (match Signal.names s with
     | [ name ] -> Ok name
     | _ ->
       Or_error.error_s
         [%message
           "This signal requires a single unqiue name to identify it"
             (s : Signal.t)
             (context : string)])
;;

(* Fold in the Or_error monad. *)
let rec fold l ~init:arg ~f =
  match l with
  | [] -> Ok arg
  | h :: t ->
    let%bind.Or_error arg = f arg h in
    fold t ~init:arg ~f
;;

(* Transformation of the circuit into a checkable form. Logically state is removed and new
   inputs and outputs minted for them. The is reexpressed in terms of [Comb_gates.t]. *)
module Checkable_circuit = struct
  type unsheduled_signals =
    { inputs : Signal.t list
    ; regs : Signal.t list
    ; mems : Signal.t list
    ; insts : Signal.t list
    }
  [@@deriving sexp_of]

  type scheduling =
    { unscheduled : unsheduled_signals
    ; scheduled : Signal.t list
    }
  [@@deriving sexp_of]

  type register_outputs =
    { name : string
    ; clock : Comb_gates.t
    ; clock_edge : Edge.t
    ; reset : Comb_gates.t option
    ; reset_edge : Edge.t
    ; reset_to : Comb_gates.t option
    ; clear : Comb_gates.t option
    ; clear_to : Comb_gates.t option
    ; enable : Comb_gates.t option
    ; d : Comb_gates.t
    }
  [@@deriving sexp_of]

  type t =
    { circuit : Circuit.t
    ; schedule : Signal.t list
    ; scheduling : scheduling
    }
  [@@deriving sexp_of]

  type sat =
    { sat_gates : Comb_gates.t Map.M(Signal.Type.Uid).t
    ; sat_registers : register_outputs Map.M(Signal.Type.Uid).t
    }

  (* Find inputs and stateful elements *)
  let partition_signals circuit =
    let empty = [] in
    let add t c = t :: c in
    Signal_graph.depth_first_search
      (Circuit.signal_graph circuit)
      ~init:
        { unscheduled = { inputs = empty; regs = empty; mems = empty; insts = empty }
        ; scheduled = empty
        }
      ~f_before:(fun { unscheduled; scheduled } signal ->
        if Signal.is_empty signal
        then { unscheduled; scheduled }
        else if Signal.Type.is_reg signal
        then
          { unscheduled = { unscheduled with regs = add signal unscheduled.regs }
          ; scheduled
          }
        else if Circuit.is_input circuit signal
        then
          { unscheduled = { unscheduled with inputs = add signal unscheduled.inputs }
          ; scheduled
          }
        else if Signal.Type.is_mem signal
        then
          { unscheduled = { unscheduled with mems = add signal unscheduled.mems }
          ; scheduled
          }
        else if Signal.Type.is_inst signal
        then
          { unscheduled = { unscheduled with insts = add signal unscheduled.insts }
          ; scheduled
          }
        else { unscheduled; scheduled = add signal scheduled })
  ;;

  (* Identify each register in the circuit and find all it's inputs, some of which are
     optional. *)
  let register_outputs map (register : Signal.t) =
    let%bind.Or_error name = get_unique_name "Sec.register_outputs" register in
    let%bind.Or_error register, d =
      match register with
      | Reg { info = _; register; d } -> Ok (register, d)
      | _ -> Or_error.error_s [%message "[Sec.register_outputs] Expecting register"]
    in
    let find s =
      match Map.find map (Signal.uid s) with
      | Some s -> Ok s
      | None ->
        Or_error.error_s
          [%message
            "[Sec.register_outputs] failed to lookup input to register" (s : Signal.t)]
    in
    let find_opt s =
      match s with
      | None -> Ok None
      | Some s ->
        let%bind.Or_error s = find s in
        Ok (Some s)
    in
    let { Signal.Type.Reg.Clock_spec.clock; clock_edge } = register.clock in
    let%bind.Or_error clock = find clock
    and reset, reset_edge, reset_to =
      match register.reset with
      | None -> Ok (None, Edge.Rising, None)
      | Some { reset; reset_edge; reset_to } ->
        let%bind.Or_error reset = find reset
        and reset_to = find reset_to in
        Ok (Some reset, reset_edge, Some reset_to)
    and clear, clear_to =
      match register.clear with
      | None -> Ok (None, None)
      | Some { clear; clear_to } ->
        let%bind.Or_error clear = find clear
        and clear_to = find clear_to in
        Ok (Some clear, Some clear_to)
    and enable = find_opt register.enable
    and d = find d in
    Ok
      { name; clock; clock_edge; reset; reset_edge; reset_to; clear; clear_to; enable; d }
  ;;

  (* Create a map of all inputs, including the pseudo inputs for registers etc. *)
  let create_initial_sat_gates inputs regs insts =
    let merge a b =
      With_return.with_return (fun r ->
        Ok
          (Map.merge a b ~f:(fun ~key:_ how ->
             match how with
             | `Both _ ->
               r.return
                 (Or_error.error_s
                    [%message
                      "[Sec.create_initial_sat_gates] cannot merge input, register and \
                       instantiation maps"])
             | `Left x | `Right x -> Some x)))
    in
    let%bind.Or_error map = merge inputs regs in
    merge map insts
  ;;

  (* get all inputs, then convert each signal into [Comb_gates] from an ordered set of
     signals (the dependencies of each signal will be ready when it is processed). *)
  let compile_sat_gates schedule ~inputs ~registers ~instantiations =
    let%bind.Or_error initial_sat_gates =
      create_initial_sat_gates inputs registers instantiations
    in
    fold schedule ~init:initial_sat_gates ~f:(fun ready signal ->
      let add sat_gates =
        match Map.add ready ~key:(Signal.uid signal) ~data:sat_gates with
        | `Ok s -> Ok s
        | `Duplicate ->
          Or_error.error_s
            [%message
              "[Sec.compile_sat_gates] failed to add duplicate signal" (signal : Signal.t)]
      in
      let find signal =
        match Map.find ready (Signal.uid signal) with
        | Some s -> Ok s
        | None ->
          Or_error.error_s
            [%message
              "[Sec.compile_sat_gates] Failed to look up signal" (signal : Signal.t)]
      in
      match signal with
      | Empty -> Ok ready
      | Const { info = _; constant } ->
        add (Comb_gates.of_constant (Bits.to_constant constant))
      | Op2 { info = _; op; arg_a; arg_b } ->
        let%bind.Or_error arg_a = find arg_a in
        let%bind.Or_error arg_b = find arg_b in
        add
          ((match op with
            | Add -> Comb_gates.( +: )
            | Sub -> Comb_gates.( -: )
            | Mulu -> Comb_gates.( *: )
            | Muls -> Comb_gates.( *+ )
            | And -> Comb_gates.( &: )
            | Or -> Comb_gates.( |: )
            | Xor -> Comb_gates.( ^: )
            | Eq -> Comb_gates.( ==: )
            | Lt -> Comb_gates.( <: ))
             arg_a
             arg_b)
      | Mux { info = _; select; cases } ->
        let%bind.Or_error select = find select in
        let%bind.Or_error cases = Or_error.all (List.map cases ~f:find) in
        add (Comb_gates.mux select cases)
      | Cases { info = _; select; cases; default } ->
        let%bind.Or_error select = find select in
        let%bind.Or_error default = find default in
        let%bind.Or_error cases =
          Or_error.all
            (List.map cases ~f:(fun (match_with, value) ->
               let%bind.Or_error match_with = find match_with in
               let%map.Or_error value = find value in
               match_with, value))
        in
        add (Comb_gates.cases ~default select cases)
      | Cat { info = _; args } ->
        let%bind.Or_error args = Or_error.all (List.map args ~f:find) in
        add (Comb_gates.concat_msb args)
      | Not { info = _; arg } ->
        let%bind.Or_error arg = find arg in
        add (Comb_gates.( ~: ) arg)
      | Wire { info = _; driver = None } -> Ok ready
      | Wire { info = _; driver = Some driver } ->
        let%bind.Or_error driver = find driver in
        add driver
      | Select { info = _; arg; high; low } ->
        let%bind.Or_error arg = find arg in
        add arg.Comb_gates.:[high, low]
      | Reg { info = _; register = _; d = _ } ->
        (* We do nothing with registers here. *)
        Ok ready
      | Multiport_mem _ | Mem_read_port _ ->
        Or_error.error_s [%message "memories are not supported (yet)"]
      | Inst { info = _; instantiation = _ } -> Ok ready)
  ;;

  (* compile each register *)

  let compile_sat_registers sat_gates regs =
    let%bind.Or_error regs_and_outputs =
      List.map regs ~f:(fun reg ->
        let%map.Or_error out = register_outputs sat_gates reg in
        Signal.uid reg, out)
      |> Or_error.all
    in
    match Map.of_alist (module Signal.Type.Uid) regs_and_outputs with
    | `Ok map -> Ok map
    | `Duplicate_key _ ->
      Or_error.error_s
        [%message "[Sec.compile_sat_registers] Failed to add duplicate signal"]
  ;;

  module Scheduling_deps = Signal.Type.Make_deps (struct
      let fold (t : Signal.t) ~init ~f =
        match t with
        | Signal.Type.Inst _ -> init
        | _ -> Signal_graph.Deps_for_loop_checking.fold t ~init ~f
      ;;
    end)

  let topsort outputs =
    Result.map_error
      (Signal_graph.topological_sort
         ~deps:(module Scheduling_deps)
         (Signal_graph.create outputs))
      ~f:(fun cycle -> Error.create_s [%sexp (cycle : Signal.t list)])
  ;;

  (* Compute a topological ordering of signals *)
  let create circuit =
    (* create a topological sorting of combinational nodes *)
    let outputs = Circuit.outputs circuit in
    let scheduling = partition_signals circuit in
    let%bind.Or_error schedule =
      if List.is_empty outputs then Ok [] else topsort outputs
    in
    Ok { circuit; schedule; scheduling }
  ;;

  (* Compile combinational and register logic *)
  let compile t ~inputs ~registers ~instantiations =
    let%bind.Or_error sat_gates =
      compile_sat_gates t.schedule ~inputs ~registers ~instantiations
    in
    let%bind.Or_error sat_registers =
      compile_sat_registers sat_gates t.scheduling.unscheduled.regs
    in
    Ok { sat_gates; sat_registers }
  ;;
end

module Pair = struct
  type 'a t =
    { left : 'a
    ; right : 'a
    }
  [@@deriving sexp_of]

  let map p ~f = { left = f p.left; right = f p.right }
  let map2 p q ~f = { left = f p.left q.left; right = f p.right q.right }

  let map4 p q r s ~f =
    { left = f p.left q.left r.left s.left; right = f p.right q.right r.right s.right }
  ;;

  let lift_errors { left; right } =
    let%bind.Or_error left and right in
    Ok { left; right }
  ;;

  let map_or_error p ~f = map p ~f |> lift_errors
  let map2_or_error p q ~f = map2 p q ~f |> lift_errors
  let map4_or_error p q r s ~f = map4 p q r s ~f |> lift_errors
end

type 'a named =
  { name : string
  ; data : 'a
  }
[@@deriving sexp_of]

type 'a paired = 'a named Pair.t [@@deriving sexp_of]

let map_by_unique_names context (pair : Signal.t list Pair.t) =
  let module T = struct
    type t =
      { set : Set.M(String).t
      ; map : Signal.t Map.M(String).t
      }

    let empty = { set = Set.empty (module String); map = Map.empty (module String) }
  end
  in
  let of_signals signals =
    fold signals ~init:T.empty ~f:(fun set_and_map signal ->
      let { T.set; map } = set_and_map in
      let%bind.Or_error name =
        get_unique_name ("[Sec.pair_signals_by_name] " ^ context) signal
      in
      let set = Set.add set name in
      let%bind.Or_error map =
        match Map.add map ~key:name ~data:signal with
        | `Ok map -> Ok map
        | `Duplicate ->
          Or_error.error_s
            [%message
              ("[Sec.map_by_unique_names] duplicate " ^ context) (signal : Signal.t)]
      in
      Ok { T.set; map })
  in
  let%bind.Or_error { left; right } = Pair.map_or_error pair ~f:of_signals in
  if not (Set.equal left.set right.set)
  then (
    let only_in_left = Set.diff left.set right.set in
    let only_in_right = Set.diff right.set left.set in
    Or_error.error_s
      [%message
        "[Sec.pair_signals_by_name] left and right circuits contain different names"
          (context : string)
          (only_in_left : Set.M(String).t)
          (only_in_right : Set.M(String).t)])
  else Ok ({ Pair.left = left.map; right = right.map }, Set.to_list left.set)
;;

let pair_signals_by_name context (signals : Signal.t list Pair.t) =
  let%bind.Or_error maps, unique_names = map_by_unique_names context signals in
  List.map unique_names ~f:(fun name ->
    let%bind.Or_error signal =
      Pair.map_or_error maps ~f:(fun map ->
        let%bind.Or_error data =
          match Map.find map name with
          | Some name -> Ok name
          | None ->
            Or_error.error_s [%message "Logic error, name should exist in both maps"]
        in
        Ok { name; data })
    in
    (* Check the widths match. Skip this for instantiations - if the circuit does not use
       an output port, it may not defined in one of the circuit. This can happen when
       converting one of the designs from verilog. We will do checks on the ports
       themselves. *)
    if Signal.width signal.left.data <> Signal.width signal.right.data
       && not (Signal.Type.is_inst signal.left.data)
    then
      Or_error.error_s
        [%message
          "[Sec.pair_signals_by_name] unable to pair signals - different widths"
            (context : string)
            (signal : Signal.t named Pair.t)]
    else Ok signal)
  |> Or_error.all
;;

type 'a paired_inputs =
  { paired : Signal.t paired list
  ; inputs : Comb_gates.t Map.M(Signal.Type.Uid).t Pair.t
  }
[@@deriving sexp_of]

let pair_ports_by_name context ports =
  let%bind.Or_error paired = pair_signals_by_name context ports in
  let%bind.Or_error left, right =
    fold
      paired
      ~init:(Map.empty (module Signal.Type.Uid), Map.empty (module Signal.Type.Uid))
      ~f:(fun (left, right) paired ->
        let add map key data =
          match Map.add map ~key ~data with
          | `Ok map -> Ok map
          | `Duplicate ->
            Or_error.error_s
              [%message
                "[Sec.pair_inputs_by_name] failed to add duplicate signal"
                  (context : string)]
        in
        let input =
          Comb_gates.input
            (context ^ "$" ^ paired.left.name)
            (Signal.width paired.left.data)
        in
        let%bind.Or_error left = add left (Signal.uid paired.left.data) input in
        let%bind.Or_error right = add right (Signal.uid paired.right.data) input in
        Ok (left, right))
  in
  Ok { paired; inputs = { left; right } }
;;

let pair_inputs_by_name = pair_ports_by_name "input"
let pair_outputs_by_name = pair_signals_by_name "output"
let pair_registers_by_name = pair_ports_by_name "register"

let instantiation_of_signal (s : Signal.t) =
  match s with
  | Inst { instantiation; _ } -> Ok instantiation
  | _ ->
    (* The error context doesn't matter much here - it shouldn't happen *)
    Or_error.error_s [%message "Expected an instantiation" (s : Signal.t)]
;;

let instantiation_names_match s =
  let%bind.Or_error i = Pair.map_or_error s ~f:instantiation_of_signal in
  let error context =
    Or_error.error_s
      [%message "[Sec.check_instantiation]" (context : string) (s : Signal.t Pair.t)]
  in
  if not (String.equal i.left.circuit_name i.right.circuit_name)
  then error "module names do not match"
  else if not (String.equal i.left.instance_label i.right.instance_label)
  then error "module instantiation labels do not match"
  else Ok ()
;;

let instantiation_ports_test ~(instantiation_ports_match : Instantiation_ports_match.t) =
  match instantiation_ports_match with
  | Exactly -> Set.equal
  | Left_is_subset_of_right -> fun left right -> Set.is_subset left ~of_:right
;;

let instantiation_input_ports_match ~instantiation_ports_match instantiation_signal =
  let%bind.Or_error i =
    Pair.map_or_error instantiation_signal ~f:instantiation_of_signal
  in
  let module Port = struct
    module T = struct
      type t = Signal.t Signal.Type.Inst.Input.t

      let sexp_of_t { Signal.Type.Inst.Input.name; input_signal } =
        [%sexp_of: string * Signal.t] (name, input_signal)
      ;;

      let compare
        { Signal.Type.Inst.Input.name = a; input_signal = x }
        { Signal.Type.Inst.Input.name = b; input_signal = y }
        =
        [%compare: string * int] (a, Signal.width x) (b, Signal.width y)
      ;;
    end

    include T
    include Comparator.Make (T)
  end
  in
  let intantiation_port_sets =
    Pair.map i ~f:(fun i -> Set.of_list (module Port) i.inputs)
  in
  let test_sets = instantiation_ports_test ~instantiation_ports_match in
  if not (test_sets intantiation_port_sets.left intantiation_port_sets.right)
  then (
    let unmatched_on_left =
      Set.diff intantiation_port_sets.left intantiation_port_sets.right
    in
    let unmatched_on_right =
      Set.diff intantiation_port_sets.right intantiation_port_sets.left
    in
    Or_error.error_s
      [%message
        "[Sec.check_instantiation] input ports do not match"
          (instantiation_ports_match : Instantiation_ports_match.t)
          (instantiation_signal : Signal.t Pair.t)
          (unmatched_on_left : Set.M(Port).t)
          (unmatched_on_right : Set.M(Port).t)])
  else Ok ()
;;

let instantiation_output_ports_match ~instantiation_ports_match s =
  let%bind.Or_error i = Pair.map_or_error s ~f:instantiation_of_signal in
  let module Port = struct
    module T = struct
      type t = Signal.Type.Inst.Output.t

      let sexp_of_t { Signal.Type.Inst.Output.name; output_width; output_low_index } =
        [%sexp_of: string * (int * int)] (name, (output_width, output_low_index))
      ;;

      let compare
        { Signal.Type.Inst.Output.name = a; output_width = m; output_low_index = _ }
        { Signal.Type.Inst.Output.name = b; output_width = n; output_low_index = _ }
        =
        [%compare: string * int] (a, m) (b, n)
      ;;
    end

    include T
    include Comparator.Make (T)
  end
  in
  let p = Pair.map i ~f:(fun i -> Set.of_list (module Port) i.outputs) in
  let test_sets = instantiation_ports_test ~instantiation_ports_match in
  if not (test_sets p.left p.right)
  then
    Or_error.error_s
      [%message
        "[Sec.check_instantiation] output ports do not match"
          (instantiation_ports_match : Instantiation_ports_match.t)
          (s : Signal.t Pair.t)
          (p : Set.M(Port).t Pair.t)]
  else Ok ()
;;

let check_instantiations ~instantiation_ports_match s =
  let%bind.Or_error () = instantiation_names_match s
  and () = instantiation_input_ports_match ~instantiation_ports_match s
  and () = instantiation_output_ports_match ~instantiation_ports_match s in
  Ok ()
;;

let build_right_instantiation_pseudo_input (i : Signal.t named) =
  let%bind.Or_error inst = instantiation_of_signal i.data in
  let pseudo_inputs =
    List.map
      inst.outputs
      ~f:(fun { name = port_name; output_width = width; output_low_index = _ } ->
        Comb_gates.input ("instantiation$" ^ i.name ^ "$" ^ port_name) width)
  in
  Ok (Comb_gates.concat_lsb pseudo_inputs)
;;

let rebuild_left_instantiation_pseudo_input_from_right
  input
  (insts : Signal.t named Pair.t)
  =
  let%bind.Or_error insts =
    Pair.map_or_error insts ~f:(fun i -> instantiation_of_signal i.data)
  in
  (* scan the instantiation in the right circuit, and build a map of output port to the
     select into the input *)
  let%bind.Or_error right_map =
    fold
      insts.right.outputs
      ~init:(Map.empty (module String))
      ~f:
        (fun
          map { name = port_name; output_width = width; output_low_index = lo_index } ->
        match Map.add map ~key:port_name ~data:(width, lo_index) with
        | `Ok m -> Ok m
        | `Duplicate ->
          Or_error.error_s
            [%message
              "Duplicate instantiation output port"
                (insts.right.circuit_name : string)
                (insts.right.instance_label : string)
                (port_name : string)])
  in
  (* rebuild the left input from the right input *)
  let%bind.Or_error left_ports =
    List.map insts.left.outputs ~f:(fun { name = port_name; _ } ->
      match Map.find right_map port_name with
      | None ->
        Or_error.error_s
          [%message
            "Failed to find instantiation output port"
              (insts.left.circuit_name : string)
              (insts.left.instance_label : string)
              (port_name : string)]
      | Some (width, lo_index) -> Ok input.Comb_gates.:[width + lo_index - 1, lo_index])
    |> Or_error.all
  in
  Ok (Comb_gates.concat_lsb left_ports)
;;

(* Associate instantiations together, then run through their outputs ports and create the
   psuedo inputs.

   This is complicated by [Instantiation_ports_match] where we allow different port sets
   (specifically the left can be a subset of the right). Therefore we create the input
   port for the right instantiation and construct an input from it for the left
   instantiation.
*)
let pair_instantiations_by_name ~instantiation_ports_match insts =
  let context = "instantiation" in
  let%bind.Or_error paired = pair_signals_by_name context insts in
  let%bind.Or_error left, right =
    fold
      paired
      ~init:(Map.empty (module Signal.Type.Uid), Map.empty (module Signal.Type.Uid))
      ~f:(fun (left, right) paired ->
        let%bind.Or_error () =
          check_instantiations
            ~instantiation_ports_match
            (Pair.map paired ~f:(fun d -> d.data))
        in
        let add map key data =
          match Map.add map ~key ~data with
          | `Ok map -> Ok map
          | `Duplicate ->
            Or_error.error_s
              [%message
                "[Sec.pair_inputs_by_name] failed to add duplicate signal"
                  (context : string)]
        in
        let%bind.Or_error right_input =
          build_right_instantiation_pseudo_input paired.right
        in
        let%bind.Or_error right = add right (Signal.uid paired.right.data) right_input in
        let%bind.Or_error left_input =
          rebuild_left_instantiation_pseudo_input_from_right right_input paired
        in
        let%bind.Or_error left = add left (Signal.uid paired.left.data) left_input in
        Ok (left, right))
  in
  Ok { paired; inputs = { left; right } }
;;

let lookup (map : Comb_gates.t Map.M(Signal.Type.Uid).t) signal =
  match Map.find map (Signal.uid signal) with
  | None ->
    Or_error.error_s
      [%message "Failed to find signal in Comb_gates map" (signal : Signal.t)]
  | Some gates -> Ok gates
;;

let compare_signal_pair maps (p : _ paired) =
  let%bind.Or_error name = get_unique_name "output port" p.left.data in
  let%bind.Or_error p = Pair.map2_or_error maps p ~f:(fun map p -> lookup map p.data) in
  Ok { name; data = Comb_gates.(p.left ==: p.right) }
;;

let compare_signal_pairs maps p = Or_error.all (List.map p ~f:(compare_signal_pair maps))

type t =
  { checkable_circuits : Checkable_circuit.t Pair.t
  ; circuit_outputs_propositions : Comb_gates.t named list
  ; register_inputs_propositions : Comb_gates.t named list
  ; instantiation_inputs_propositions : Comb_gates.t named list named list
  }
[@@deriving sexp_of]

module Proposition = struct
  type t = Comb_gates.t [@@deriving sexp_of]
end

module Equivalence_result = struct
  type t = Cnf.Model_with_vectors.input list Sat.t [@@deriving sexp_of]
end

let reduce_and l =
  if List.is_empty l then Comb_gates.vdd else Comb_gates.(reduce l ~f:( &: ))
;;

let reduce_and_named (l : _ named list) =
  List.map l ~f:(fun { name = _; data } -> data) |> reduce_and
;;

let compare_register (circuits : Checkable_circuit.sat Pair.t) (pair : Signal.t paired) =
  (* Find the register inputs (which become outputs of the modified circuit we check) *)
  let find_reg map s =
    match Map.find map (Signal.uid s.data) with
    | Some d -> Ok d
    | None -> Or_error.error_s [%message "Failed to find register" (s : Signal.t named)]
  in
  let%bind.Or_error regs =
    Pair.map2_or_error circuits pair ~f:(fun c -> find_reg c.sat_registers)
  in
  (* Check each part matches - clock, reset, clear, enable *)
  let field f = Pair.map regs ~f in
  let eq (p : _ Pair.t) = Comb_gates.(p.left ==: p.right) in
  let check_edge context (e : _ Pair.t) =
    if Edge.equal e.left e.right
    then Ok ()
    else
      Or_error.error_s
        [%message
          "Edge specifications do not match"
            (context : string)
            (e : Edge.t Pair.t)
            ~name:(pair.left.name : string)]
  in
  let check_optional_signal context (s : _ Pair.t) =
    match s.left, s.right with
    | None, None -> Ok Comb_gates.vdd
    | Some left, Some right -> Ok (eq { Pair.left; right })
    | _ ->
      Or_error.error_s
        [%message "Unable to compare registers - inputs differ" (context : string)]
  in
  let clock = eq (field (fun d -> d.clock)) in
  let%bind.Or_error () = check_edge "clock_edge" (field (fun d -> d.clock_edge))
  and reset = check_optional_signal "reset" (field (fun d -> d.reset))
  and () = check_edge "reset_edge" (field (fun d -> d.reset_edge))
  and reset_to = check_optional_signal "reset_to" (field (fun d -> d.reset_to))
  and clear = check_optional_signal "clear" (field (fun d -> d.clear))
  and clear_to = check_optional_signal "clear_to" (field (fun d -> d.clear_to))
  and enable = check_optional_signal "enable" (field (fun d -> d.enable)) in
  let d = eq (field (fun d -> d.d)) in
  Ok
    { name = pair.left.name
    ; data = Comb_gates.(clock &: reset &: reset_to &: clear &: clear_to &: enable &: d)
    }
;;

let compare_registers
  (circuits : Checkable_circuit.sat Pair.t)
  (regs : Signal.t paired list)
  =
  List.map regs ~f:(compare_register circuits) |> Or_error.all
;;

(* Go through the inputs of the instantiation, and compare them on the left and right. *)
let compare_instantiation
  (maps : _ Map.M(Signal.Type.Uid).t Pair.t)
  (paired : Signal.t paired)
  =
  let%bind.Or_error i =
    Pair.map_or_error paired ~f:(fun d -> instantiation_of_signal d.data)
  in
  let right_inputs =
    List.map i.right.inputs ~f:(fun { name; input_signal } ->
      name, lookup maps.right input_signal)
    |> Map.of_alist_exn (module String)
  in
  (* Build the propositions based on the left circuits instantiation inputs. They have
     been checked to be equal to, or a subset of, the right circuits inputs. *)
  let%bind.Or_error proposition =
    List.map i.left.inputs ~f:(fun { name; input_signal } ->
      let%bind.Or_error right =
        match Map.find right_inputs name with
        | Some right -> right
        | None ->
          Or_error.error_s
            [%message
              "[Sec.compare_instantiation] instantiation input not present"
                (name : string)]
      in
      let%bind.Or_error left = lookup maps.left input_signal in
      Ok { name; data = Comb_gates.(left ==: right) })
    |> Or_error.all
  in
  Ok { name = i.left.instance_label; data = proposition }
;;

let compare_instantiations maps (instantiations : Signal.t paired list) =
  Or_error.all (List.map instantiations ~f:(compare_instantiation maps))
;;

let create ?(instantiation_ports_match : Instantiation_ports_match.t = Exactly) left right
  =
  let circuits = { Pair.left; right } in
  (* Topsort the circuits and find inputs, outputs, registers ets *)
  let%bind.Or_error checkable_circuits =
    Pair.map_or_error circuits ~f:Checkable_circuit.create
  in
  (* Pair inputs, outputs, registers and instantiations between both circuits and perform
     various sanity checks. *)
  let%bind.Or_error paired_inputs =
    pair_inputs_by_name (Pair.map circuits ~f:Circuit.inputs)
  and paired_outputs = pair_outputs_by_name (Pair.map circuits ~f:Circuit.outputs)
  and paired_regs =
    pair_registers_by_name
      (Pair.map checkable_circuits ~f:(fun c -> c.scheduling.unscheduled.regs))
  and paired_instantiations =
    pair_instantiations_by_name
      ~instantiation_ports_match
      (Pair.map checkable_circuits ~f:(fun c -> c.scheduling.unscheduled.insts))
  in
  (* Compile the circuits into a CNF-able form *)
  let%bind.Or_error compiled_circuits =
    Pair.map4_or_error
      checkable_circuits
      paired_inputs.inputs
      paired_regs.inputs
      paired_instantiations.inputs
      ~f:(fun checkable_circuit inputs registers instantiations ->
        Checkable_circuit.compile checkable_circuit ~inputs ~registers ~instantiations)
  in
  (* Build the logical equivalence proposition *)
  let sat_gates = Pair.map compiled_circuits ~f:(fun c -> c.sat_gates) in
  let%bind.Or_error register_inputs_propositions =
    compare_registers compiled_circuits paired_regs.paired
  and instantiation_inputs_propositions =
    compare_instantiations sat_gates paired_instantiations.paired
  and circuit_outputs_propositions = compare_signal_pairs sat_gates paired_outputs in
  Ok
    { checkable_circuits
    ; circuit_outputs_propositions
    ; register_inputs_propositions
    ; instantiation_inputs_propositions
    }
;;

let find_named (t : _ named list) ~name =
  List.find t ~f:(fun t -> String.equal t.name name)
;;

let circuit_outputs_proposition t = reduce_and_named t.circuit_outputs_propositions

let find_circuit_output_port_proposition t ~port_name =
  let%bind.Option { name = _; data } =
    find_named t.circuit_outputs_propositions ~name:port_name
  in
  Some data
;;

let find_register_inputs_proposition t ~name =
  let%bind.Option { name = _; data } = find_named t.register_inputs_propositions ~name in
  Some data
;;

let reduce_and_instantiation_propositions t =
  let p = t.instantiation_inputs_propositions in
  List.map p ~f:(fun { name = _; data } -> reduce_and_named data) |> reduce_and
;;

let find_instantiation_inputs_proposition t ~name =
  let%bind.Option { name = _; data } =
    find_named t.instantiation_inputs_propositions ~name
  in
  Some (reduce_and_named data)
;;

let find_instantiation_input_port_proposition t ~instantiation_name ~port_name =
  let%bind.Option { name = _; data = ports } =
    find_named t.instantiation_inputs_propositions ~name:instantiation_name
  in
  let%bind.Option { name = _; data } = find_named ports ~name:port_name in
  Some data
;;

let equivalent propositions =
  Solver.solve (Comb_gates.cnf (Comb_gates.( ~: ) (reduce_and propositions)))
;;

let circuits_equivalent t =
  equivalent
    [ circuit_outputs_proposition t
    ; reduce_and_named t.register_inputs_propositions
    ; reduce_and_instantiation_propositions t
    ]
;;
