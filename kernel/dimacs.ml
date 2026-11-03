open Base
open Stdio

let write_problem (cnf : Cnf.t) out_channel =
  let open Out_channel in
  fprintf
    out_channel
    "p cnf %i %i\n"
    (Cnf.number_of_variables cnf)
    (Cnf.number_of_clauses cnf);
  Cnf.iter cnf ~f:(fun disjunction ->
    Cnf.Disjunction.iter disjunction ~f:(fun literal ->
      match Cnf.to_int_literal cnf literal with
      | Some literal -> fprintf out_channel "%i " literal
      | None -> raise_s [%message "Cannot lookup literal" (literal : Cnf.Literal.t)]);
    fprintf out_channel "0\n")
;;

let parse_sat_result lines =
  try
    let l =
      lines
      |> List.map ~f:(String.split_on_chars ~on:[ ' '; '\r'; '\t'; '\n' ])
      |> List.concat
      |> List.filter_map ~f:(fun s ->
        if String.compare s "v" = 0 || String.compare s "" = 0
        then None
        else Some (Int.of_string s))
    in
    Ok (Sat.Sat l)
  with
  | _ -> Or_error.error_s [%message "Failed to parse SAT output"]
;;

let parse_result lines =
  match lines with
  | [] -> Or_error.error_s [%message "No SAT result"]
  | hd :: tl ->
    (match String.lowercase hd with
     | "unsat" | "unsatisfiable" | "s unsatisfiable" -> Ok Sat.Unsat
     | "sat" | "satisfiable" | "s satisfiable" -> parse_sat_result tl
     | _ -> Or_error.error_s [%message "Dont know how to parse SAT result"])
;;

let read_result in_channel = In_channel.input_lines in_channel |> parse_result
