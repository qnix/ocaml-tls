open Read_trace

let to_re str =
  (Str.regexp_string str, String.length str)

let user_agent =  to_re "User-Agent"
let referer = to_re "Referer"

type result = [
  | `UserAgent of string
  | `Referer of string
]

let result_to_string = function
  | `UserAgent s -> "user-agent: " ^ s
  | `Referer r -> "referer: " ^ r

let find_user_agent_referer buf =
  let str = Cstruct.to_string buf in
  let find_re (re, l) =
    try
      let idx = Str.search_forward re str 0 in
      let start = succ (idx + l) in
      let nl = try String.index_from str start '\r' with Not_found -> String.length str in
      Some (String.sub str start (nl - start))
    with
      _ -> None
  in
  match find_re user_agent, find_re referer with
  | Some x, Some y -> [`UserAgent x ; `Referer y]
  | Some x, None -> [`UserAgent x]
  | None, Some y -> [`Referer y]
  | None, None -> []

let rec analyse acc = function
  | (`ApplicationDataIn s)::xs -> analyse ((find_user_agent_referer s) @ acc) xs
  | _::xs -> analyse acc xs
  | [] -> acc

let analyse_and_print traces =
  let res = analyse [] traces in
  let d = List.map result_to_string res in
  () (* Printf.printf "result:\n  %s\n" (String.concat "\n  " d) *)

let handle file =
  match load file with
  | None -> Printf.printf "error loading %s\n" file ; None
  | Some (Some time, traces) ->
    let timestring = timestamp_to_string time in
    (* Printf.printf "trace from %s with %d elements\n" timestring (List.length traces) ; *)
    (* analyse_and_print traces *)
    Some (timestring, traces)
  | Some (None, traces) ->
    (* Printf.printf "trace (no time) with %d elements\n" (List.length traces) ; *)
    (* analyse_and_print traces *)
    Some ("", traces)


let run dir file =
  match dir, file with
  | Some file, _ ->
    let dirent = Unix.opendir file in
    Unix.readdir dirent ; Unix.readdir dirent ;
    let filen = ref (try Some (Unix.readdir dirent) with End_of_file -> None) in
    let successes = Hashtbl.create 100
    and failures = Hashtbl.create 100
    in
    let suc (ts, traces) name =
      if Hashtbl.mem successes name then
        let ele = Hashtbl.find successes name in
        Printf.printf "replaced\n%!" ;
        Hashtbl.replace successes name (succ ele)
      else
        Hashtbl.add successes name 1
    and fails e name =
      if Hashtbl.mem failures e then
        let ele = Hashtbl.find failures e in
        Hashtbl.replace failures e (name :: ele)
      else
        Hashtbl.add failures e [name]
    in
    while not (!filen = None) do
      let Some filename = !filen in
      (try
         match handle (Filename.concat file filename) with
         | Some x -> suc x filename
         | None -> ()
       with
       | Trace_error e -> fails e filename
       | e -> Printf.printf "problem with file %s\n%!" filename ; raise e) ;
      filen := try Some (Unix.readdir dirent) with End_of_file -> None
    done ;
    Printf.printf "statistics: %d success size, %d failure size\n"
      (Hashtbl.length successes) (Hashtbl.length failures) ;
    Hashtbl.iter  (fun k v ->
        Printf.printf "reason %s count %d\n" (Sexplib.Sexp.to_string_hum (sexp_of_error k)) (List.length v))
      failures
  | None, Some file ->
    try (match handle file with
        | Some (ts, traces) -> Printf.printf "trace from %s, loaded %d traces\n" ts (List.length traces)
        | None -> Printf.printf "couldn't load any traces..." )
    with
    | Trace_error e -> Printf.printf "problem %s\n" (Sexplib.Sexp.to_string_hum (sexp_of_error e))


let trace_dir = ref None
let trace_file = ref None
let rest = ref []

let usage = "usage " ^ Sys.argv.(0)

let arglist = [
  ("-f", Arg.String (fun f -> trace_file := Some f), "trace file");
  ("-d", Arg.String (fun d -> trace_dir := Some d), "trace directory");
]

let () =
  Arg.parse arglist (fun x -> rest := x :: !rest) usage ;
  run !trace_dir !trace_file

(* results:
tls0 - statistics: 6290 success size, 2 failure size
reason InvalidHmacKey count 1
reason (InvalidInitialState Established) count 178
tls1 - statistics: 4319 success size, 1 failure size
reason (InvalidInitialState Established) count 6
tls2 - statistics: 4132 success size, 1 failure size
reason (InvalidInitialState Established) count 9
tls3 - statistics: 6949 success size, 1 failure size
reason (InvalidInitialState Established) count 19
tls4 - statistics: 12442 success size, 1 failure size
reason (InvalidInitialState Established) count 68
tls4-new - statistics: 1142 success size, 1 failure size
reason (InvalidInitialState Established) count 1

tls0 has an offending trace (which doesn't parse b4427fd723e11a0f)

---->
35274 traces

*)
