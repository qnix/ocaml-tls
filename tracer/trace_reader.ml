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
  | None -> Printf.printf "error loading %s\n" file
  | Some (Some time, traces) ->
    let timestring = timestamp_to_string time in
    Printf.printf "trace from %s with %d elements\n" timestring (List.length traces) ;
    analyse_and_print traces
  | Some (None, traces) ->
    Printf.printf "trace (no time) with %d elements\n" (List.length traces) ;
    analyse_and_print traces

let () =
  match Sys.argv with
  | [| _ ; file |] -> handle file
