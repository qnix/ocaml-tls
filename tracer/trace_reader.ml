open Read_trace

open Tls

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

let analyse_trace name trace =
  let rec goin p = function
    | [] -> None
    | x::_ when p x -> Some x
    | _::xs -> goin p xs
  in
  let rec goout p = function
    | [] -> None
    | x::_ when p x -> Some x
    | _::xs -> goout p xs
  in
  let client_hello =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 1 in
    let ch = goin (function `RecordIn (tls_hdr, d) when tls_hdr.Core.content_type = Packet.HANDSHAKE && tst d -> true | _ -> false) trace in
    match ch with
    | Some (`RecordIn (_, ch)) -> Reader.parse_handshake ch
    | _ -> assert false
  in
  let server_hello =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 2 in
    let sh = goout (function `RecordOut (Packet.HANDSHAKE, d) when tst d -> true | _ -> false) trace in
    match sh with
    | Some (`RecordOut (_, sh)) ->
      let buflen = Reader.parse_handshake_length sh in
      let data = Cstruct.sub sh 0 (buflen + 4) in
      Reader.parse_handshake data
    | _ -> assert false
  in
  match client_hello, server_hello with
  | Reader.Or_error.Ok (Core.ClientHello ch), Reader.Or_error.Ok Core.ServerHello sh ->
    Some ((sh.Core.version, ch.Core.version), ch.Core.ciphersuites, sh.Core.ciphersuites)
  | _ -> Printf.printf "problem while parsing sth in %s\n" name ; None

let analyse_success hashtbl =
  (* key is name, value is (timestamp, trace) *)
  let versions, client_cs, server_cs =
    Hashtbl.fold (fun name (_, trace) (vacc, cacc, scacc) ->
        match analyse_trace name trace with
        | Some (vs, ccs, scs) -> (vs :: vacc, ccs :: cacc, scs :: scacc)
        | None -> (vacc, cacc, scacc))
      hashtbl ([], [], [])
  in
  let s_versions = Hashtbl.create 9 in
  List.iter (fun x ->
      if Hashtbl.mem s_versions x then
        let ele = Hashtbl.find s_versions x in
        Hashtbl.replace s_versions x (succ ele)
      else
        Hashtbl.add s_versions x 1) versions ;
  Hashtbl.iter (fun (s, c) v ->
      Printf.printf "%s used (%s proposed) %d times\n" (Printer.tls_version_to_string s) (Printer.tls_any_version_to_string c) v)
    s_versions ;
  let s_ciphers = Hashtbl.create 9 in
  List.iter (fun x ->
      if Hashtbl.mem s_ciphers x then
        let ele = Hashtbl.find s_ciphers x in
        Hashtbl.replace s_ciphers x (succ ele)
      else
        Hashtbl.add s_ciphers x 1) server_cs ;
  Hashtbl.iter (fun c v ->
      Printf.printf "%s used %d times\n" (Ciphersuite.ciphersuite_to_string c) v)
    s_ciphers
(*  let c_ciphers = Hashtbl.create 9 in
  List.iter (fun x ->
      if Hashtbl.mem c_ciphers x then
        let ele = Hashtbl.find c_ciphers x in
        Hashtbl.replace c_ciphers x (succ ele)
      else
        Hashtbl.add c_ciphers x 1) client_cs ;
  Hashtbl.iter (fun c v ->
      Printf.printf "%d clients proposed %s\n" v (String.concat ", " (List.map Packet.any_ciphersuite_to_string c)))
    c_ciphers *)

let handle file =
  match load file with
  | None -> Printf.printf "error loading %s\n" file ; None
  | Some (Some time, (alert, traces)) ->
    let timestring = timestamp_to_string time in
    (* Printf.printf "trace from %s with %d elements\n" timestring (List.length traces) ; *)
    (* analyse_and_print traces *)
    Some (timestring, alert, traces)
  | Some (None, (alert, traces)) ->
    (* Printf.printf "trace (no time) with %d elements\n" (List.length traces) ; *)
    (* analyse_and_print traces *)
    Some ("", alert, traces)


let run dir file =
  match dir, file with
  | Some file, _ ->
    let dirent = Unix.opendir file in
    Unix.readdir dirent ; Unix.readdir dirent ;
    let filen = ref (try Some (Unix.readdir dirent) with End_of_file -> None) in
    let successes = Hashtbl.create 100
    and alerts = Hashtbl.create 100
    and failures = Hashtbl.create 100
    in
    let suc (ts, alert, traces) name =
      let len = List.length traces in
      match alert with
      | None ->
        if len < 10 then
          (* Printf.printf "%d elements - broken non-alert trace at %s ?\n" len name *)
          ()
        else if Hashtbl.mem successes name then
          (* let ele = Hashtbl.find successes name in
             Hashtbl.replace successes name ele *)
          assert false
        else
          Hashtbl.add successes name (ts, traces)
      | Some x ->
        if len < 3 then
          (* Printf.printf "%d elements - broken alert trace at %s ?\n" len name *)
          ()
        else if Hashtbl.mem alerts x then
          let ele = Hashtbl.find alerts x in
          Hashtbl.replace alerts x ((ts, name) :: ele)
        else
          Hashtbl.add alerts x [(ts, name)]
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
    Printf.printf "success size %d\n" (Hashtbl.length successes) ;
(*    Hashtbl.iter (fun k (ts, trace) ->
        Printf.printf "success trace length %d count %d\n" k v)
      successes ; *)
    Hashtbl.iter (fun k v ->
        Printf.printf "alert %s count %d\n" (Sexplib.Sexp.to_string_hum k) (List.length v))
      alerts ;
    analyse_success successes
(*    Hashtbl.iter (fun k v ->
        Printf.printf "reason %s count %d\n" (Sexplib.Sexp.to_string_hum (sexp_of_error k)) (List.length v))
      failures *)
  | None, Some file ->
    (try (match handle file with
         | Some (ts, Some alert, traces) ->
           Printf.printf "trace from %s, alert %s (%d traces)\n" ts (Sexplib.Sexp.to_string_hum alert) (List.length traces)
         | Some (ts, None, traces) ->
           Printf.printf "trace from %s, loaded %d traces\n" ts (List.length traces) ;
           let hash = Hashtbl.create 1 in
           Hashtbl.add hash file (ts, traces) ;
           analyse_success hash
         | None -> Printf.printf "couldn't load any traces..." )
     with
       Trace_error e -> Printf.printf "problem %s\n" (Sexplib.Sexp.to_string_hum (sexp_of_error e)))
  | _ -> assert false


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
