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

let find_user_agent buf =
  let str = Cstruct.to_string buf in
  let find_re (re, l) =
    try
      let idx = Str.search_forward re str 0 in
      let start = succ (succ (idx + l)) in
      let nl = try String.index_from str start '\r' with Not_found -> String.length str in
      Some (String.sub str start (nl - start))
    with
      _ -> None
  in
  find_re user_agent

let rec analyse acc = function
  | (`ApplicationDataIn s)::xs -> analyse (s :: acc) xs
  | _::xs -> analyse acc xs
  | [] -> List.rev acc

let analyse_trace name trace =
  let rec go p = function
    | [] -> None
    | x::_ when p x -> Some x
    | _::xs -> go p xs
  in
  let server_hello =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 2 in
    let sh = go (function `RecordOut (Packet.HANDSHAKE, d) when tst d -> true | _ -> false) trace in
    match sh with
    | Some (`RecordOut (_, sh)) ->
      let buflen = Reader.parse_handshake_length sh in
      let data = Cstruct.sub sh 0 (buflen + 4) in
      Reader.parse_handshake data
    | _ -> assert false
  in
  let appdata = analyse [] trace in
  let ua = find_user_agent (Nocrypto.Uncommon.Cs.concat appdata) in
  match server_hello with
  | Reader.Or_error.Ok Core.ServerHello sh ->
    Some (sh.Core.version, sh.Core.ciphersuites, ua)
  | _ -> Printf.printf "problem while parsing sth in %s\n" name ; None

let analyse_success hashtbl =
  (* key is name, value is (timestamp, trace) *)
  let stats, uas =
    Hashtbl.fold (fun name (_, trace) (s, ua) ->
        match analyse_trace name trace with
        | Some (v, c, u) -> ((v, c) :: s, u :: ua)
        | None -> (s, ua))
      hashtbl ([], [])
  in
  let s_stats = Hashtbl.create 9 in
  let sua = List.combine stats uas in
  List.iter (fun (s, ua) ->
      if Hashtbl.mem s_stats s then
        let cnt, uas = Hashtbl.find s_stats s in
        let uas = if List.mem ua uas then uas else ua :: uas in
        Hashtbl.replace s_stats s (succ cnt, uas)
      else
        Hashtbl.add s_stats s (1, [ua])) sua ;
  Hashtbl.iter (fun (ver, cip) (v, ua) ->
      Printf.printf "%d %s %s used by %d\n" v (Printer.tls_version_to_string ver) (Ciphersuite.ciphersuite_to_string cip) (List.length (Utils.filter_map ~f:(fun x -> x) ua)))
    s_stats ;
  let uas = Hashtbl.fold (fun k (_, uas) acc ->
      let rec maybe_add ac xs =
        match xs with
        | [] -> ac
        | None::xs -> maybe_add ac xs
        | (Some x)::xs when List.mem x ac -> maybe_add ac xs
        | (Some x)::xs -> maybe_add (x :: ac) xs
      in
      maybe_add acc uas) s_stats []
  in
  Printf.printf "%d user-agents:\n%s\n" (List.length uas) (String.concat "\n" uas)


let analyse_protocol_version trace =
  let client_hello =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 1 in
    let ch = find_trace (function `RecordIn (hdr, data) -> hdr.content_type = Packet.HANDSHAKE && tst data | _ -> false) trace in
    match ch with
    | Some (`RecordIn (_, ch)) -> Reader.parse_handshake ch
    | _ -> assert false
  in
  match client_hello with
  | Reader.Or_error.Ok Core.ClientHello ch -> ch.Core.version
  | _ -> assert false


let rec unique acc = function
  | [] -> acc
  | x::xs when List.mem x acc -> unique acc xs
  | x::xs -> unique (x :: acc) xs

let analyse_alerts hashtbl =
  (* err -> (timestamp, name, traces) *)
  let version_fails =
    Hashtbl.find hashtbl (Core.sexp_of_tls_alert (Packet.FATAL, Packet.PROTOCOL_VERSION))
  in
  let versions = List.map analyse_protocol_version (List.map (fun (_, _, x) -> x) version_fails) in
  let name_versions = List.combine version_fails versions in
  let unsupported = List.filter (fun (_, v) -> match v with
      | Core.SSL_3 -> true
      | Core.TLS_1_X _ -> true
      | _ -> false) name_versions
  in
  let single = unique [] (List.map snd unsupported) in
  Printf.printf "%d unsupported versions: %s\n"
    (List.length unsupported)
    (String.concat ", " (List.map Printer.tls_any_version_to_string single)) ;
  let supported = List.filter (fun (_, v) -> match v with
      | Core.Supported v -> true
      | _ -> false) name_versions
  in
  Printf.printf "%d supported versions (other failure)\n" (List.length supported)

let run dir file =
  match dir, file with
  | Some dir, _ ->
    let successes = Hashtbl.create 100
    and alerts = Hashtbl.create 100
    and early_alerts = Hashtbl.create 100
    and alert_in = Hashtbl.create 100
    and failures = Hashtbl.create 100
    in
    let suc (name, (ts, (alert, (traces : trace list)))) =
      let len = List.length traces in
      if List.exists (function `AlertIn x -> true | _ -> false) traces then
        let alert = List.filter (function `AlertIn x -> true | _ -> false) traces in
        assert (List.length alert = 1) ;
        let x = match alert with
          | [`AlertIn x] -> x
          | _ -> assert false
        in
        let x = Core.sexp_of_tls_alert x in
        if Hashtbl.mem alert_in x then
          let ele = Hashtbl.find alert_in x in
          Hashtbl.replace alert_in x ((ts, name) :: ele)
        else
          Hashtbl.add alert_in x [(ts, name)]
      else
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
          if Hashtbl.mem early_alerts x then
            let ele = Hashtbl.find early_alerts x in
            Hashtbl.replace early_alerts x ((ts, name) :: ele)
          else
            Hashtbl.add early_alerts x [(ts, name)]
        else if Hashtbl.mem alerts x then
          let ele = Hashtbl.find alerts x in
          Hashtbl.replace alerts x ((ts, name) :: ele)
        else
          Hashtbl.add alerts x [(ts, name)]
    and fails (name, e) =
      if Hashtbl.mem failures e then
        let ele = Hashtbl.find failures e in
        Hashtbl.replace failures e (name :: ele)
      else
        Hashtbl.add failures e [name]
    in

    let success, fail = load_dir dir in
    List.iter suc success ;
    List.iter fails fail ;

    Printf.printf "success size %d\n" (Hashtbl.length successes) ;
(*    Hashtbl.iter (fun k (ts, trace) ->
        Printf.printf "success trace length %d count %d\n" k v)
      successes ; *)
    Hashtbl.iter (fun k v ->
        Printf.printf "alert in %s count %d\n" (Sexplib.Sexp.to_string_hum k) (List.length v))
      alert_in ;
    Hashtbl.iter (fun k v ->
        Printf.printf "alert %s count %d\n" (Sexplib.Sexp.to_string_hum k) (List.length v))
      alerts ;
    Hashtbl.iter (fun k v ->
        Printf.printf "early alert %s count %d\n" (Sexplib.Sexp.to_string_hum k) (List.length v))
      early_alerts ;
    analyse_success successes
(*    Hashtbl.iter (fun k v ->
        Printf.printf "reason %s count %d\n" (Sexplib.Sexp.to_string_hum (sexp_of_error k)) (List.length v))
      failures *)

  | None, Some file ->
    (try (let ts, (alert, traces) = load file in
          match alert with
          | Some alert ->
            Printf.printf "trace from %s, alert %s (%d traces)\n"
              ts (Sexplib.Sexp.to_string_hum alert) (List.length traces)
          | None ->
            Printf.printf "trace from %s, loaded %d traces\n" ts (List.length traces) ;
            let hash = Hashtbl.create 1 in
            Hashtbl.add hash file (ts, traces) ;
            analyse_success hash)
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
