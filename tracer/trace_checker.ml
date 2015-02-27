open Read_trace

open Tls

let cs_mmap file =
  Unix_cstruct.of_fd Unix.(openfile file [O_RDONLY] 0)

let priv, cert =
  let file = cs_mmap "/home/hannes/tls-certs-mirage/openmirage.pem" in
  (X509.PK.of_pem_cstruct1 file, X509.Cert.of_pem_cstruct file)

open Nocrypto
open Nocrypto.Dh
let to_cstruct_sized { p; _ } z =
  Numeric.Z.(to_cstruct_be ~size:(Uncommon.cdiv (bits p) 8) z)

let public_of_secret (({ p; gg; _ } as group), { x }) =
  to_cstruct_sized group (Z.(powm gg x p))

(* pull out initial state *)
let init (trace : trace list) =
  match find_trace (function `StateIn x -> true | _ -> false) trace with
  | Some (`StateIn x) -> x
  | _ -> assert false

let find_out ?packet (trace : trace list) =
  let tst data = Cstruct.len data > 0 in
  let tstt t = match packet with None -> true | Some x when x = t -> true | _ -> false in
  match
    find_trace
      (function `RecordOut (t, d) when tstt t && tst d -> true | _ -> false)
      trace
  with
  | Some (`RecordOut r) -> Some r
  | _ -> None

let find_hs_out t =
  match find_out ~packet:Packet.HANDSHAKE t with
  | Some (_, r) -> r
  | _ -> assert false

let parse_server_hello out =
  let buflen = Reader.parse_handshake_length out in
  let data = Cstruct.sub out 0 (buflen + 4) in
  match Reader.parse_handshake data with
  | Reader.Or_error.Ok Core.ServerHello sh -> sh
  | _ -> assert false

let find_dh_sent (trace : trace list) =
  match
    find_trace
      (function
        | `StateOut st ->
          ( match st.State.handshake.State.machina with
            | State.Server (State.AwaitClientKeyExchange_DHE_RSA _) -> true
            | _ -> false )
        | _ -> false)
      trace
  with
  | Some (`StateOut st) ->
    ( match st.State.handshake.State.machina with
      | State.Server (State.AwaitClientKeyExchange_DHE_RSA (_, dh_sent, _)) ->
        let group, secret = dh_sent in
        Some (group, secret, public_of_secret dh_sent)
      | _ -> None )
  | _ -> None


(* configured is the range (min, max) -- chosen is the one from server hello -- requested the one from client hello  *)
(* sanity: min >= chosen >= max ; requested >= chosen *)
let version_agreed configured chosen requested =
  match Handshake_common.supported_protocol_version configured (Supported chosen) with
  | None -> State.fail (`Error (`NoConfiguredVersion chosen))
  | Some _ ->
    if Core.version_ge requested chosen then
      State.return chosen
    else
      State.fail (`Error (`NoConfiguredVersion chosen))

(* again, chosen better be part of configured -- and also chosen be a mem of requested *)
(* this is slightly weak -- depending on sni / certificate we have to limit the decision *)
let cipher_agreed _certificates configured chosen requested =
  if List.mem chosen configured &&
     List.mem chosen (Utils.filter_map ~f:Ciphersuite.any_ciphersuite_to_ciphersuite requested)
  then
    State.return chosen
  else
    State.fail (`Error (`NoConfiguredCiphersuite [chosen]))

let fixup_initial_state state raw next =
  let server_hello = parse_server_hello raw in
  let dh_sent = match Ciphersuite.ciphersuite_kex server_hello.Core.ciphersuites with
    | Ciphersuite.RSA -> None
    | Ciphersuite.DHE_RSA -> find_dh_sent next
  in
  let config = {
    state.State.handshake.State.config with
    own_certificates = `Single (cert, priv)
  } in
  let choices = State.{
      version = version_agreed config.protocol_versions server_hello.Core.version ;
      cipher = cipher_agreed config.own_certificates config.ciphers server_hello.Core.ciphersuites ;
      random = (fun () -> server_hello.Core.random) ;
      session_id = (fun () -> server_hello.Core.sessionid) ;
      dh_secret = (fun () -> dh_sent)
    }
  in
  let handshake = { state.State.handshake with config } in
  (choices, server_hello.Core.version, { state with handshake })


(* what we should do: *)
(* hello extension normaliser / equivalence -- we might want to pass extension types *)
(* ensure that each RecordOut is normalised! *)
(*   pass through the pending output records *)
(*   when an input comes along: append outputs to pending outputs! *)
(*   when an output comes along: check that it matches the first item *)
(*   check invariants -- at the end out should be empty *)

let rec replay ?choices state = function
  | (`RecordIn (hdr, data))::xs ->
    Printf.printf "record-in %s\n" (Packet.content_type_to_string hdr.Core.content_type) ;
    ( match hdr.Core.content_type with
      | Packet.HANDSHAKE when Cstruct.get_uint8 data 0 = 1 ->
        (* client hello *)
        begin
          let out_raw = find_hs_out xs in
          assert (Cstruct.get_uint8 out_raw 0 = 2) ;
          let choices, version, state = fixup_initial_state state out_raw xs in
          match Engine.handle_tls ~choices state (fixup_in_record hdr data) with
          | `Ok (`Ok state', `Response out, `Data data) ->
            assert (data = None) ;
            ( match out with
              | None -> Printf.printf "out is empty!?\n"
              | Some fst_out' ->
                let raw_out =
                  fixup_in_record
                    { Core.content_type = Packet.HANDSHAKE ; Core.version = Core.Supported version }
                    out_raw
                in
                if not (Uncommon.Cs.equal raw_out fst_out') then
                  (Printf.printf "raw_out" ; Cstruct.hexdump raw_out ;
                   Printf.printf "fst_out'" ; Cstruct.hexdump fst_out' ;
                   assert false) ;
                Printf.printf "first handshake out is the same!\n" ;
                replay ~choices state' xs )
          | `Fail (e, _) -> Printf.printf "sth failed %s\n" (Sexplib.Sexp.to_string_hum (Engine.sexp_of_failure e))
        end
      | _ ->
        ( match Engine.handle_tls ?choices state (fixup_in_record hdr data) with
          | `Ok (st, `Response res, `Data dat) ->
            (match dat with
             | None -> ()
             | Some x -> Printf.printf "received: %s\n" (Cstruct.to_string x)) ;
            ( match st, res with
              | `Ok state', Some out ->
                ( match find_out xs with
                  | Some (t, out_raw) ->
                    let raw_out = fixup_in_record { hdr with Core.content_type = t } out_raw in
                    if not (Uncommon.Cs.equal raw_out out) then
                      (Printf.printf "raw_out" ; Cstruct.hexdump raw_out ;
                       Printf.printf "out" ; Cstruct.hexdump out ) ;
                    assert (Uncommon.Cs.equal raw_out out) ;
                    Printf.printf "handshake out is the same!\n" ;
                    replay ?choices state' xs
                  | None -> Printf.printf "expected a next output!\n" )
              | `Ok state', None ->
                Printf.printf "no out generated!\n" ;
                replay ?choices state' xs
              | `Alert al, _ ->
                Printf.printf "received alerttt %s\n" (Packet.alert_type_to_string al)
            )
          | `Fail _ -> Printf.printf "failed\n" )
    )
  | (`AlertIn alert_in)::_ -> Printf.printf "received alert %s\n" (Sexplib.Sexp.to_string_hum (Core.sexp_of_tls_alert alert_in))
  | (`AlertOut alert_out)::_ -> Printf.printf "sending alert %s\n" (Sexplib.Sexp.to_string_hum (Core.sexp_of_tls_alert alert_out))
  | _::xs -> replay state xs
  | [] -> Printf.printf "sucess!\n"
    (* should do sth useful with state.. *)

let rec mix c s =
  match c, s with
  | [], [] -> []
  | [c], [] ->
    ( match Engine.separate_records c with
      | State.Ok (xs, rest) ->
        assert (Cstruct.len rest = 0) ;
        List.map (fun x -> `RecordIn x) xs )
  | c::cs, s::ss ->
    match Engine.separate_records c, Engine.separate_records s with
    | State.Ok (xs, rest), State.Ok (ys, rest') ->
      assert (Cstruct.len rest = 0) ;
      assert (Cstruct.len rest' = 0) ;
      let c = List.map (fun x -> `RecordIn x) xs in
      let s = List.map (fun (hdr, data) -> `RecordOut (hdr.Core.content_type, data)) ys in
      c @ s @ mix cs ss
    | _ -> assert false

let reconstruct =
  let client = List.map Nocrypto.Uncommon.Cs.of_hex Trace_data.client
  and server = List.map Nocrypto.Uncommon.Cs.of_hex Trace_data.server
  in
  let trace = mix client server in
  let config = Config.server ~ciphers:[`TLS_RSA_WITH_RC4_128_MD5] ~certificates:(`Single (cert, priv)) () in
  let state = Engine.server config in
  (state, trace)

let run dir file pcap =
  Nocrypto.Rng.reseed (Cstruct.create 10);
  match dir, file, pcap with
  | Some dir, _, _ ->
    Printf.printf "not yet implemented\n"
  | None, Some file, _ ->
    let ts, (alert, trace) = load file in
    ( match alert with
      | Some x -> Printf.printf "got alert %s somewhere\n" (Sexplib.Sexp.to_string_hum x)
      | None ->
        let state = init trace in
        replay state trace)
  | None, None, Some _ ->
    let state, trace = reconstruct in
    replay state trace
  | _ -> assert false

let trace_dir = ref None
let trace_file = ref None
let trace_pcap = ref None
let rest = ref []

let usage = "usage " ^ Sys.argv.(0)

let arglist = [
  ("-f", Arg.String (fun f -> trace_file := Some f), "trace file");
  ("-d", Arg.String (fun d -> trace_dir := Some d), "trace directory");
  ("-p", Arg.String (fun p -> trace_pcap := Some p), "trace pcap");
]

let () =
  Arg.parse arglist (fun x -> rest := x :: !rest) usage ;
  run !trace_dir !trace_file !trace_pcap
