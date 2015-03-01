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
  | Some p -> p
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


let dbg_cc c = Printf.printf "cc %s\n" (Sexplib.Sexp.to_string_hum (State.sexp_of_crypto_state c))

let dbg_al al = Sexplib.Sexp.to_string_hum (Core.sexp_of_tls_alert al)

let dbg_fail f = Sexplib.Sexp.to_string_hum (Engine.sexp_of_failure f)

let normalise crypt ver data =
  match Engine.separate_records data with
  | State.Ok (xs, rest) ->
    assert (Cstruct.len rest = 0) ;
    (* Printf.printf "now trying to decrypt %d packets\n" (List.length xs) ; *)
    let e, acc = List.fold_left (fun (enc, acc) (hdr, data) ->
        (* dbg_cc enc; Cstruct.hexdump data ; *)
        match Engine.decrypt ver enc hdr.Core.content_type data with
        | State.Ok (enc, d) ->
          (* Printf.printf "dec is %d\n" (Cstruct.len d) ; *)
          (enc, d :: acc)
        | State.Error e ->
          if hdr.Core.content_type == Packet.CHANGE_CIPHER_SPEC (* && Cstruct.len data = 1 *) then
            (* we're a bit unlucky, but let's pretend to be good *)
            let ccs = Writer.assemble_change_cipher_spec in
            (enc, ccs :: acc)
          else
            (Printf.printf "dec failed %s\n" (dbg_fail e) ;
             assert false))
        (crypt, []) xs
    in
    (List.rev acc, e)
  | _ -> assert false

(* what we should do: *)
(* hello extension normaliser / equivalence -- we might want to pass extension types *)
(* what happens if handle didn't produce an output, but record-out came along? --
     need a way to passthrough / match these as well! *)
(* also, alerts/failure traces *)
(* while separate records is a good start, we need separate handshake here as well! *)
(* eaf3996a47b6fcf2 has reneg! *)
(* structural equality, rather than byte equality! *)
let rec replay ?choices prev_state state pending_out t =
  let handle_and_rec ?choices state hdr data xs =
    match Engine.handle_tls ?choices state (fixup_in_record hdr data) with
    | `Ok (`Ok state', `Response out, `Data data) ->
      ( match data with
        | None -> ()
        | Some x -> Printf.printf "received data %s\n" (Cstruct.to_string x) ) ;
      let pending = match out with
        | None -> (* Printf.printf "empty out!?\n"; *) pending_out
        | Some out ->
          Printf.printf "output from handle_tls, normalising\n" ;
          let ver = state.State.handshake.State.protocol_version in
          let data, _ = normalise state.encryptor ver out in
          pending_out @ data
      in
      let prev = match hdr.Core.content_type with
        | Packet.CHANGE_CIPHER_SPEC -> state'
        | _ -> prev_state
      in
      replay ?choices prev state' pending xs
    | `Fail (e, _) ->
      (* in the trace we better have an alert as well! *)
      Printf.printf "sth failed %s\n" (dbg_fail e) ;
      assert false
  in

  match t with
  | (`RecordIn (hdr, data))::xs ->
    Printf.printf "record-in %s\n" (Packet.content_type_to_string hdr.Core.content_type) ;
    ( match hdr.Core.content_type with
      | Packet.HANDSHAKE ->
        let enc = fixup_in_record hdr data in
        let ver = state.State.handshake.State.protocol_version in
        let dec, _ = normalise state.State.decryptor ver enc in
        ( match dec with
          | x::_ when Cstruct.get_uint8 x 0 = 1->
            (* Printf.printf "decrypted (%d):" (Cstruct.len x) ; Cstruct.hexdump x ; *)
            let t, out = find_hs_out xs in
            let out_data = Writer.assemble_hdr ver (t, out) in
            ( match normalise prev_state.State.encryptor ver out_data with
              | x::_,_ ->
                assert (Cstruct.get_uint8 x 0 = 2) ;
                let choices, version, state = fixup_initial_state state x xs in
                handle_and_rec ~choices state hdr data xs
              | _ -> assert false )
          | _ -> handle_and_rec ?choices state hdr data xs )
      | _ -> handle_and_rec ?choices state hdr data xs )
  | (`RecordOut (t, data))::xs ->
    let rec cmp_data expected rcvd =
      match expected, rcvd with
      | [], [] -> []
      | [], _ -> assert false
      | x::xs, y::ys ->
        (* Printf.printf "comparing out %d vs %d\n" (Cstruct.len x) (Cstruct.len y) ; *)
        if not (Nocrypto.Uncommon.Cs.equal x y) then
          (Printf.printf "mismatch! (computed)" ; Cstruct.hexdump x ; Printf.printf "stored" ; Cstruct.hexdump y ;
           assert false) ;
        cmp_data xs ys
      | xs, [] -> xs
    in
    let version = state.handshake.protocol_version in
    let data = Writer.assemble_hdr version (t, data) in
    Printf.printf "record out, normalising\n" ;
    let ver = state.State.handshake.State.protocol_version in
    let data, e = normalise prev_state.encryptor ver data in
    let leftover = cmp_data pending_out data in
    replay ?choices { prev_state with State.encryptor = e } state leftover xs
  | (`AlertIn alert_in)::_ -> Printf.printf "received alert %s\n" (dbg_al alert_in)
  | (`AlertOut alert_out)::_ -> Printf.printf "sending alert %s\n" (dbg_al alert_out)
  | (`StateIn s)::xs -> replay ?choices { prev_state with State.encryptor = s.State.encryptor } state pending_out xs
  | _::xs -> replay ?choices prev_state state pending_out xs
  | [] ->
    assert (List.length pending_out = 0) ;
    Printf.printf "sucess!\n"
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

let doit (name, (ts, (alert, trace))) =
  match alert with
  | None ->
    Printf.printf "file %s: " name;
    let state = init trace in
    replay state state [] trace
  | Some _ -> ()

let run dir file pcap =
  Nocrypto.Rng.reseed (Cstruct.create 1);
  match dir, file, pcap with
  | Some dir, _, _ ->
    let success, fail, skip = load_dir dir in
    List.iter doit success
  | None, Some file, _ ->
    let ts, (alert, trace) = load file in
    ( match alert with
      | Some x -> Printf.printf "got alert %s somewhere\n" (Sexplib.Sexp.to_string_hum x)
      | None ->
        let state = init trace in
        replay state state [] trace)
  | None, None, Some _ ->
    let state, trace = reconstruct in
    replay state state [] trace
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
