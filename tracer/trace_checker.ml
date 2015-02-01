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

let replay (trace : trace list) =
  let rec go p = function
    | [] -> None
    | x::_ when p x -> Some x
    | _::xs -> go p xs
  in
  let initial_state = go (function `StateIn x -> true | _ -> false) trace
  in
  let client_hello =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 1 in
    let ch = go (function `RecordIn (tls_hdr, d) when tls_hdr.Core.content_type = Packet.HANDSHAKE && tst d -> true | _ -> false) trace in
    match ch with
    | Some (`RecordIn r) -> r
    | _ -> assert false
  in
  let fst_out =
    let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 2 in
    let sh = go (function `RecordOut (Packet.HANDSHAKE, d) when tst d -> true | _ -> false) trace in
    match sh with
    | Some (`RecordOut (_, out)) -> out
    | _ -> assert false
  in
  let server_hello =
    let buflen = Reader.parse_handshake_length fst_out in
    Cstruct.sub fst_out 0 (buflen + 4)
  in
  match initial_state, Reader.parse_handshake server_hello with
  | Some (`StateIn st), Reader.Or_error.Ok Core.ServerHello sh ->
    let dh_sent = match Ciphersuite.ciphersuite_kex sh.Core.ciphersuites with
      | Ciphersuite.RSA -> None
      | Ciphersuite.DHE_RSA ->
        let awaitckex = go (function `StateOut st -> (match st.State.handshake.State.machina with
              State.Server (State.AwaitClientKeyExchange_DHE_RSA _) -> true | _ -> false) | _ -> false) trace in
        match awaitckex with
        | Some (`StateOut st) -> match st.State.handshake.State.machina with
          | State.Server (State.AwaitClientKeyExchange_DHE_RSA (_, dh_sent, _)) -> Some (dh_sent, public_of_secret dh_sent)
    in
    let valid = State.{ version = Some sh.Core.version ; cipher = Some sh.Core.ciphersuites ; server_random = Some sh.Core.random ; dh_sent } in
    let config = { st.handshake.config with own_certificates = `Single (cert, priv) } in
    let handshake = { st.handshake with config } in
    let st = { st with handshake } in
    match Engine.handle_raw_record ~valid st client_hello with
    | Core.Error e -> Printf.printf "sth failed %s\n" (Packet.alert_type_to_string e)
    | Core.Ok (st', out, data, err) ->
      assert (data = None) ; assert (err = `No_err) ;
      match out with
      | [] -> Printf.printf "out is empty!?\n"
      | (_, fst_out')::_ ->
        assert (Uncommon.Cs.equal fst_out fst_out') ;
        Printf.printf "first handshake out is the same!\n"


let run dir file =
  Nocrypto.Rng.reseed (Cstruct.create 10);
  match dir, file with
  | Some dir, _ ->
    Printf.printf "not yet implemented\n"
  | None, Some file ->
    let ts, (alert, trace) = load file in
    ( match alert with
      | Some x -> Printf.printf "got alert %s somewhere\n" (Sexplib.Sexp.to_string_hum x)
      | None -> replay trace)
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
