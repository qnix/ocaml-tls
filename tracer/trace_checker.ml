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

let find_server_hello (trace : trace list) =
  let tst data = Cstruct.len data > 0 && Cstruct.get_uint8 data 0 = 2 in
  match
    find_trace
      (function `RecordOut (Packet.HANDSHAKE, d) when tst d -> true | _ -> false)
      trace
  with
  | Some (`RecordOut (_, out)) -> out
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
        Some (dh_sent, public_of_secret dh_sent)
      | _ -> None )
  | _ -> None

let rec replay state = function
  | (`RecordIn (hdr, data))::xs when hdr.Core.content_type = Packet.HANDSHAKE ->
    ( match Cstruct.get_uint8 data 0 with
      | 1 (* client hello *) ->
        let next_out_raw = find_server_hello xs in
        let server_hello = parse_server_hello next_out_raw in
        let dh_sent = match Ciphersuite.ciphersuite_kex server_hello.Core.ciphersuites with
          | Ciphersuite.RSA -> None
          | Ciphersuite.DHE_RSA -> find_dh_sent xs
        in
        let valid = State.{ version = Some server_hello.Core.version ;
                            cipher = Some server_hello.Core.ciphersuites ;
                            server_random = Some server_hello.Core.random ;
                            dh_sent } in
        let config = {
          state.State.handshake.State.config with
            own_certificates = `Single (cert, priv)
        } in
        let handshake = { state.State.handshake with config } in
        let state = { state with handshake } in
    match Engine.handle_raw_record ~valid state (hdr, data) with
    | State.Ok (st', out, data, err) ->
      assert (data = None) ; assert (err = `No_err) ;
      ( match out with
        | [] -> Printf.printf "out is empty!?\n"
        | (_, fst_out')::_ ->
          assert (Uncommon.Cs.equal next_out_raw fst_out') ;
          Printf.printf "first handshake out is the same!\n"  )
    | State.Error e -> Printf.printf "sth failed %s\n" (Sexplib.Sexp.to_string_hum (Engine.sexp_of_failure e))
    )
  | (`RecordOut (Packet.HANDSHAKE, rec_out))::xs -> Printf.printf "should handle record out!\n"
  | _::xs -> replay state xs
  | [] -> Printf.printf "sucess!\n"
  (* | `AlertIn alert_in ->
     | `AlertOut alert_out -> *)
    (* should do sth useful with state.. *)

let run dir file =
  Nocrypto.Rng.reseed (Cstruct.create 10);
  match dir, file with
  | Some dir, _ ->
    Printf.printf "not yet implemented\n"
  | None, Some file ->
    let ts, (alert, trace) = load file in
    ( match alert with
      | Some x -> Printf.printf "got alert %s somewhere\n" (Sexplib.Sexp.to_string_hum x)
      | None ->
        let state = init trace in
        replay state trace)
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
