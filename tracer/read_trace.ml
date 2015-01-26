(* reading traces back in from those created in TLS *)

open Sexplib
open Sexplib.Sexp
open Sexplib.Conv

open Tls

(* why is this so messy? because tls-0.1.0 (which we used to produce traces) uses
   different data types! Also, the trace is only partial (esp cipher_state is not
   marshalled to disk). In here, we only read those traces (and make them complete!). *)

(* we currently focus on traces recorded by the server, thus some partial pattern matches
   (don't expect this to work for a client trace) *)

let session_of_server s =
  let open State in
  match s with
  | AwaitClientHello -> None
  | AwaitClientHelloRenegotiate -> None
  | AwaitClientCertificate_RSA (session_data, _) -> Some session_data
  | AwaitClientCertificate_DHE_RSA (session_data, _, _) -> Some session_data
  | AwaitClientKeyExchange_RSA (session_data, _) -> Some session_data
  | AwaitClientKeyExchange_DHE_RSA (session_data, _, _) -> Some session_data
  | AwaitClientCertificateVerify (session_data, _, _, _) -> Some session_data
  | AwaitClientChangeCipherSpec (session_data, _, _, _) -> Some session_data
  | AwaitClientFinished (session_data, _) -> Some session_data
  | Established -> None

let session_of_state = function
  | State.Server x -> session_of_server x
  | _              -> None

let session = function
  | None -> Handshake_common.empty_session
  | Some x -> match session_of_state x.State.handshake.State.machina with
    | None -> Handshake_common.empty_session
    | Some x -> x

let version = function
  | None -> Core.TLS_1_0
  | Some x -> x.State.handshake.State.protocol_version

type tls_ver =
    SSL_3 | TLS_1_0 | TLS_1_1 | TLS_1_2 | TLS_1_X of (int * int) with sexp

let tls_ver_to_any_version = function
  | SSL_3 -> Core.SSL_3
  | TLS_1_0 -> Core.(Supported TLS_1_0)
  | TLS_1_1 -> Core.(Supported TLS_1_1)
  | TLS_1_2 -> Core.(Supported TLS_1_2)
  | TLS_1_X (3, m) -> Core.TLS_1_X m
  | TLS_1_X _ -> assert false

open Sexp_ext

type hs_params = {
  server_random  : Cstruct_s.t ;
  client_random  : Cstruct_s.t ;
  client_version : tls_ver ;
  cipher         : Ciphersuite.ciphersuite
} with sexp

let conv_hs_params sess data =
  let hs_params = hs_params_of_sexp data in
  { sess with
    State.server_random = hs_params.server_random ;
    State.client_random = hs_params.client_random ;
    State.client_version = tls_ver_to_any_version hs_params.client_version ;
    State.ciphersuite = hs_params.cipher }

type cs =
  | Random
  | Iv of Cstruct_s.t
  | Stream

let sexp_of_old_cs = function
  | List [ Atom "<cbc-state>" ; Atom "Random_iv" ] -> Random
  | List [ Atom "<cbc-state>" ; List [ Atom "Iv" ; iv ] ] -> Iv (Cstruct_s.t_of_sexp iv)
  | Atom "<stream-state>" -> Stream

let sexp_of_old_cc s =
  match
    List.fold_left (fun (seq, cipher, mac) x -> match x with
        | List [ Atom "sequence" ; seq ] -> (Some (int64_of_sexp seq), cipher, mac)
        | List [ Atom "cipher_st" ; cs ] -> (seq, Some (sexp_of_old_cs cs), mac)
        | List [ Atom "mac" ; mac ] -> (seq, cipher, Some (Cstruct_s.t_of_sexp mac))
      ) (None, None, None) s
  with
  | Some s, Some c, Some m -> (s, c, m)
  | _ -> assert false

let sexp_of_old_cc_option = function
  | List [] -> None
  | List [ List xs ] -> Some (sexp_of_old_cc xs)

let rec find_ccs = function
  | [] -> assert false
  | x::xs ->
    ( match x.State.handshake.State.machina with
      | State.Server (State.AwaitClientChangeCipherSpec (_, cc, sc, _)) -> (cc, sc)
      | _ -> find_ccs xs )
  | _::xs -> find_ccs xs

let cc_checker old_cc new_cc =
  let sequence, iv, mac = sexp_of_old_cc old_cc in
  assert (new_cc.State.sequence = sequence) ;
  match new_cc.State.cipher_st with
  | State.Stream s ->
    assert (iv = Stream) ;
    assert (Nocrypto.Uncommon.Cs.equal s.State.hmac_secret mac)
  | State.CBC c ->
    assert (Nocrypto.Uncommon.Cs.equal c.State.hmac_secret mac) ;
    match c.State.iv_mode, iv with
    | State.Iv x, Iv y -> assert (Nocrypto.Uncommon.Cs.equal x y)
    | State.Random_iv, Random -> ()
    | _ -> assert false

let conv_server_handshake maybe_state = function
  | Atom "AwaitClientHello" -> State.AwaitClientHello
  | List [ Atom "AwaitClientKeyExchange_DHE_RSA" ; hs ; dh ; log ] ->
    let session_data = session maybe_state in
    let sess = conv_hs_params session_data hs in
    State.AwaitClientKeyExchange_DHE_RSA (sess, State.dh_sent_of_sexp dh, State.hs_log_of_sexp log)
  | List [ Atom "AwaitClientKeyExchange_RSA" ; hs ; log ] ->
    let session_data = session maybe_state in
    let sess = conv_hs_params session_data hs in
    State.AwaitClientKeyExchange_RSA (sess, State.hs_log_of_sexp log)
  | List [ Atom "AwaitClientChangeCipherSpec" ; List ccc ; List scc ; ms ; log ] ->
    let master_secret = Cstruct_s.t_of_sexp ms in
    let session_data = session maybe_state in
    let session = { session_data with State.master_secret = master_secret } in
    let sc, cc = Handshake_crypto.make_context
        session.State.ciphersuite
        (version maybe_state)
        master_secret
        session.State.server_random
        session.State.client_random
    in
    cc_checker ccc cc ; cc_checker scc sc ;
    State.AwaitClientChangeCipherSpec (session, cc, sc, State.hs_log_of_sexp log)
  | List [ Atom "AwaitClientFinished" ; ms ; log ] ->
    let session = session maybe_state in
    State.AwaitClientFinished (session, State.hs_log_of_sexp log)
  | Atom "Established" -> State.Established

let conv_machina maybe_state = function
  | List [ Atom "Server" ; xs ] -> State.Server (conv_server_handshake maybe_state xs)

(* we have to transform ancient things to more recent sexps *)
let conv_config = function
  | List [ Atom "use_rekeying" ; reneg ] ->
    List [ Atom "use_reneg" ; reneg ]
  | List [ Atom "requre_sec_rek" ; reneg ] ->
    List [ Atom "secure_reneg" ; reneg ]
  | List [ Atom "validator" ; x ] ->
    List [ Atom "authenticator" ; x ]
  | List [ Atom "certificate" ; x ] ->
    List [ Atom "certificates" ; x ]
  | List [ Atom "hashes" ; List hashes ] ->
    List [ Atom "hashes" ; List (List.map (function Atom "SHA" -> Atom "SHA1" | x -> x) hashes) ]
  | x -> x

let conv_handshake maybe_state = function
  | List eles ->
    match
      List.fold_left (fun (session, ver, machina, config, hs_frag) ele ->
          match ele with
          | List [ Atom "version" ; x ] -> (session, Some (Core.tls_version_of_sexp x), machina, config, hs_frag)
          | List [ Atom "reneg" ; x ] -> (* TODO: needs to be injected into session_data... *) (session, ver, machina, config, hs_frag)
          | List [ Atom "machina" ; x ] -> (session, ver, Some (conv_machina maybe_state x), config, hs_frag)
          | List [ Atom "config" ; List cfgs ] -> (session, ver, machina, Some (Config.config_of_sexp (List (List.map conv_config cfgs))), hs_frag)
          | List [ Atom "hs_fragment" ; x ] -> (session, ver, machina, config, Some (Cstruct_s.t_of_sexp x)))
        (Some [] (* TODO: fix me *), None, None, None, None) eles
    with
    | Some session, Some protocol_version, Some machina, Some config, Some hs_fragment ->
      State.{ session ; protocol_version ; machina ; config ; hs_fragment }
    | _ -> assert false


let conv_cst mac old cst =
  match old, cst with
  | State.Stream x, Stream ->
    assert (Nocrypto.Uncommon.Cs.equal x.State.hmac_secret mac) ;
    State.Stream x
  | State.CBC c, Random ->
    assert (Nocrypto.Uncommon.Cs.equal c.State.hmac_secret mac) ;
    assert (c.State.iv_mode = State.Random_iv) ;
    old
  | State.CBC c, Iv iv ->
    assert (Nocrypto.Uncommon.Cs.equal c.State.hmac_secret mac) ;
    assert (not (c.State.iv_mode = State.Random_iv)) ;
    (State.CBC { c with State.iv_mode = State.Iv iv })

let conv_cc states last proj sexp =
  match sexp_of_old_cc_option sexp with
  | None -> None
  | Some (sequence, cipher_state, mac) ->
    match last with
    | Some x ->
      let st = conv_cst mac x.State.cipher_st cipher_state in
      Some { x with State.sequence = sequence ; State.cipher_st = st }
    | None ->
      let cc = find_ccs states in
      let cc = proj cc in
      let st = conv_cst mac cc.State.cipher_st cipher_state in
      Some { State.sequence = sequence ; State.cipher_st = st }

let conv_state maybe_st all = function
  | List xs ->
    match
      List.fold_left (fun (hs, dec, enc, frag) x -> match x with
          | List [ Atom "handshake" ; xs ] ->
            let hs = conv_handshake maybe_st xs in
            (Some hs, dec, enc, frag)
          | List [ Atom "decryptor" ; xs ] ->
            let last = match maybe_st with
              | None -> None
              | Some x -> x.State.decryptor
            in
            let dec = conv_cc all last snd xs in
            (hs, Some dec, enc, frag)
          | List [ Atom "encryptor" ; xs ] ->
            let last = match maybe_st with
              | None -> None
              | Some x -> x.State.encryptor
            in
            let enc = conv_cc all last fst xs in
            (hs, dec, Some enc, frag)
          | List [ Atom "fragment" ; xs ] -> (hs, dec, enc, Some (Cstruct_s.t_of_sexp xs)) )
        (None, None, None, None) xs
    with
    | Some handshake, Some decryptor, Some encryptor, Some fragment ->
      State.{ handshake ; decryptor ; encryptor ; fragment }
    | _ -> assert false

let process_sexp acc x =
  let top = match acc with
    | [] -> None
    | x::_ -> Some x
  in
  match x with
  | List [ Atom "state-in" ; xs ] ->
    Printf.printf "got state in\n" ;
    let state = conv_state top acc xs in
    state :: acc
  | List [ Atom "state-out" ; xs ] ->
    Printf.printf "got state out\n" ;
    let state = conv_state top acc xs in
    state :: acc
  | List [ Atom x ; xs ] -> Printf.printf "gotx %s\n" x ; acc
  | xs -> Printf.printf "unexpected\n" ; acc

let process_trace elements =
  let states = List.fold_left (fun acc ele -> process_sexp acc ele) [] elements in
  let states = List.rev states in
  Printf.printf "loaded %d states\n%!" (List.length states)

let timestamp file =
  match
    try Some (Scanf.sscanf file "%.05f" (fun x -> x))
    with _ -> None
  with
  | Some ts ->
    let tm = Unix.gmtime ts in
    let date = Printf.sprintf "%04d-%02d-%02d %02d:%02d:%02d"
        (1900 + tm.Unix.tm_year) (succ tm.Unix.tm_mon) tm.Unix.tm_mday
        tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
    in
    Printf.printf "trace from %s\n%!" date
  | None -> Printf.printf "cannot find timestamp\n%!"

let load file =
  timestamp (Filename.basename file) ;
  match try Some (load_sexp file) with _ -> None with
    | None -> Printf.printf "error loading %s\n" file
    | Some (List xs) -> process_trace xs ; ()

let () =
  match Sys.argv with
  | [| _ ; file |] -> load file
