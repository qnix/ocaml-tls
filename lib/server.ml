open Core
open Flow

let answer_client_finished (sp : security_parameters) (packets : Cstruct.t list) (fin : Cstruct.t) (raw : Cstruct.t)  =
  let computed = Crypto.finished sp.master_secret "client finished" packets in
  assert (Utils.cs_eq computed fin);
  Printf.printf "received good handshake finished\n";
  let my_checksum = Crypto.finished sp.master_secret "server finished" (packets @ [raw]) in
  let send = Writer.assemble_handshake (Finished my_checksum) in
  let params = { sp with client_verify_data = computed ;
                         server_verify_data = my_checksum }
  in
  (`Established params, [`Record (Packet.HANDSHAKE, send)], `Pass)

let answer_client_key_exchange (sp : security_parameters) (packets : Cstruct.t list) (kex : Cstruct.t) (raw : Cstruct.t) =
  let premastersecret =
    match Ciphersuite.ciphersuite_kex sp.ciphersuite with
    | Ciphersuite.RSA ->
       Crypto.decryptRSA_unpadPKCS 48 (Crypto_utils.get_key "server.key") kex
    | Ciphersuite.DHE_RSA ->
       (* we assume explicit communication here, not a client certificate *)
       let params = match sp.dh_params with
         | Some x -> x
         | None -> assert false
       in
       let sec = match sp.dh_secret with
         | Some x -> x
         | None -> assert false
       in
       Crypto.computeDH params sec kex
    | _ -> assert false
  in
  let client_ctx, server_ctx, params = initialise_crypto_ctx sp premastersecret in
  (`KeysExchanged (`Crypted server_ctx, `Crypted client_ctx, params, packets @ [raw]), [], `Pass)

let answer_client_hello_params sp ch raw =
  let cipher = sp.ciphersuite in
  assert (List.mem cipher ch.ciphersuites);
  List.iter (function
              | SecureRenegotiation x ->
                  Printf.printf "got secure renegotiation";
                  Cstruct.hexdump x;
                  Printf.printf "thought I'd get";
                  Cstruct.hexdump sp.client_verify_data;
                  assert (Utils.cs_eq sp.client_verify_data x)
              | _ -> ())
            ch.extensions;
  let params = { sp with
                   server_random = Cstruct.create 32 ; (* TODO: more randomness! *)
                   client_random = ch.random } in
  let server_hello : server_hello =
    { version      = (3, 1) ;
      random       = params.server_random ;
      sessionid    = None ;
      ciphersuites = cipher ;
      extensions   = [SecureRenegotiation (params.client_verify_data <> params.server_verify_data)] } in
  let bufs = [Writer.assemble_handshake (ServerHello server_hello)] in
  let kex = Ciphersuite.ciphersuite_kex cipher in
  let bufs', params' =
    if Ciphersuite.needs_certificate kex then
      let pem = Crypto_utils.read_pem_file "server.pem" in
      let cert = Crypto_utils.pem_to_cstruct pem in
      let asn = Crypto_utils.pem_to_cert pem in
      (bufs @ [Writer.assemble_handshake (Certificate [cert])],
       { params with server_certificate = Some asn })
    else
      (bufs, params)
  in
  let bufs'', params'' =
    if Ciphersuite.needs_server_kex kex then
      begin
        match kex with
        | Ciphersuite.DHE_RSA ->
           let dh_params, priv = Crypto.generateDH 1024 in
           let params'' = { params' with dh_params = Some dh_params ; dh_secret = Some priv } in
           let written = Writer.assemble_dh_parameters dh_params in
           Printf.printf "written";
           Cstruct.hexdump written;
           let data = (params''.client_random <> params''.server_random) <> written in
           let md5signature = Crypto.md5 data in
           let shasignature = Crypto.sha data in
           let signing = md5signature <> shasignature in
           Printf.printf "signing";
           Cstruct.hexdump signing;
           let sign = Crypto.padPKCS1_and_signRSA 128 (Crypto_utils.get_key "server.key") signing in
           let kex = Writer.assemble_dh_parameters_and_signature written sign in
           (bufs' @ [Writer.assemble_handshake (ServerKeyExchange kex)], params'')
        | _ -> assert false
      end
    else
      (bufs', params')
  in
  (* server hello done! *)
  let hello_done = Writer.assemble_handshake ServerHelloDone in
  let packets = bufs'' @ [hello_done] in
  (`Handshaking (params'', raw :: packets),
   List.map (fun e -> `Record (Packet.HANDSHAKE, e)) packets,
   `Pass)

let answer_client_hello (ch : client_hello) raw =
  assert (List.mem Ciphersuite.TLS_EMPTY_RENEGOTIATION_INFO_SCSV ch.ciphersuites);
(*    let cipher = Ciphersuite.TLS_RSA_WITH_3DES_EDE_CBC_SHA in *)
(*    let cipher = Ciphersuite.TLS_RSA_WITH_RC4_128_MD5 in *)
(*    let cipher = Ciphersuite.TLS_RSA_WITH_RC4_128_SHA in *)
  let cipher = Ciphersuite.TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA in
  let params = { entity             = Server ;
                 ciphersuite        = cipher ;
                 master_secret      = Cstruct.create 0 ;
                 client_random      = Cstruct.create 0 ;
                 server_random      = Cstruct.create 0 ;
                 dh_params          = None ;
                 dh_secret          = None ;
                 server_certificate = None ;
                 client_verify_data = Cstruct.create 0 ;
                 server_verify_data = Cstruct.create 0 }
  in
  answer_client_hello_params params ch raw

let handle_record
: tls_internal_state -> content_type -> Cstruct.t
  -> (tls_internal_state * rec_resp list * dec_resp)
= fun is ct buf ->
  Printf.printf "HANDLE_RECORD (in state %s) %s\n"
                (state_to_string is)
                (Packet.content_type_to_string ct);
  match ct with
  | Packet.ALERT ->
     let al = Reader.parse_alert buf in
     Printf.printf "ALERT: %s" (Printer.alert_to_string al);
     (is, [], `Pass)
  | Packet.APPLICATION_DATA ->
     Printf.printf "APPLICATION DATA";
     Cstruct.hexdump buf;
     (is, [], `Pass)
  | Packet.CHANGE_CIPHER_SPEC ->
     begin
       match is with
       | `KeysExchanged (enc, dec, _, _) ->
          let ccs = Cstruct.create 1 in
          Cstruct.set_uint8 ccs 0 1;
          (is,
           [`Record (Packet.CHANGE_CIPHER_SPEC, ccs); `Change_enc enc],
           `Change_dec dec)
       | _ -> assert false
     end
  | Packet.HANDSHAKE ->
     begin
       let handshake = Reader.parse_handshake buf in
       Printf.printf "HANDSHAKE: %s" (Printer.handshake_to_string handshake);
       Cstruct.hexdump buf;
       match (is, handshake) with
       | `Initial, ClientHello ch ->
            answer_client_hello ch buf
       | `Handshaking (p, bs), ClientKeyExchange kex ->
            answer_client_key_exchange p bs kex buf
       | `KeysExchanged (_, _, p, bs), Finished fin ->
            answer_client_finished p bs fin buf
       | `Established sp, ClientHello ch -> (* key renegotiation *)
            answer_client_hello_params sp ch buf
       | _, _-> assert false
     end
  | _ -> assert false

let handle_tls = handle_tls_int handle_record