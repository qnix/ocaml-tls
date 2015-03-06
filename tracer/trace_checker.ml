open Read_trace

open Tls
open State

(* why this is all so hackish:
  - incomplete traces (hopping sequence numbers of incoming records (after 1 comes 120))
  - incomplete persistency of stream ciphers (we cannot do much after the first handshake)
  - out of order events: state-in; record-in; state-out; record-out -- crucially: in our recorded state, CCS is already encrypted..
  - fragmentation on both levels: record and handshake
  - incomplete traces (such as "()")
  - traces where version in first handshake is not the same as the one in the upcoming (70edd70bfe97ce96 is a great example of this) -- occurs when searching for the next server hello to fill the choices
 *)

let cs_mmap file =
  Unix_cstruct.of_fd Unix.(openfile file [O_RDONLY] 0)

let priv, cert =
  let file = cs_mmap "/home/hannes/tls-certs-mirage/openmirage.pem" in
  (X509.PK.of_pem_cstruct1 file, X509.Cert.of_pem_cstruct file)

open Nocrypto
open Nocrypto.Dh
let public_of_secret (({ p; gg; _ } as group), { x }) =
  Numeric.Z.to_cstruct_be Z.(powm gg x p)

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

let find_hs_out dec ver t =
  if
    (dec = None) ||
    (try (
       let sout = List.find (function `StateOut _ -> true | _ -> false) t in
       match sout with
       | `StateOut sout -> ver = sout.handshake.protocol_version
       | _ -> true)
     with Not_found -> true)
  then
    find_out ~packet:Packet.HANDSHAKE t
  else
    None

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
          ( match st.handshake.machina with
            | Server (AwaitClientKeyExchange_DHE_RSA _) -> true
            | _ -> false )
        | _ -> false)
      trace
  with
  | Some (`StateOut st) ->
    ( match st.handshake.machina with
      | Server (AwaitClientKeyExchange_DHE_RSA (_, dh_sent, _)) ->
        let group, secret = dh_sent in
        Some (group, secret, public_of_secret dh_sent)
      | _ -> None )
  | _ -> None


(* configured is the range (min, max) -- chosen is the one from server hello -- requested the one from client hello  *)
(* sanity: min >= chosen >= max ; requested >= chosen *)
let version_agreed configured chosen requested =
  match Handshake_common.supported_protocol_version configured (Supported chosen) with
  | None -> fail (`Error (`NoConfiguredVersion chosen))
  | Some _ ->
    if Core.version_ge requested chosen then
      return chosen
    else
      fail (`Error (`NoConfiguredVersion chosen))

(* again, chosen better be part of configured -- and also chosen be a mem of requested *)
(* this is slightly weak -- depending on sni / certificate we have to limit the decision *)
let cipher_agreed _certificates configured chosen requested =
  if List.mem chosen configured &&
     List.mem chosen (Utils.filter_map ~f:Ciphersuite.any_ciphersuite_to_ciphersuite requested)
  then
    return chosen
  else
    fail (`Error (`NoConfiguredCiphersuite [chosen]))

let fixup_initial_state state raw next =
  let server_hello = parse_server_hello raw in
  let dh_sent = match Ciphersuite.ciphersuite_kex server_hello.Core.ciphersuites with
    | Ciphersuite.RSA -> None
    | Ciphersuite.DHE_RSA -> find_dh_sent next
  in
  let config = {
    state.handshake.config with
      own_certificates = `Single (cert, priv) ;
      use_scsv = false ;
  } in
  let choices = {
      version = version_agreed config.protocol_versions server_hello.Core.version ;
      cipher = cipher_agreed config.own_certificates config.ciphers server_hello.Core.ciphersuites ;
      random = (fun () -> server_hello.Core.random) ;
      session_id = (fun () -> server_hello.Core.sessionid) ;
      dh_secret = (fun () -> dh_sent)
    }
  in
  let handshake = { state.handshake with config } in
  (choices, server_hello.Core.version, { state with handshake })


let dbg_cc c = Printf.printf "cc %s\n" (Sexplib.Sexp.to_string_hum (sexp_of_crypto_state c))

let dbg_al al = Sexplib.Sexp.to_string_hum (Core.sexp_of_tls_alert al)

let dbg_fail f = Sexplib.Sexp.to_string_hum (Engine.sexp_of_failure f)

let check_stream = function
  | None -> false
  | Some x -> match x.cipher_st with
    | Stream _ -> true
    | _ -> false

let normalise crypt ver data =
  match Engine.separate_records data with
  | Ok (xs, rest) ->
    assert (Cstruct.len rest = 0) ;
    (* Printf.printf "now trying to decrypt %d packets\n" (List.length xs) ; *)
    let e, acc = List.fold_left (fun (enc, acc) (hdr, data) ->
        dbg_cc enc; Cstruct.hexdump data ;
        match Engine.decrypt ver enc hdr.Core.content_type data with
        | Ok (enc, d) ->
          Printf.printf "dec is %d\n" (Cstruct.len d) ; Cstruct.hexdump d ;
          (enc, (hdr, d) :: acc)
        | Error e ->
          if hdr.Core.content_type == Packet.CHANGE_CIPHER_SPEC (* && Cstruct.len data = 1 *) then
            (* we're a bit unlucky, but let's pretend to be good *)
            let ccs = Writer.assemble_change_cipher_spec in
            (enc, (hdr, ccs) :: acc)
          else
            (Printf.printf "dec failed %s\n" (dbg_fail e) ;
             Cstruct.hexdump data ;
             assert false))
        (crypt, []) xs
    in
    (List.rev acc, e)
  | _ -> assert false

(* am I really bold enough to define equality? *)
let rec exts_eq a b =
  let open Core in
  match a with
  | [] -> true
  | x::xs ->
    exts_eq xs b &&
    match x with
    | Hostname s ->
      ( try (match List.find (function Hostname _ -> true | _ -> false) b, s with
            | Hostname None, None -> true
            | Hostname (Some x), Some y when x = y -> true
            | _ -> false
          ) with Not_found -> false )
    | MaxFragmentLength mfl ->
      ( try (match List.find (function MaxFragmentLength _ -> true | _ -> false) b, mfl with
            | MaxFragmentLength x, y when x = y -> true
            | _ -> false
          ) with Not_found -> false )
    | EllipticCurves ncs ->
      ( try (match List.find (function EllipticCurves _ -> true | _ -> false) b with
            | EllipticCurves x -> List.for_all (fun ec -> List.mem ec x) ncs
            | _ -> false
          ) with Not_found -> false )
    | ECPointFormats ecp ->
      ( try (match List.find (function ECPointFormats _ -> true | _ -> false) b with
            | ECPointFormats x -> List.for_all (fun ec -> List.mem ec x) ecp
            | _ -> false
          ) with Not_found -> false )
    | SecureRenegotiation sn -> (* actually, if sn empty might also be ciphersuite! *)
      ( try (match List.find (function SecureRenegotiation _ -> true | _ -> false) b with
            | SecureRenegotiation sn' -> Nocrypto.Uncommon.Cs.equal sn sn'
            | _ -> false
          ) with Not_found -> false )
    | Padding _ -> true
    | SignatureAlgorithms hs ->
      ( try (match List.find (function SignatureAlgorithms _ -> true | _ -> false) b with
            | SignatureAlgorithms hs' -> List.for_all (fun hs -> List.mem hs hs') hs
            | _ -> false
          ) with Not_found -> false )
    | UnknownExtension (num, data) ->
      ( try (match List.find (function UnknownExtension (x, _) when x = num -> true | _ -> false) b with
            | UnknownExtension (_, data') -> Nocrypto.Uncommon.Cs.equal data data'
            | _ -> false
          ) with Not_found -> false )

let hello_eq (a : ('a, 'b) Core.hello) (b : ('a, 'b) Core.hello) cs_cmp =
  let open Core in
  let cs_eq = Nocrypto.Uncommon.Cs.equal in
  a.version = b.version &&
  cs_eq a.random b.random &&
  (match a.sessionid, b.sessionid with
   | None, None -> true
   | Some a, Some b -> cs_eq a b
   | _ -> false) &&
  cs_cmp a.ciphersuites b.ciphersuites &&
  exts_eq a.extensions b.extensions

let handshake_equal a b =
  let open Core in
  let cs_eq = Nocrypto.Uncommon.Cs.equal in
  match a, b with
  | HelloRequest, HelloRequest -> true
  | ServerHelloDone, ServerHelloDone -> true
  | ClientHello ch, ClientHello ch' -> hello_eq ch ch' (fun a b -> List.for_all (fun c -> List.mem c b) a)
  | ServerHello sh, ServerHello sh' -> hello_eq sh sh' (fun a b -> a = b)
  | Certificate c, Certificate c' -> List.for_all (fun (a, b) -> cs_eq a b) (List.combine c c')
  | ServerKeyExchange skex, ServerKeyExchange skex' -> cs_eq skex skex'
  | CertificateRequest cr, CertificateRequest cr' -> cs_eq cr cr' (* should do modulo CA list *)
  | ClientKeyExchange ckex, ClientKeyExchange ckex' -> cs_eq ckex ckex'
  | CertificateVerify cv, CertificateVerify cv' -> cs_eq cv cv'
  | Finished f, Finished f' -> cs_eq f f'
  | _ -> false

let record_equal (ahdr, adata) (bhdr, bdata) =
  (* Printf.printf "comparing %s with %s\n"
     (Packet.content_type_to_string ahdr.Core.content_type)
     (Packet.content_type_to_string bhdr.Core.content_type) ; *)
  match ahdr.Core.content_type, bhdr.Core.content_type with
  | Packet.CHANGE_CIPHER_SPEC, Packet.CHANGE_CIPHER_SPEC -> true
  | Packet.ALERT, Packet.ALERT -> true (* since we hangup after alert anyways *)
  | Packet.HANDSHAKE, Packet.HANDSHAKE ->
    ( match Engine.separate_handshakes adata, Engine.separate_handshakes bdata with
      | Ok (ahs, arest), Ok (bhs, brest) when
          (Cstruct.len arest = 0) && (Cstruct.len brest = 0) ->
        let cmp1 (a, b) =
          match Reader.parse_handshake a, Reader.parse_handshake b with
          | Reader.Or_error.Ok a, Reader.Or_error.Ok b -> handshake_equal a b
          | _ -> false
        in
        List.for_all cmp1 (List.combine ahs bhs)
      | _ -> false )
    | Packet.APPLICATION_DATA, Packet.APPLICATION_DATA -> true (* should I bother about payload? *)
  | _ -> false

open Sexplib.Conv

type ret =
  | End_of_trace of int
  | Handle_alert of string
  | Alert_in of string
  | Stream_enc
  | No_handshake_out
  | Comparison_failed
  | Alert_out_success
  | Alert_out_fail
with sexp

(* TODO *)
(* pass extension types in choices! *)
(* what happens if handle didn't produce an output, but record-out came along? -- need a way to passthrough / match these as well! *)
(* alert/failure traces *)
let rec replay ?choices prev_state state pending_out t ccs alert_out =
  let handle_and_rec ?choices state hdr data xs =
    (* Printf.printf "now handling...\n" ; dbg_cc state.decryptor ; *)
    match Engine.handle_tls ?choices state (fixup_in_record hdr data) with
    | `Ok (`Ok state', `Response out, `Data data) ->
      let pending = match out with
        | None -> (* Printf.printf "empty out!?\n"; *) pending_out
        | Some out ->
          (* Printf.printf "output from handle_tls, normalising\n" ; *)
          let ver = state.handshake.protocol_version in
          let data, _ = normalise state.encryptor ver out in
          pending_out @ data
      in
      let prev, ccs = match hdr.Core.content_type with
        | Packet.CHANGE_CIPHER_SPEC -> (state', succ ccs)
        | _ -> (prev_state, ccs)
      in
      ( match data with
        | None -> replay ?choices prev state' pending xs ccs alert_out
        | Some x ->
          (* Printf.printf "received data %s\n" (Cstruct.to_string x); *)
          if check_stream state.encryptor then
            Stream_enc
          else
            replay ?choices prev state' pending xs ccs alert_out)
    | `Fail (e, al) ->
      (* in the trace we better have an alert as well! *)
      match alert_out with
      | None ->
        Printf.printf "sth failed %s\n" (dbg_fail e) ;
        Handle_alert (dbg_fail e)
      | Some x ->
        let al = Engine.alert_of_failure e in
        if snd x = al then
          Alert_out_success
        else
          Alert_out_fail
  in

  match t with
  | (`RecordIn (hdr, data))::xs ->
    Printf.printf "record-in %s\n" (Packet.content_type_to_string hdr.Core.content_type) ;
    ( match hdr.Core.content_type with
      | Packet.HANDSHAKE ->
        let enc = fixup_in_record hdr data in
        let ver = state.handshake.protocol_version in
        (* Printf.printf "normalising in record-in to find whether it is a clienthello\n"; *)
        let dec, _ = normalise state.decryptor ver enc in
        ( match dec with
          | (_,x)::_ when Cstruct.get_uint8 x 0 = 1->
            (* Printf.printf "decrypted (%d):" (Cstruct.len x) ; Cstruct.hexdump x ; *)
            ( match find_hs_out state.decryptor ver xs with
              | Some (t, out) ->
                let out_data = Writer.assemble_hdr ver (t, out) in
                (* Printf.printf "normalising out_data\n" ; *)
                ( match normalise prev_state.encryptor ver out_data with
                  | (_,x)::_,_ ->
                    assert (Cstruct.get_uint8 x 0 = 2) ;
                    let choices, version, state = fixup_initial_state state x xs in
                    handle_and_rec ~choices state hdr data xs
                  | _ -> assert false )
              | None ->
                if List.length xs < 3 then
                  ((* Printf.printf "couldn't find handshake out, but trace isn't too long..\n" ; *)
                   No_handshake_out)
                else
                  assert false )
          | _ -> handle_and_rec ?choices state hdr data xs )
      | Packet.ALERT -> (* Printf.printf "alert in! success\n" ; *)
        let enc = fixup_in_record hdr data in
        let ver = state.handshake.protocol_version in
        let dec, _ = normalise state.decryptor ver enc in
        let _ = Engine.handle_tls ?choices state enc in
        ( match dec with
          | (_,x)::_ ->
            ( match Reader.parse_alert x with
              | Reader.Or_error.Ok (_, t) -> Alert_in (Packet.alert_type_to_string t)
              | _ -> Alert_in (Printf.sprintf "unknown alert %d" (Cstruct.get_uint8 data 1) ))
          | _ -> Alert_in (Printf.sprintf "unknown alert' %d" (Cstruct.get_uint8 data 1)) )
      | _ -> handle_and_rec ?choices state hdr data xs )
  | (`RecordOut (t, data))::xs ->
    let rec cmp_data expected rcvd k =
      match expected, rcvd with
      | [], [] -> k []
      | [], _ -> assert false
      | (xh,x)::xs, (yh,y)::ys ->
        (* Printf.printf "comparing out %d vs %d\n" (Cstruct.len x) (Cstruct.len y) ; *)
        (* if not (Nocrypto.Uncommon.Cs.equal x y) then
          (Printf.printf "mismatch! (computed)" ; Cstruct.hexdump x ; Printf.printf "stored" ; Cstruct.hexdump y ;
           assert false) ; *)
        if record_equal (xh,x) (yh,y) then
          cmp_data xs ys k
        else
          (Printf.printf "mismatched records!\n";
           Comparison_failed)
      | xs, [] -> k xs
    in
    let version = state.handshake.protocol_version in
    let data = Writer.assemble_hdr version (t, data) in
    (* Printf.printf "record out, normalising\n" ; *)
    let ver = state.handshake.protocol_version in
    let data, e = normalise prev_state.encryptor ver data in
    cmp_data pending_out data (fun leftover ->
        replay ?choices { prev_state with encryptor = e } state leftover xs ccs alert_out)

  | (`StateIn s)::xs ->
    let maybe_seq recs sin =
      match recs, sin with
      | Some st, Some sin -> Some { st with sequence = sin.sequence }
      | _ -> recs
    in
    let encryptor = maybe_seq prev_state.encryptor s.encryptor
    and decryptor = maybe_seq state.decryptor s.decryptor
    in
    replay ?choices { prev_state with encryptor } { state with decryptor } pending_out xs ccs alert_out
  | _::xs -> replay ?choices prev_state state pending_out xs ccs alert_out
  | [] ->
    match alert_out with
    | None ->
      assert (List.length pending_out = 0) ;
      End_of_trace ccs
    | Some x ->
      Alert_out_fail

let rec mix c s =
  match c, s with
  | [], [] -> []
  | [c], [] ->
    ( match Engine.separate_records c with
      | Ok (xs, rest) ->
        assert (Cstruct.len rest = 0) ;
        List.map (fun x -> `RecordIn x) xs )
  | c::cs, s::ss ->
    match Engine.separate_records c, Engine.separate_records s with
    | Ok (xs, rest), Ok (ys, rest') ->
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

let doit res name ts alert_out trace =
  match alert_out with
  | None ->
    (* Printf.printf "file %s: " name; *)
    let state = init trace in
    let r = replay state state [] trace 0 None in
    if Hashtbl.mem res r then
      let v = Hashtbl.find res r in
      Hashtbl.replace res r (succ v)
    else
      Hashtbl.add res r 1
  | Some al ->
    let alert = Core.tls_alert_of_sexp al in
    (* these are the traces ending with an AlertOut! *)
    let state = init trace in
    let r = replay state state [] trace 0 (Some alert) in
    if Hashtbl.mem res r then
      let v = Hashtbl.find res r in
      Hashtbl.replace res r (succ v)
    else
      Hashtbl.add res r 1

let analyse_res r =
  Hashtbl.iter (fun k v ->
      Printf.printf "%s : %d\n" (Sexplib.Sexp.to_string_hum (sexp_of_ret k)) v)
    r

let run dir file pcap =
  Nocrypto.Rng.reseed (Cstruct.create 1);
  match dir, file, pcap with
  | Some dir, _, _ ->
    let res = Hashtbl.create 10 in
    let ign = ref 0 in
    let suc (name, (ts, (alert, traces))) =
      try (
        if List.length traces > 2 then
          (Printf.printf "+%!" ;
           doit res name ts alert traces)
        else
          ign := succ !ign )
      with e -> Printf.printf "%s error: %s\n%!" name (Printexc.to_string e)
    and fail _ = ign := succ !ign
    in
    let skip = load_dir dir suc fail in
    Printf.printf "skipped %d, ignored %d\n" skip !ign;
    analyse_res res
  | None, Some file, _ ->
    let ts, (alert, trace) = load file in
    let state = init trace in
    let alert = match alert with
      | None -> None
      | Some x -> Some (Core.tls_alert_of_sexp x)
    in
    let r = replay state state [] trace 0 alert in
    ()
  | None, None, Some _ ->
    let state, trace = reconstruct in
    let r = replay state state [] trace 0 None in
    ()
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
