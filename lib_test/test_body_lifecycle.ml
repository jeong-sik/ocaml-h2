open H2
module Internal = H2__
open H2__
module Wire = Internal.Serialize.Writer

let bs s = Bigstringaf.of_string s ~off:0 ~len:(String.length s)
let check = Alcotest.(check bool)
let completion reader expected = check "body completion" true (Body.Reader.completion reader = expected)
let consume reader ~on_eof ~on_read =
  let rec read () = Body.Reader.schedule_read reader ~on_eof
    ~on_read:(fun b ~off ~len -> on_read (Bigstringaf.substring b ~off ~len); read ()) in
  read ()

type side = {
  next : unit -> [ `Write of Bigstringaf.t IOVec.t list | `Yield | `Close of int ];
  report : [ `Ok of int | `Closed ] -> unit;
  read : Bigstringaf.t -> off:int -> len:int -> int;
  wake : (unit -> unit) -> unit;
  mutable parked : bool;
  mutable pending : string;
}
let drain source target =
  let rec loop n = if source.parked then n else match source.next () with
    | `Write xs ->
      let s = String.concat "" (List.map (fun (v : _ IOVec.t) -> Bigstringaf.substring v.buffer ~off:v.off ~len:v.len) xs) in
      source.report (`Ok (String.length s));
      target.pending <- target.pending ^ s; loop (n + String.length s)
    | `Yield -> source.parked <- true; source.wake (fun () -> source.parked <- false); n
    | `Close _ -> n in
  loop 0
let feed target =
  let len = String.length target.pending in
  if len = 0 then 0 else (
    let n = target.read (bs target.pending) ~off:0 ~len in
    target.pending <- String.sub target.pending n (len - n); n)
let pump a b =
  let rec loop () =
    let n = drain b a + feed a + drain a b + feed b in
    if n > 0 then loop () in
  loop ()
let pair ?(on_error = fun _ -> ()) handler =
  let server = Server_connection.create
    ~config:{ Config.default with initial_window_size = 65535l }
    ~error_handler:(fun ?request:_ error respond -> on_error error; Body.Writer.close (respond Headers.empty)) handler in
  let client = Client_connection.create ~error_handler:(function
    | `Protocol_error (code, message) -> Alcotest.failf "connection error %ld: %s" (Error_code.serialize code) message
    | _ -> Alcotest.fail "connection error") () in
  let a = { next = (fun () -> Server_connection.next_write_operation server);
    report = Server_connection.report_write_result server; read = Server_connection.read server;
    wake = Server_connection.yield_writer server; parked = false; pending = "" } in
  let b = { next = (fun () -> Client_connection.next_write_operation client);
    report = Client_connection.report_write_result client; read = Client_connection.read client;
    wake = Client_connection.yield_writer client; parked = false; pending = "" } in
  server, client, a, b
let request ?(headers = Headers.empty) ?(meth = `POST) ?(on_error = ignore)
    ?(on_response = fun _ r -> consume r ~on_eof:ignore ~on_read:ignore) client target body ~close =
  let writer = Client_connection.request client ~flush_headers_immediately:true
    (Request.create ~scheme:"http" meth target
      ~headers:(Headers.of_list ((":authority", "localhost") :: Headers.to_list headers)))
    ~error_handler:on_error ~response_handler:on_response in
  Body.Writer.write_string writer body;
  if close then Body.Writer.flush writer (fun _ -> Body.Writer.close writer);
  writer
let wire target write =
  let writer = Wire.create 4096 in
  write writer;
  let encoded = Faraday.serialize_to_string (Wire.faraday writer) in
  target.pending <- target.pending ^ encoded;
  ignore (feed target)
let info ?(end_stream = false) ?(padding = Bigstringaf.empty) id =
  let flags = if end_stream then Internal.Flags.(default_flags |> set_end_stream) else Internal.Flags.default_flags in
  Wire.make_frame_info ~flags ~padding id
let inflow server =
  let Internal.Server_connection.Scheduler.Connection root = server.Internal.Server_connection.streams in
  root.inflow

let test_reader_callback_credit () =
  let credit = ref 0 in
  let reader = Internal.Body.Reader.create (Bigstringaf.create 32) ~done_reading:(fun n -> credit := !credit + n) in
  Faraday.write_string (Internal.Body.Reader.unsafe_faraday reader) "payload";
  (try Internal.Body.Reader.schedule_read reader ~on_eof:ignore
    ~on_read:(fun _ ~off:_ ~len:_ -> failwith "callback") with Failure _ -> ());
  Internal.Body.Reader.discard reader;
  Alcotest.(check int) "raising callback returns current chunk once" 7 !credit
let test_nested_discard_credit () =
  let credit = ref 0 and eof = ref false in
  let reader = Internal.Body.Reader.create (Bigstringaf.create 32) ~done_reading:(fun n -> credit := !credit + n) in
  let f = Internal.Body.Reader.unsafe_faraday reader in
  Faraday.schedule_bigstring f (bs "first"); Faraday.schedule_bigstring f (bs "second");
  Internal.Body.Reader.schedule_read reader ~on_eof:ignore ~on_read:(fun _ ~off:_ ~len:_ ->
    Internal.Body.Reader.discard reader;
    Internal.Body.Reader.schedule_read reader ~on_eof:(fun () -> eof := true) ~on_read:(fun _ ~off:_ ~len:_ -> Alcotest.fail "discard delivered bytes"));
  Internal.Body.Reader.discard reader;
  Alcotest.(check int) "current and buffered chunks each credited once" 11 !credit;
  check "discard delivered EOF" true !eof
let test_empty_isolation () =
  let first = Internal.Body.Reader.create_empty () and second = Internal.Body.Reader.create_empty () in
  Internal.Body.Reader.discard first;
  check "first aborted" true (Internal.Body.Reader.completion first = Aborted);
  check "second remains complete" true (Internal.Body.Reader.completion second = Complete)

let test_refused_connection mode () =
  let refused = ref [] and received = ref 0 and completed = ref false in
  let handler reqd =
    let reader = Reqd.request_body reqd in
    if (Reqd.request reqd).target = "/refuse" then (
      (match mode with
       | `Close -> Body.Reader.close reader
       | `Discard -> Body.Reader.discard reader
       | `Buffered -> ());
      refused := reqd :: !refused)
    else consume reader ~on_read:(fun s -> received := !received + String.length s)
      ~on_eof:(fun () -> completion reader Complete; completed := true;
        Reqd.respond_with_string reqd (Response.create `OK) "ok") in
  let server, client, a, b = pair handler in
  for _ = 1 to 3 do
    ignore (request client "/refuse" (String.make 40000 'x') ~close:true);
    pump a b;
    List.iter (fun reqd -> Reqd.respond_with_string reqd (Response.create `Unauthorized) "denied") !refused;
    refused := []; pump a b;
    Alcotest.(check int32) "refusal restores connection window" 65535l (inflow server)
  done;
  ignore (request client "/normal" (String.make 40000 'z') ~close:true); pump a b;
  Alcotest.(check int) "next POST receives every byte" 40000 !received;
  check "next POST receives valid EOF" true !completed

let test_error_eof () =
  let active = ref None and observed = ref false in
  let _, client, a, b = pair (fun reqd ->
    active := Some reqd;
    let reader = Reqd.request_body reqd in
    consume reader ~on_read:ignore ~on_eof:(fun () ->
      completion reader Aborted;
      check "error visible before EOF" true (Option.is_some (Reqd.error_code reqd)); observed := true)) in
  ignore (request client "/partial" "prefix" ~close:false); pump a b;
  Reqd.report_exn (Option.get !active) (Failure "injected");
  check "error notified EOF" true !observed
let test_reset_eof raises () =
  let eof = ref false and errors = ref 0 and normal = ref false in
  let handler reqd =
    let reader = Reqd.request_body reqd in
    if (Reqd.request reqd).target = "/reset" then
      consume reader ~on_read:ignore ~on_eof:(fun () ->
        completion reader Aborted; eof := true;
        if raises then failwith "EOF callback" else Reqd.report_exn reqd (Failure "reentrant"))
    else consume reader ~on_read:ignore ~on_eof:(fun () -> normal := true;
      Reqd.respond_with_string reqd (Response.create `OK) "ok") in
  let _, client, a, b = pair ~on_error:(fun _ -> incr errors) handler in
  ignore (request client "/reset" "prefix" ~close:false); pump a b;
  wire a (fun w -> Wire.write_rst_stream w (info 1l) Error_code.Cancel);
  check "reset delivered aborted EOF" true !eof;
  Alcotest.(check int) "reset callback creates no error response" 0 !errors;
  ignore (request client "/normal" "good" ~close:true); pump a b;
  check "normal sibling survives reset callback" true !normal

let test_retired_data () =
  let normal = ref false in
  let server, client, a, b = pair (fun reqd ->
    let reader = Reqd.request_body reqd in
    consume reader ~on_read:ignore ~on_eof:(fun () ->
      normal := true; Reqd.respond_with_string reqd (Response.create `OK) "ok")) in
  ignore (request client "/closed" "done" ~close:true); pump a b;
  (* Remove a genuinely closed descriptor to exercise the late in-flight DATA
     path, independently of the scheduler's retention duration. *)
  let Internal.Server_connection.Scheduler.Connection root = server.Internal.Server_connection.streams in
  Internal.Scheduler.StreamsTbl.remove root.all_streams 1l;
  for _ = 1 to 3 do wire a (fun w -> Wire.write_data w (info 1l) (String.make 16000 'x')) done;
  Alcotest.(check int32) "retired stream DATA restores connection inflow" 65535l (inflow server);
  normal := false; ignore (request client "/next" (String.make 40000 'z') ~close:true); pump a b;
  check "POST after retired stream DATA completes" true !normal
let test_padded_data () =
  let reader = ref None and eof = ref false in
  let server, client, a, b = pair (fun reqd ->
    let body = Reqd.request_body reqd in reader := Some body;
    consume body ~on_read:ignore ~on_eof:(fun () -> eof := true)) in
  ignore (request client "/padded" "" ~close:false); pump a b;
  wire a (fun w -> Wire.write_data w (info ~end_stream:true ~padding:(bs "padding") 1l) "abc");
  check "padded DATA completes" true !eof; completion (Option.get !reader) Complete;
  Alcotest.(check int32) "padding and application credits restored" 65535l (inflow server)

let test_bad_request headers payload () =
  let invalid_deliveries = ref 0 and errors = ref 0 and normal = ref false in
  let _, client, a, b = pair ~on_error:(fun _ -> incr errors) (fun reqd ->
    let reader = Reqd.request_body reqd in
    consume reader ~on_read:ignore ~on_eof:(fun () ->
      if Body.Reader.completion reader = Complete then (
        if (Reqd.request reqd).target = "/invalid" then incr invalid_deliveries else normal := true;
        Reqd.respond_with_string reqd (Response.create `OK) "ok"))) in
  ignore (request client "/invalid" payload ~headers:(Headers.of_list headers) ~close:true); pump a b;
  check "invalid request rejected" true (!errors > 0);
  Alcotest.(check int) "invalid body never delivered as complete" 0 !invalid_deliveries;
  ignore (request client "/normal" (String.make 40000 'z') ~close:true); pump a b;
  check "normal sibling after invalid request completes" true !normal

let test_response meth status declared payload () =
  let completed = ref false and invalid = ref false in
  let _, client, a, b = pair (fun reqd ->
    Reqd.respond_with_string reqd (Response.create status ~headers:(Headers.of_list ["content-length", declared])) payload) in
  ignore (request client "/response" "" ~meth ~close:true
    ~on_error:(fun _ -> invalid := true)
    ~on_response:(fun _ reader -> consume reader ~on_read:ignore
      ~on_eof:(fun () -> completed := Body.Reader.completion reader = Complete)));
  pump a b;
  let valid = payload = "" && (meth = `HEAD || status = `No_content || status = `Not_modified) || String.length payload = int_of_string declared in
  check "response completion matches actual length with bodyless exceptions" valid !completed;
  check "invalid response reports error" (not valid) !invalid

let test_upgrade declared payload () =
  let calls = ref 0 and errors = ref 0 and observed = ref None in
  let body = bs payload in
  let result = Server_connection.create_h2c ~meth:`POST ~target:"/upgrade"
    ~config:{Config.default with initial_window_size = 65535l}
    ~headers:(Httpun_types.Headers.of_list ["connection", "Upgrade, HTTP2-Settings"; "upgrade", "h2c";
      "http2-settings", ""; "host", "localhost"; "content-length", declared])
    ~request_body:[{IOVec.buffer=body; off=0; len=String.length payload}]
    ~error_handler:(fun ?request:_ _ respond -> incr errors; Body.Writer.close (respond Headers.empty))
    (fun reqd -> incr calls; let reader = Reqd.request_body reqd in
      consume reader ~on_read:ignore ~on_eof:(fun () -> observed := Some (Body.Reader.completion reader))) in
  let server = match result with Ok server -> server | Error msg -> Alcotest.fail msg in
  if String.length payload = int_of_string declared then (
    Alcotest.(check int) "valid upgrade reaches handler" 1 !calls;
    check "valid upgrade complete" true (!observed = Some Complete);
    Alcotest.(check int32) "HTTP1 upgrade bytes create no H2 credits" 65535l (inflow server))
  else (
    Alcotest.(check int) "invalid upgrade never dispatched" 0 !calls;
    Alcotest.(check int) "invalid upgrade rejected" 1 !errors)

let test_read_exception_connection () =
  let normal = ref false in
  let server, client, a, b = pair (fun reqd ->
    let reader = Reqd.request_body reqd in
    if (Reqd.request reqd).target = "/raise" then
      Body.Reader.schedule_read reader ~on_eof:ignore
        ~on_read:(fun _ ~off:_ ~len:_ -> failwith "read callback")
    else consume reader ~on_read:ignore ~on_eof:(fun () ->
      normal := true; Reqd.respond_with_string reqd (Response.create `OK) "ok")) in
  ignore (request client "/raise" (String.make 40000 'x') ~close:true); pump a b;
  Alcotest.(check int32) "failed callback restores inflow" 65535l (inflow server);
  ignore (request client "/next" (String.make 40000 'z') ~close:true); pump a b;
  check "sibling survives raising read callback" true !normal

let trailer_info id =
  Wire.make_frame_info ~max_frame_size:8
    ~flags:Internal.Flags.(default_flags |> set_end_stream) id
let trailers = Headers.of_list ["x-trailer", String.make 100 't']
let test_request_trailers declared () =
  let complete = ref false and errors = ref 0 in
  let _, client, a, b = pair ~on_error:(fun _ -> incr errors) (fun reqd ->
    let reader = Reqd.request_body reqd in
    consume reader ~on_read:ignore ~on_eof:(fun () ->
      complete := Body.Reader.completion reader = Complete;
      if !complete then Reqd.respond_with_string reqd (Response.create `OK) "ok")) in
  ignore (request client "/trailers" "abc" ~headers:(Headers.of_list ["content-length", declared]) ~close:false);
  pump a b;
  wire a (fun w -> Wire.write_response_trailers w (Hpack.Encoder.create 4096) (trailer_info 1l) trailers);
  pump a b;
  let valid = declared = "3" in
  check "request completion after fragmented trailers" valid !complete;
  Alcotest.(check int) "request trailer length errors" (if valid then 0 else 1) !errors
let test_response_trailers declared () =
  let complete = ref false and errors = ref 0 in
  let _, client, a, b = pair (fun _ -> ()) in
  ignore (request client "/trailers" "" ~close:true
    ~on_error:(fun _ -> incr errors)
    ~on_response:(fun _ reader -> consume reader ~on_read:ignore
      ~on_eof:(fun () -> complete := Body.Reader.completion reader = Complete)));
  pump a b;
  let encoder = Hpack.Encoder.create 4096 in
  wire b (fun w -> Wire.write_response_headers w encoder (info 1l)
    (Response.create `OK ~headers:(Headers.of_list ["content-length", declared])));
  wire b (fun w -> Wire.write_data w (info 1l) "abc");
  wire b (fun w -> Wire.write_response_trailers w encoder (trailer_info 1l) trailers);
  let valid = declared = "3" in
  check "response completion after fragmented trailers" valid !complete;
  Alcotest.(check int) "response trailer length errors" (if valid then 0 else 1) !errors

let test_error_eof_exception client_error () =
  let normal = ref false and errors = ref 0 in
  let _, client, a, b = pair ~on_error:(fun _ -> incr errors) (fun reqd ->
    let target = (Reqd.request reqd).target in
    if target = "/invalid-response" then
      Reqd.respond_with_string reqd
        (Response.create `OK ~headers:(Headers.of_list ["content-length", "10"])) "abc"
    else (
      let reader = Reqd.request_body reqd in
      consume reader ~on_read:ignore ~on_eof:(fun () ->
        if target = "/invalid-request" then failwith "error EOF callback";
        normal := true; Reqd.respond_with_string reqd (Response.create `OK) "ok"))) in
  if client_error then
    ignore (request client "/invalid-response" "" ~close:true
      ~on_error:(fun _ -> incr errors)
      ~on_response:(fun _ reader -> consume reader ~on_read:ignore
        ~on_eof:(fun () -> failwith "error EOF callback")))
  else ignore (request client "/invalid-request" "abc" ~close:true
    ~headers:(Headers.of_list ["content-length", "10"]));
  pump a b;
  Alcotest.(check int) "original error handler called once" 1 !errors;
  ignore (request client "/normal" (String.make 40000 'z') ~close:true); pump a b;
  check "sibling survives error EOF exception" true !normal

let test_client_retired_data () =
  let complete = ref false in
  let _, client, a, b = pair (fun reqd ->
    consume (Reqd.request_body reqd) ~on_read:ignore ~on_eof:(fun () ->
      Reqd.respond_with_string reqd (Response.create `OK) "ok")) in
  ignore (request client "/first" "done" ~close:true); pump a b;
  let Internal.Client_connection.Scheduler.Connection root = client.Internal.Client_connection.streams in
  let initial_inflow = root.inflow in
  Internal.Scheduler.StreamsTbl.remove root.all_streams 1l;
  for _ = 1 to 3 do wire b (fun w -> Wire.write_data w (info 1l) (String.make 16000 'x')) done;
  Alcotest.(check int32) "retired response DATA preserves connection inflow" initial_inflow root.inflow;
  ignore (request client "/next" (String.make 40000 'z') ~close:true
    ~on_response:(fun _ reader -> consume reader ~on_read:ignore
      ~on_eof:(fun () -> complete := Body.Reader.completion reader = Complete)));
  pump a b;
  check "sibling after retired response completes" true !complete

let test_client_padded_data () =
  let complete = ref false in
  let _, client, a, b = pair (fun _ -> ()) in
  ignore (request client "/padded" "" ~close:true
    ~on_response:(fun _ reader -> consume reader ~on_read:ignore
      ~on_eof:(fun () -> complete := Body.Reader.completion reader = Complete)));
  pump a b;
  let Internal.Client_connection.Scheduler.Connection root = client.Internal.Client_connection.streams in
  let initial_inflow = root.inflow in
  wire b (fun w -> Wire.write_response_headers w (Hpack.Encoder.create 4096) (info 1l)
    (Response.create `OK ~headers:(Headers.of_list ["content-length", "3"])));
  wire b (fun w -> Wire.write_data w (info ~end_stream:true ~padding:(bs "padding") 1l) "abc");
  check "padded response complete" true !complete;
  Alcotest.(check int32) "response padding credits restored" initial_inflow root.inflow

let test_completed_response_survives_no_error_reset () =
  let received_reader = ref None in
  let _, client, a, b = pair (fun reqd ->
    Reqd.respond_with_string reqd
      (Response.create `OK ~headers:(Headers.of_list ["content-length", "3"])) "abc") in
  ignore (request client "/early-response" "prefix" ~close:false
    ~on_response:(fun _ reader -> received_reader := Some reader));
  pump a b;
  let reader = Option.get !received_reader in
  completion reader Complete;
  let bytes = Buffer.create 3 and eof = ref false in
  consume reader ~on_read:(Buffer.add_string bytes) ~on_eof:(fun () -> eof := true);
  Alcotest.(check string) "completed response remains readable after upload cancellation" "abc" (Buffer.contents bytes);
  check "completed response has EOF" true !eof

let () = Alcotest.run "H2 body lifecycle" ["lifecycle", List.map (fun (name, run) -> name, `Quick, run) [
  "callback exception returns credit", test_reader_callback_credit;
  "nested discard credits once", test_nested_discard_credit;
  "empty readers independent", test_empty_isolation;
  "closed refusal connection continuity", test_refused_connection `Close;
  "discarded refusal connection continuity", test_refused_connection `Discard;
  "buffered refusal connection continuity", test_refused_connection `Buffered;
  "error visible at aborted EOF", test_error_eof;
  "reset EOF reentrancy", test_reset_eof false;
  "reset EOF exception isolation", test_reset_eof true;
  "retired stream DATA credits", test_retired_data;
  "padded DATA credits", test_padded_data;
  "invalid decimal", test_bad_request ["content-length", "0x10"] "";
  "conflicting lengths", test_bad_request ["content-length", "2"; "content-length", "3"] "";
  "short request DATA", test_bad_request ["content-length", "10"] "abc";
  "empty incomplete request", test_bad_request ["content-length", "10"] "";
  "short response DATA", test_response `GET `OK "10" "abc";
  "empty incomplete response", test_response `GET `OK "10" "";
  "HEAD representation length", test_response `HEAD `OK "10" "";
  "204 representation length", test_response `GET `No_content "10" "";
  "304 representation length", test_response `GET `Not_modified "10" "";
  "valid fixed response", test_response `GET `OK "3" "abc";
  "valid upgrade", test_upgrade "3" "abc";
  "short upgrade", test_upgrade "10" "abc";
  "empty incomplete upgrade", test_upgrade "10" "";
  "raising read callback connection continuity", test_read_exception_connection;
  "valid fragmented request trailers", test_request_trailers "3";
  "short fragmented request trailers", test_request_trailers "10";
  "valid fragmented response trailers", test_response_trailers "3";
  "short fragmented response trailers", test_response_trailers "10";
  "request error EOF exception isolation", test_error_eof_exception false;
  "response error EOF exception isolation", test_error_eof_exception true;
  "retired response DATA credits", test_client_retired_data;
  "padded response DATA credits", test_client_padded_data;
  "complete response survives NO_ERROR reset", test_completed_response_survives_no_error_reset;
]]
