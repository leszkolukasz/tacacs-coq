open Unix
open Definitions
open CoqPacket
open CoqClient
open CoqUtils
open Bindings
open Types

let default_server_port = Globals.server_port
let max_packet_size = Globals.max_tacacs_packet_size

let ocaml_ip_to_coq_ip (a, b, c, d) : coq_IPAddress =
  (((Char.chr a, Char.chr b), Char.chr c), Char.chr d)

let string_of_response_type (res : coq_ResponseType) : string =
  response_type_to_string res

let string_of_reason_type (reason : coq_ReasonType) : string =
  reason_type_to_string reason

let ip_address_of_string (ip_str : string) : int * int * int * int =
  try Scanf.sscanf ip_str "%d.%d.%d.%d" (fun a b c d -> (a, b, c, d))
  with _ -> failwith ("Invalid IP address format: " ^ ip_str)

class tacacs_client server_host server_port =
  let addr =
    try (gethostbyname server_host).h_addr_list.(0)
    with Not_found -> failwith ("Host not found: " ^ server_host)
  in
  let server_sockaddr = ADDR_INET (addr, server_port) in

  object (self)
    val mutable socket_opt = None

    method init_socket () =
      if socket_opt = None then
        socket_opt <- Some (Unix.socket PF_INET SOCK_DGRAM 0)

    method close_socket () =
      match socket_opt with
      | Some sock ->
          close sock;
          socket_opt <- None
      | None -> ()

    method private send_and_receive (packet_type : coq_PacketType)
        (username : string) (password : string) (dest_addr : coq_IPAddress)
        (dest_port : Uint63.t) : coq_ParsedPacket =
      self#init_socket ();
      match socket_opt with
      | Some sock -> (
          match
            build_and_serialize_packet packet_type username password dest_addr
              dest_port
          with
          | Error msg ->
              failwith
                (match msg with
                | Some s -> s
                | None -> "Failed to build packet")
          | Ok serialized_data -> (
              let bytes = Bytes.of_string serialized_data in
              let sent =
                sendto sock bytes 0 (Bytes.length bytes) [] server_sockaddr
              in
              if sent <> Bytes.length bytes then
                failwith "Failed to send complete packet";

              setsockopt_float sock SO_RCVTIMEO 5.0;

              let buffer = Bytes.create max_packet_size in
              try
                let len, _ = recvfrom sock buffer 0 max_packet_size [] in
                if len <= 0 then failwith "Empty response received";

                (* Parse the received packet *)
                let response_data = Bytes.sub_string buffer 0 len in
                let parsed_packet = parse_packet response_data in
                (* Validate and handle the response packet *)
                match parsed_packet with
                | Ok packet -> (
                    Printf.printf "%s" (packet_to_string packet);
                    (* Handle the response packet *)
                    match handle_response_packet packet with
                    | Ok validated_packet -> validated_packet
                    | Error msg ->
                        failwith
                          (match msg with
                          | Some s -> s
                          | None -> "Invalid response packet"))
                | Error msg ->
                    failwith
                      (match msg with
                      | Some s -> s
                      | None -> "Failed to parse response")
              with
              | Unix_error (EAGAIN, _, _) ->
                  failwith "Timeout waiting for response"
              | e -> failwith (Printexc.to_string e)))
      | None -> failwith "Socket initialization failed"

    method login username password =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketLogin username password empty_addr
          (Uint63.of_int 0)
      in
      response

    method superuser username password =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketSuperuser username password empty_addr
          (Uint63.of_int 0)
      in
      response

    method connect_request (dest_ip : int * int * int * int) (dest_port : int) =
      let coq_ip = ocaml_ip_to_coq_ip dest_ip in
      let coq_port = Uint63.of_int dest_port in
      let response =
        self#send_and_receive PacketConnect "" "" coq_ip coq_port
      in
      response

    method logout ?(username = "") ?(password = "") ?(line = 1)
        ?(reason = ReasonQuit) () =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketLogout username password empty_addr
          (Uint63.of_int 0)
      in
      response

    method set_slip_address (ip_addr : int * int * int * int) =
      let coq_ip = ocaml_ip_to_coq_ip ip_addr in
      let response =
        self#send_and_receive PacketSlipAddr "" "" coq_ip (Uint63.of_int 0)
      in
      response

    method slip_on =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketSlipOn "" "" empty_addr (Uint63.of_int 0)
      in
      response

    method slip_off =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketSlipOff "" "" empty_addr (Uint63.of_int 0)
      in
      response
  end

class tacacs_connection host port =
  object (self)
    val client = new tacacs_client host port

    (* Handles a standard login connection sequence *)
    method login_connection username password =
      (* Step 1: Send LOGIN packet *)
      Printf.printf "Starting login connection sequence...\n";
      Printf.printf "Step 1: Sending login request to %s:%d...\n" host port;
      let login_response = client#login username password in
      Printf.printf "Login response: %s (Reason: %s)\n"
        (string_of_response_type login_response.response)
        (string_of_reason_type login_response.reason);

      if not (is_success_response login_response) then Error "Login failed"
      else Ok login_response

    (* Send CONNECT packet during an active connection *)
    method connect_during_session ip_addr port =
      Printf.printf "Sending connect request during active session...\n";
      let response = client#connect_request ip_addr port in
      Printf.printf "Connect response: %s (Reason: %s)\n"
        (string_of_response_type response.response)
        (string_of_reason_type response.reason);
      if is_success_response response then Ok response
      else Error "Connect failed"

    (* End a login connection with LOGOUT *)
    method end_connection ?(username = "") ?(password = "") ?(line = 1)
        ?(reason = ReasonQuit) () =
      Printf.printf "Ending connection...\n";
      let response = client#logout ~username ~password ~line ~reason () in
      Printf.printf "Logout response: %s (Reason: %s)\n"
        (string_of_response_type response.response)
        (string_of_reason_type response.reason);
      client#close_socket ();
      if is_success_response response then Ok response
      else Error "Logout failed"

    (* Handle a complete SLIP connection sequence *)
    method slip_connection username password slip_ip =
      (* Step 1: LOGIN *)
      Printf.printf "Starting SLIP connection sequence...\n";
      Printf.printf "Step 1: Sending login request...\n";
      let login_response = client#login username password in
      Printf.printf "Login response: %s (Reason: %s)\n"
        (string_of_response_type login_response.response)
        (string_of_reason_type login_response.reason);

      if not (is_success_response login_response) then
        Error "SLIP connection failed at login step"
      else (
        (* Step 2: SLIPADDR *)
        Printf.printf "Step 2: Setting SLIP address...\n";
        let slip_addr_response = client#set_slip_address slip_ip in
        Printf.printf "SlipAddr response: %s (Reason: %s)\n"
          (string_of_response_type slip_addr_response.response)
          (string_of_reason_type slip_addr_response.reason);

        if not (is_success_response slip_addr_response) then
          Error "SLIP connection failed at SLIPADDR step"
        else (
          (* Step 3: SLIPON *)
          Printf.printf "Step 3: Activating SLIP mode...\n";
          let slip_on_response = client#slip_on in
          Printf.printf "SlipOn response: %s (Reason: %s)\n"
            (string_of_response_type slip_on_response.response)
            (string_of_reason_type slip_on_response.reason);

          if not (is_success_response slip_on_response) then
            Error "SLIP connection failed at SLIPON step"
          else (
            (* Step 4: LOGOUT (immediate) *)
            Printf.printf "Step 4: Sending logout for SLIP session...\n";
            (* For SLIP mode, pass the username but use ReasonNone reason as per RFC 1492 *)
            let logout_response =
              client#logout ~username ~reason:ReasonNone ()
            in
            Printf.printf "Logout response: %s (Reason: %s)\n"
              (string_of_response_type logout_response.response)
              (string_of_reason_type logout_response.reason);

            if not (is_success_response logout_response) then
              Error "SLIP connection failed at LOGOUT step"
            else
              Ok
                ( login_response,
                  slip_addr_response,
                  slip_on_response,
                  logout_response ))))

    (* End SLIP session *)
    method end_slip_session () =
      Printf.printf "Ending SLIP session...\n";
      let response = client#slip_off in
      Printf.printf "SlipOff response: %s (Reason: %s)\n"
        (string_of_response_type response.response)
        (string_of_reason_type response.reason);
      client#close_socket ();
      if is_success_response response then Ok response
      else Error "SlipOff failed"
  end

let usage =
  "Usage: tacacs_cli [options] command [args...]\n\
   Commands:\n\
  \  login <username> <password>            - Login to TACACS server\n\
  \  superuser <username> <password>        - Request superuser privileges\n\
  \  connect <ip_address> <port>            - Request connection to remote host\n\
  \  logout                                 - Logout from TACACS server\n\
  \  logout <username> <password> <line>    - Logout with specific credentials\n\
  \  slipaddr <ip_address>                  - Set SLIP address\n\
  \  slipon                                 - Enable SLIP mode\n\
  \  slipoff                                - Disable SLIP mode\n\
  \  session login <username> <password>    - Start a login connection session\n\
  \  session slip <username> <password> <ip> - Start a SLIP connection session\n\n\
   Options:\n\
  \  -h, --host <hostname>                  - TACACS server hostname (default: \
   localhost)\n\
  \  -p, --port <port>                      - TACACS server port (default: 3000)\n\
  \  --help                                 - Display this help message"

let main () =
  let host = ref "localhost" in
  let port = ref default_server_port in
  let args = ref [] in

  let set_host h = host := h in
  let set_port p = port := int_of_string p in

  let spec_list =
    [
      ("-h", Arg.String set_host, "TACACS server hostname");
      ("--host", Arg.String set_host, "TACACS server hostname");
      ("-p", Arg.String set_port, "TACACS server port");
      ("--port", Arg.String set_port, "TACACS server port");
    ]
  in

  let collect_args arg = args := !args @ [ arg ] in

  Arg.parse spec_list collect_args usage;

  match !args with
  | [] | [ "--help" ] -> print_endline usage
  | "login" :: username :: password :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending login request to %s:%d...\n" !host !port;
        let response = client#login username password in
        Printf.printf "Login response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);

        if is_success_response response then print_endline "Login successful!"
        else print_endline "Login failed.";

        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "superuser" :: username :: password :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending superuser request to %s:%d...\n" !host !port;
        let response = client#superuser username password in
        Printf.printf "Superuser response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "connect" :: ip_str :: port_str :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending connect request to %s:%d...\n" !host !port;
        let ip_addr = ip_address_of_string ip_str in
        let dest_port = int_of_string port_str in
        let response = client#connect_request ip_addr dest_port in
        Printf.printf "Connect response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "logout" :: username :: password :: line_str :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending logout request to %s:%d...\n" !host !port;
        let line = int_of_string line_str in
        let response = client#logout ~username ~password ~line () in
        Printf.printf "Logout response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "slipaddr" :: ip_str :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending slip address request to %s:%d...\n" !host !port;
        let ip_addr = ip_address_of_string ip_str in
        let response = client#set_slip_address ip_addr in
        Printf.printf "SlipAddr response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "slipon" :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending SLIP ON request to %s:%d...\n" !host !port;
        let response = client#slip_on in
        Printf.printf "SlipOn response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "slipoff" :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending SLIP OFF request to %s:%d...\n" !host !port;
        let response = client#slip_off in
        Printf.printf "SlipOff response: %s (Reason: %s)\n"
          (string_of_response_type response.response)
          (string_of_reason_type response.reason);
        client#close_socket ()
      with e ->
        Printf.printf "Error: %s\n" (Printexc.to_string e);
        client#close_socket ())
  | "session" :: "login" :: username :: password :: _ -> (
      let connection = new tacacs_connection !host !port in
      try
        match connection#login_connection username password with
        | Ok _ ->
            print_endline
              "Login successful! Type 'connect <ip> <port>' to establish \
               connections or 'quit' to logout.";
            let rec session_loop () =
              Printf.printf "> ";
              let input = read_line () in
              match String.split_on_char ' ' input with
              | [ "connect"; ip_str; port_str ] ->
                  let ip_addr = ip_address_of_string ip_str in
                  let port = int_of_string port_str in
                  (match connection#connect_during_session ip_addr port with
                  | Ok _ -> print_endline "Connection successful!"
                  | Error msg -> Printf.printf "Connection failed: %s\n" msg);
                  session_loop ()
              | [ "quit" ] -> (
                  match connection#end_connection () with
                  | Ok _ -> print_endline "Session ended."
                  | Error msg -> Printf.printf "Error ending session: %s\n" msg)
              | _ ->
                  print_endline
                    "Unknown command. Use 'connect <ip> <port>' or 'quit'.";
                  session_loop ()
            in
            session_loop ()
        | Error msg -> Printf.printf "Error: %s\n" msg
      with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
  | "session" :: "slip" :: username :: password :: ip_str :: _ -> (
      let connection = new tacacs_connection !host !port in
      try
        let slip_ip = ip_address_of_string ip_str in
        match connection#slip_connection username password slip_ip with
        | Ok _ ->
            print_endline
              "SLIP connection established. Type 'connect <ip> <port>' to \
               establish connections or 'quit' to terminate.";

            let rec session_loop () =
              Printf.printf "> ";
              let input = read_line () in
              match String.split_on_char ' ' input with
              | [ "connect"; ip_str; port_str ] ->
                  let ip_addr = ip_address_of_string ip_str in
                  let port = int_of_string port_str in
                  (match connection#connect_during_session ip_addr port with
                  | Ok _ -> print_endline "Connection successful!"
                  | Error msg -> Printf.printf "Connection failed: %s\n" msg);
                  session_loop ()
              | [ "quit" ] -> (
                  match connection#end_slip_session () with
                  | Ok _ -> print_endline "SLIP session terminated."
                  | Error msg -> Printf.printf "Error ending session: %s\n" msg)
              | _ ->
                  print_endline
                    "Unknown command. Use 'connect <ip> <port>' or 'quit'.";
                  session_loop ()
            in
            session_loop ()
        | Error msg -> Printf.printf "Error: %s\n" msg
      with e -> Printf.printf "Error: %s\n" (Printexc.to_string e))
  | cmd :: _ ->
      Printf.printf "Unknown command: %s\nUse --help for usage information.\n"
        cmd

let () = main ()
