open Unix
open Definitions
open CoqPacket
open CoqClient
open CoqUtils
open Bindings
open Types

(* Constants from TACACS protocol *)
(* let tacacs_version = 0x80 Version 128 *)

let default_server_port =
  Globals.server_port (* Port 49 according to RFC, using 3000 for testing *)

let max_packet_size = Globals.max_tacacs_packet_size (* 536 bytes *)

(* Convert between OCaml and Coq types *)
(* let coq_ip_to_ocaml_ip (addr : coq_IPAddress) : int * int * int * int =
  let ((b1, b2), b3), b4 = addr in
  (Char.code b1, Char.code b2, Char.code b3, Char.code b4) *)

let ocaml_ip_to_coq_ip (a, b, c, d) : coq_IPAddress =
  (((Char.chr a, Char.chr b), Char.chr c), Char.chr d)

let string_of_response_type (res : coq_ResponseType) : string =
  response_type_to_string res

let string_of_reason_type (reason : coq_ReasonType) : string =
  reason_type_to_string reason

let ip_address_of_string (ip_str : string) : int * int * int * int =
  try Scanf.sscanf ip_str "%d.%d.%d.%d" (fun a b c d -> (a, b, c, d))
  with _ -> failwith ("Invalid IP address format: " ^ ip_str)

(* Client class encapsulating TACACS functionality *)
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
          (* Build packet using CoqClient functions *)
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
              (* Send packet *)
              let bytes = Bytes.of_string serialized_data in
              let sent =
                sendto sock bytes 0 (Bytes.length bytes) [] server_sockaddr
              in
              if sent <> Bytes.length bytes then
                failwith "Failed to send complete packet";

              (* Set socket timeout *)
              setsockopt_float sock SO_RCVTIMEO 5.0;

              (* Receive response *)
              let buffer = Bytes.create max_packet_size in
              try
                let len, _ = recvfrom sock buffer 0 max_packet_size [] in
                if len <= 0 then failwith "Empty response received";

                (* Parse response *)
                let response_data = Bytes.sub_string buffer 0 len in
                match parse_packet response_data with
                | Ok packet -> (
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

    (* High-level API methods for TACACS operations *)

    (* Login to the TACACS server *)
    method login username password =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketLogin username password empty_addr
          (Uint63.of_int 0)
      in
      response

    (* Request superuser privileges *)
    method superuser username password =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketSuperuser username password empty_addr
          (Uint63.of_int 0)
      in
      response

    (* Request connection to a remote host *)
    method connect_request (dest_ip : int * int * int * int) (dest_port : int) =
      let coq_ip = ocaml_ip_to_coq_ip dest_ip in
      let coq_port = Uint63.of_int dest_port in
      let response =
        self#send_and_receive PacketConnect "" "" coq_ip coq_port
      in
      response

    (* Logout from the TACACS server *)
    method logout =
      let empty_addr = (((Char.chr 0, Char.chr 0), Char.chr 0), Char.chr 0) in
      let response =
        self#send_and_receive PacketLogout "" "" empty_addr (Uint63.of_int 0)
      in
      response

    (* Set SLIP address *)
    method set_slip_address (ip_addr : int * int * int * int) =
      let coq_ip = ocaml_ip_to_coq_ip ip_addr in
      let response =
        self#send_and_receive PacketSlipAddr "" "" coq_ip (Uint63.of_int 0)
      in
      response
  end

(* Command-line interface *)
let usage =
  "Usage: tacacs_cli [options] command [args...]\n\
   Commands:\n\
  \  login <username> <password>            - Login to TACACS server\n\
  \  superuser <username> <password>        - Request superuser privileges\n\
  \  connect <ip_address> <port>            - Request connection to remote host\n\
  \  logout                                 - Logout from TACACS server\n\
  \  slipaddr <ip_address>                  - Set SLIP address\n\n\
   Options:\n\
  \  -h, --host <hostname>                  - TACACS server hostname (default: \
   localhost)\n\
  \  -p, --port <port>                      - TACACS server port (default: 3000)\n\
  \  --help                                 - Display this help message"

(* Process the command line arguments and perform requested operations *)
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
  | "logout" :: _ -> (
      let client = new tacacs_client !host !port in
      try
        Printf.printf "Sending logout request to %s:%d...\n" !host !port;
        let response = client#logout in
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
  | cmd :: _ ->
      Printf.printf "Unknown command: %s\nUse --help for usage information.\n"
        cmd

(* Entry point *)
let () = main ()
