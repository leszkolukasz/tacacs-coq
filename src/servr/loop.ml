open Bindings
open Types
open Network
open Unix
open Definitions
open CoqServer
open Uint63
open Utils

let rec loop (state : coq_ServerState) (buffer : bytes) :
    (unit, errorMsg) result =
  match state with
  | NotStarted | Stopped -> return ()
  | Running data -> (
      match recv_packet data.socket buffer with
      | Error _ as r ->
          ignore @@ log_err @@ r;
          loop state buffer
      | Ok (client_addr, packet_len) -> (
          let strbuf = String.sub (Bytes.to_string buffer) 0 packet_len in
          let ipacket : coq_Packet = { data = strbuf; addr = client_addr } in
          let* new_state, opacket = next_state state (Received ipacket) in
          match opacket with
          | None -> loop new_state buffer
          | Some opacket ->
              let olen = String.length opacket.data in
              Bytes.blit_string opacket.data 0 buffer 0 olen;
              ignore @@ log_err
              @@ send_packet data.socket opacket.addr buffer olen;
              loop new_state buffer))

let loop_entry (state : coq_ServerState) : (unit, errorMsg) result =
  let buffer_size = 2 * Globals.max_tacacs_packet_size in
  let buffer = Bytes.make buffer_size '\000' in
  loop state buffer

let start_server (host : string) (port : int) : (unit, errorMsg) result =
  let socket = get_socket_connection host port in
  let he = gethostbyname host in
  let inet_addr = he.h_addr_list.(0) in
  let addr = ADDR_INET (inet_addr, port) in
  bind socket addr;
  let* init_state, _ =
    next_state NotStarted (Init (Uint63.of_int port, socket))
  in
  loop_entry init_state
