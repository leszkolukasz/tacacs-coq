open Bindings
open Types
open Network
open Unix
open Protocol

let loop_entry (state : unit) : (unit, errorMsg) result =
  let buffer_size = 1024 in
  let buffer = Bytes.make buffer_size '\000' in
  return ()

let start_server (host : string) (port : int) : (unit, errorMsg) result =
  let socket = get_socket_connection host port in
  let he = gethostbyname host in
  let inet_addr = he.h_addr_list.(0) in
  let addr = ADDR_INET (inet_addr, port) in
  bind socket addr;
  let init_state = () in
  (* TODO popraw *)
  loop_entry init_state
