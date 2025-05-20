open Unix
open Bindings
open Types

let recv_packet (socket : file_descr) (buffer : bytes) : (sockaddr * int, errorMsg) result =
  let (len, addr) = recvfrom socket buffer 0 (Bytes.length buffer) [] in
  if len <= 0 then
    Error (Some "recvfrom failed")
  else
    return (addr, len)

let send_packet (socket : file_descr) (addr : sockaddr) (buffer : bytes) (len: int) : (unit, errorMsg) result =
  let len = sendto socket buffer 0 len [] addr in
  if len <= 0 then
    Error (Some "sendto failed")
  else
    return ()

let get_socket_connection (host : string) (port : int) =
  socket PF_INET SOCK_DGRAM 0
