open Unix

let get_socket_connection (host : string) (port : int) =
  socket PF_INET SOCK_DGRAM 0
