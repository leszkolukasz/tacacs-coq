open Types

let check_args () : (string, string) result =
  if Array.length Sys.argv <> 3 then Error "Wrong number of arguments."
  else if Sys.argv.(1) <> "-h" then Error "Wrong format of arguments."
  else Ok Sys.argv.(2)

let print_usage (err_msg : string) =
  print_string err_msg;
  print_newline ();
  print_string "Usage: server -h <host>";
  print_newline ()

let run () : (unit, errorMsg) result =
  match check_args () with
  | Error err_msg ->
      print_usage err_msg;
      Error None
  | Ok host -> Servr.Loop.start_server host Globals.server_port

let main () =
  let result =
    try run ()
    with e ->
      let msg = Printexc.to_string e in
      Error (Some (Printf.sprintf "Exception: %s" msg))
  in
  match result with
  | Ok () -> ()
  | Error msg ->
      ignore @@ Option.map print_endline msg;
      exit 1
;;

if !Sys.interactive then () else main ()
