let log_err (m : ('a, 'b) result) : ('a, 'b) result =
  match m with
  | Ok _ -> m
  | Error e ->
      ignore @@ Option.map print_string e;
      print_newline ();
      m
