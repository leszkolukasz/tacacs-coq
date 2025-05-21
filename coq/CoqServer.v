Require Import String.
Require Import Definitions.
Require Import CoqPacket.

Open Scope string_scope.

Definition next_state (state: ServerState) (input: ServerEvent) : Result (ServerState * option Packet) ErrorMsg :=
  match state with
  | NotStarted =>
      match input with
      | Init port socket =>
          let new_state := {| port := port ; socket := socket |} in
          Ok (Running new_state, None)
      | _ => Error (Some "Unexpected event in NotStarted state")
      end
  | Running sdata =>
      match input with
      | Received packet =>
          match parse_packet packet.(data) with
          | Ok parsed_packet =>
            let _ := print_string "hello there" in
            let _ := print_string (packet_to_string parsed_packet) in
            let response := ("Responding... " ++ packet.(data)) in
            let opacket := {| data := response ; addr := packet.(addr) |} in
            Ok (Running sdata, Some opacket)
          | Error e => Error e
          end
      | _ => Error (Some "Unexpected event in Running state")
      end
  | Stopped => Error (Some "Server is stopped")
  end.