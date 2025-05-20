Require Import String.
Require Import Definitions.
Require Import CoqPacket.

Definition next_state (state: ServerState) (input: ServerEvent) : Result (ServerState * option Packet) ErrorMsg :=
  match state with
  | NotStarted =>
      match input with
      | Init port socket =>
          let new_state := {| port := port ; socket := socket |} in
          Ok (Running new_state, None)
      | _ => Error (Some "Unexpected event in NotStarted state"%string)
      end
  | Running sdata =>
      match input with
      | Received packet =>
          match parse_packet packet.(data) with
          | Ok parsed_packet =>
            let response := ("Responding... " ++ packet.(data))%string in
            let opacket := {| data := response ; addr := packet.(addr) |} in
            Ok (Running sdata, Some opacket)
          | Error e => Error e
          end
      | _ => Error (Some "Unexpected event in Running state"%string)
      end
  | Stopped => Error (Some "Server is stopped"%string)
  end.