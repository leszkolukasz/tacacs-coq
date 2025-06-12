Require Import String.
Require Import List.
Require Import Definitions.
Require Import CoqPacket.
Require Import CoqUtils.
Require Import CoqDatabase.

Open Scope string_scope.

Definition THandlePacket : Type := Ret (ParsedPacket * ServerData).

Definition invalid_packet_type (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr) : THandlePacket :=
  log_message "Invalid packet type" (fun _ => Ok (rejected_packet packet, sdata)).

Definition handle_login (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr) : THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some _ => log_message "[LOGIN] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  | None => match find_user packet.(p_username) with
    | Some user =>
        if String.eqb user.(u_password) packet.(p_password) then
          let conn := {| client_addr := clnt_addr ; mode := Normal ; slip_addr := None|} in
          log_message "[LOGIN] OK" (fun _ => Ok (accepted_packet packet, add_connection conn sdata))
        else let opacket := rejected_packet packet
                            |> with_reason_type ReasonPassword in
          log_message "[LOGIN] Wrong password" (fun _ => Ok (opacket, sdata))
    | None => log_message "[LOGIN] User not found" (fun _ => Ok (rejected_packet packet, sdata))
    end
  end.

Definition handle_response := invalid_packet_type.

Definition handle_change := invalid_packet_type.

Definition handle_follow := invalid_packet_type.

Definition handle_connect (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      match conn.(mode) with
      | Normal => log_message "[CONNECT] OK" (fun _ => Ok (accepted_packet packet, sdata)) (* always allow for now *)
      | Slip _ => log_message "[CONNECT] Already in slip mode" (fun _ => Ok (rejected_packet packet, sdata)) (* TODO: should it be rejected here? *)
      end
  | None => log_message "[CONNECT] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_superuser (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      match find_user packet.(p_username) with
      | Some user =>
          if user.(superuser) then log_message "[CONNECT] OK" (fun _ => Ok (accepted_packet packet, sdata))
          else log_message "[CONNECT] Not superuser" (fun _ => Ok (rejected_packet packet, sdata))
      | None => Ok (rejected_packet packet, sdata)
      end
  | None => log_message "[SUPERUSER] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_logout (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      match conn.(mode) with
      | Normal => log_message "[LOGOUT] OK" (fun _ =>
          Ok (accepted_packet packet, remove_connection clnt_addr sdata))
      | Slip logout => match logout with
        | true => log_message "[LOGOUT] Already logged out after entering slip mode" (fun _ =>
          Ok (rejected_packet packet, sdata))
        | false =>
            let new_conn := with_mode (Slip true) conn in
            log_message "[LOGOUT] OK" (fun _ => Ok (accepted_packet packet, update_connection new_conn sdata))
        end
      end
  | None => log_message "[LOGOUT] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_reload := invalid_packet_type.

Definition handle_slip_on (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      match conn.(mode) with
      | Normal =>
          (* Check if slip_addr is set before allowing SLIPON *)
          match conn.(slip_addr) with
          | Some _ =>
              let new_conn := with_mode (Slip false) conn in
              log_message "[SLIPON] OK" (fun _ => Ok (accepted_packet packet, update_connection new_conn sdata))
          | None => 
              log_message "[SLIPON] No SLIP address set" (fun _ => Ok (rejected_packet packet, sdata))
          end
      | Slip _ => log_message "[SLIPON] Already in slip mode" (fun _ => Ok (rejected_packet packet, sdata))
      end
  | None => log_message "[SLIPON] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_slip_off (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      match conn.(mode) with
      | Normal => log_message "[SLIPOFF] In normal mode" (fun _ => Ok (rejected_packet packet, sdata))
      | Slip false =>
          log_message "[SLIPOFF] In slip mode but LOGOUT has not been requested yet" (fun _ =>
            Ok (rejected_packet packet, sdata))
      | Slip true => log_message "[SLIPOFF] OK" (fun _ =>
          Ok (accepted_packet packet, remove_connection clnt_addr sdata))
      end
  | None => log_message "[SLIPOFF] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_slip_addr (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr): THandlePacket :=
  match find_connection clnt_addr sdata with
  | Some conn =>
      let new_conn := with_slip_addr (Some packet.(destination_addr)) conn in
      log_message "[SLIPADDR] OK" (fun _ => Ok (accepted_packet packet, update_connection new_conn sdata))
  | None => log_message "[SLIPADDR] No existing connection found" (fun _ => Ok (rejected_packet packet, sdata))
  end.

Definition handle_packet (packet: ParsedPacket) (sdata: ServerData) (clnt_addr: sockaddr) : THandlePacket :=
  match packet.(kind) with
  | PacketLogin => handle_login packet sdata clnt_addr
  | PacketResponse => handle_response packet sdata clnt_addr
  | PacketChange => handle_change packet sdata clnt_addr
  | PacketFollow => handle_follow packet sdata clnt_addr
  | PacketConnect => handle_connect packet sdata clnt_addr
  | PacketSuperuser => handle_superuser packet sdata clnt_addr
  | PacketLogout => handle_logout packet sdata clnt_addr
  | PacketReload => handle_reload packet sdata clnt_addr
  | PacketSlipOn => handle_slip_on packet sdata clnt_addr
  | PacketSlipOff => handle_slip_off packet sdata clnt_addr
  | PacketSlipAddr => handle_slip_addr packet sdata clnt_addr
  end.

Definition next_state (state: ServerState) (input: ServerEvent) : Ret (ServerState * option Packet) :=
  match state with
  | NotStarted =>
      match input with
      | Init port socket =>
          let new_state := {| port := port ; socket := socket ; connections := nil |} in
          Ok (Running new_state, None)
      | _ => Error (Some "Unexpected event in NotStarted state")
      end
  | Running sdata =>
      match input with
      | Received packet =>
          match parse_packet packet.(data) with
          | Ok parsed_packet =>
            log_message (packet_to_string parsed_packet) (fun _ =>
                match handle_packet parsed_packet sdata packet.(addr) with
                | Ok (out_packet, new_sdata) =>
                  let response := serialize_packet out_packet in
                  let opacket := {| data := response ; addr := packet.(addr) |} in
                  Ok (Running new_sdata, Some opacket)
                | Error e => Error e
                end)
          | Error e => log_message ("Failed to parse packet: " ++ err_to_string e) (
            fun _ => Ok (Running sdata, None))
          end
      | _ => Error (Some "Unexpected event in Running state")
      end
  | Stopped => Error (Some "Server is stopped")
  end.