Require Import String.
Require Import List.
Require Import Definitions.
Require Import CoqPacket.
Require Import CoqUtils.

Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.

Definition database : list User := [
  {| u_username := "user1" ; u_password := "pass1" |} ;
  {| u_username := "user2" ; u_password := "pass2" |} ;
  {| u_username := "user3" ; u_password := "pass3" |} ;
  {| u_username := "user4" ; u_password := "pass4" |} ;
  {| u_username := "user5" ; u_password := "pass5" |}
].

Definition THandlePacket : Type := Ret (ParsedPacket * ServerData).  

Definition handle_login (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_response (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_change (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_follow (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_connect (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_superuser (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_logout (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_reload (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_slip_on (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_slip_off (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_slip_addr (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  Ok (packet, sdata).

Definition handle_packet (packet: ParsedPacket) (sdata: ServerData) : THandlePacket :=
  match packet.(type) with
  | PacketLogin => handle_login packet sdata  
  | PacketResponse => handle_response packet sdata
  | PacketChange => handle_change packet sdata
  | PacketFollow => handle_follow packet sdata
  | PacketConnect => handle_connect packet sdata
  | PacketSuperuser => handle_superuser packet sdata
  | PacketLogout => handle_logout packet sdata
  | PacketReload => handle_reload packet sdata
  | PacketSlipOn => handle_slip_on packet sdata
  | PacketSlipOff => handle_slip_off packet sdata
  | PacketSlipAddr => handle_slip_addr packet sdata
  end.

Definition next_state (state: ServerState) (input: ServerEvent) : Ret (ServerState * option Packet) :=
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
            match  (println (packet_to_string parsed_packet)) with
            | tt =>
                match handle_packet parsed_packet sdata with
                | Ok (out_packet, new_sdata) =>
                  let response := serialize_packet out_packet in
                  let opacket := {| data := response ; addr := packet.(addr) |} in
                  Ok (Running new_sdata, Some opacket)
                | Error e => Error e
                end
            end
          | Error e => Error e (*Ok (Running sdata, None) (*TODO: log*)*)
          end
      | _ => Error (Some "Unexpected event in Running state")
      end
  | Stopped => Error (Some "Server is stopped")
  end.