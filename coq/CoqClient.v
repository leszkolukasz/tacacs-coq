Require Import String.
Require Import List.
Require Import Sint63.
Require Import Uint63.
Require Import Definitions.
Require Import CoqPacket.
Require Import CoqUtils.
Require Import CoqDatabase.

Open Scope string_scope.

Definition handle_response_packet (packet: ParsedPacket) : Ret ParsedPacket :=
  match packet.(kind) with
  | PacketResponse => Ok packet
  | _ => Error (Some "Unexpected response packet type")
  end.

Definition create_login_packet (username password: string) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketLogin;
    nonce := of_nat 2;
    user_len := of_nat (String.length username);
    password_len := of_nat (String.length password);
    response := ResponseNone;
    reason := ReasonNone;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := (Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0, 
                         Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0);
    destination_port := of_nat 0;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := username;
    p_password := password;
  |}.

Definition create_superuser_packet (username password: string) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketSuperuser;
    nonce := of_nat 2;
    user_len := of_nat (String.length username);
    password_len := of_nat (String.length password);
    response := ResponseNone;
    reason := ReasonNone;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := (Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0, 
                         Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0);
    destination_port := of_nat 0;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := username;
    p_password := password;
  |}.

Definition create_connect_packet (dest_addr: IPAddress) (dest_port: int) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketConnect;
    nonce := of_nat 2;
    user_len := of_nat 0;
    password_len := of_nat 0;
    response := ResponseNone;
    reason := ReasonNone;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := dest_addr;
    destination_port := dest_port;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := "";
    p_password := "";
  |}.

Definition create_logout_packet (username password: string) (line_num: int) (reason: ReasonType) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketLogout;
    nonce := of_nat 2;
    user_len := of_nat (String.length username);
    password_len := of_nat (String.length password);
    response := ResponseNone;
    reason := reason;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := (Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0, 
                         Ascii.ascii_of_nat 0, Ascii.ascii_of_nat 0);
    destination_port := of_nat 0;
    line := line_num;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := username;
    p_password := password;
  |}.

Definition create_slip_addr_packet (addr: IPAddress) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketSlipAddr;
    nonce := of_nat 2;
    user_len := of_nat 0;
    password_len := of_nat 0;
    response := ResponseNone;
    reason := ReasonNone;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := addr;
    destination_port := of_nat 0;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := "";
    p_password := "";
  |}.

Definition create_slip_on_packet (addr: IPAddress) : ParsedPacket :=
  {|
    version := Extended;
    kind := PacketSlipOn;
    nonce := of_nat 2;
    user_len := of_nat 0;
    password_len := of_nat 0;
    response := ResponseNone;
    reason := ReasonNone;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := addr;
    destination_port := of_nat 0;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := "";
    p_password := "";
  |}.

Definition create_slip_off_packet (addr: IPAddress): ParsedPacket :=
  {|
    version := Extended;
    kind := PacketSlipOff;
    nonce := of_nat 2;
    user_len := of_nat 0;
    password_len := of_nat 0;
    response := ResponseNone;
    reason := ReasonQuit;
    result1 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    destination_addr := addr;
    destination_port := of_nat 0;
    line := of_nat 1;
    result2 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "")));
    result3 := String (Ascii.ascii_of_nat 0)
              (String (Ascii.ascii_of_nat 0) "");
    p_username := "";
    p_password := "";
  |}.

Definition build_and_serialize_packet (packet_type: PacketType) 
                                     (username password: string)
                                     (dest_addr: IPAddress)
                                     (dest_port: int) : Ret string :=
  let packet := match packet_type with
                | PacketLogin => create_login_packet username password
                | PacketSuperuser => create_superuser_packet username password
                | PacketConnect => create_connect_packet dest_addr dest_port
                | PacketLogout => create_logout_packet username password (of_nat 1) ReasonQuit
                | PacketSlipAddr => create_slip_addr_packet dest_addr
                | PacketSlipOn => create_slip_on_packet dest_addr
                | PacketSlipOff => create_slip_off_packet dest_addr
                | _ => create_login_packet "" ""
                end in
  Ok (serialize_packet packet).

Definition is_success_response (packet: ParsedPacket) : bool :=
  eqb_response_type packet.(response) ResponseAccepted.

Definition get_response_reason (packet: ParsedPacket) : string :=
  (response_type_to_string packet.(response)) ++ ": " ++ (reason_type_to_string packet.(reason)).