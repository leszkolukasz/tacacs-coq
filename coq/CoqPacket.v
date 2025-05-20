Require Import Sint63.
Require Import String.
Require Import Ascii.
Require Import Definitions.

Include Protocol.

Definition version_type_of_ascii (c: ascii) : option VersionType :=
  match c with
  | "000"%char => Some Simple
  | "128"%char => Some Extended
  | _ => None
  end.

Definition ascii_of_version_type (vt: VersionType) : ascii :=
  match vt with
  | Simple => Ascii.ascii_of_nat 0
  | Extended => Ascii.ascii_of_nat 128
  end.

Definition parse_version (data: string) : Result (VersionType * string) ErrorMsg :=
  match data with
  | String b tl =>
    match version_type_of_ascii b with
    | Some vt => Ok (vt, tl)
    | None => Error (Some "Invalid version type"%string)
    end
  | _ => Error (Some "Invalid data format when parsing version"%string)
  end.

Lemma version_ascii_id1:
  forall c v, version_type_of_ascii c = Some v -> ascii_of_version_type v = c.
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct b, b0, b1, b2, b3, b4, b5, b6; try inversion H; subst; reflexivity.
Qed. 

Lemma version_ascii_id2:
  forall v, version_type_of_ascii (ascii_of_version_type v) = Some v.
Proof.
  intros.
  destruct v; now simpl.
Qed.

Definition packet_type_of_ascii (c: ascii) : option PacketType :=
  match c with
  | "001"%char => Some PacketLogin
  | "002"%char => Some PacketResponse
  | "003"%char => Some PacketChange
  | "004"%char => Some PacketFollow
  | "005"%char => Some PacketConnect
  | "006"%char => Some PacketSuperuser
  | "007"%char => Some PacketLogout
  | "008"%char => Some PacketReload
  | "009"%char => Some PacketSlipOn
  | "010"%char => Some PacketSlipOff
  | "011"%char => Some PacketSlipAddr
  | _ => None
  end.

Definition ascii_of_packet_type (pt: PacketType) : ascii :=
  match pt with
  | PacketLogin => Ascii.ascii_of_nat 1
  | PacketResponse => Ascii.ascii_of_nat 2
  | PacketChange => Ascii.ascii_of_nat 3
  | PacketFollow => Ascii.ascii_of_nat 4
  | PacketConnect => Ascii.ascii_of_nat 5
  | PacketSuperuser => Ascii.ascii_of_nat 6
  | PacketLogout => Ascii.ascii_of_nat 7
  | PacketReload => Ascii.ascii_of_nat 8
  | PacketSlipOn => Ascii.ascii_of_nat 9
  | PacketSlipOff => Ascii.ascii_of_nat 10
  | PacketSlipAddr => Ascii.ascii_of_nat 11
  end.

Definition parse_packet_type (data: string) : Result (PacketType * string) ErrorMsg :=
  match data with
  | String b tl =>
    match packet_type_of_ascii b with
    | Some pt => Ok (pt, tl)
    | None => Error (Some "Invalid packet type"%string)
    end
  | _ => Error (Some "Invalid data format when parsing packet type"%string)
  end.

Lemma packet_ascii_id1:
  forall c p, packet_type_of_ascii c = Some p -> ascii_of_packet_type p = c.
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct b, b0, b1, b2, b3, b4, b5, b6; try inversion H; subst; reflexivity.
Qed.

Lemma packet_ascii_id2:
  forall p, packet_type_of_ascii (ascii_of_packet_type p) = Some p.
Proof.
  intros.
  destruct p; now simpl.
Qed.

Definition response_type_of_ascii (c: ascii) : option ResponseType :=
  match c with
  | "001"%char => Some Accepted
  | "002"%char => Some Rejected
  | _ => None
  end.

Definition ascii_of_response_type (rt: ResponseType) : ascii :=
  match rt with
  | Accepted => Ascii.ascii_of_nat 1
  | Rejected => Ascii.ascii_of_nat 2
  end.

Definition parse_response (data: string) : Result (ResponseType * string) ErrorMsg :=
  match data with
  | String b tl =>
    match response_type_of_ascii b with
    | Some rt => Ok (rt, tl)
    | None => Error (Some "Invalid response type"%string)
    end
  | _ => Error (Some "Invalid data format when parsing response type"%string)
  end.

Lemma response_ascii_id1:
  forall c r, response_type_of_ascii c = Some r -> ascii_of_response_type r = c.
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct b, b0, b1, b2, b3, b4, b5, b6; try inversion H; subst; reflexivity.
Qed.

Lemma response_ascii_id2:
  forall r, response_type_of_ascii (ascii_of_response_type r) = Some r.
Proof.
  intros.
  destruct r; now simpl.
Qed.

Definition reason_type_of_ascii (c: ascii) : option ReasonType :=
  match c with
  | "000"%char => Some ReasonNone
  | "001"%char => Some ReasonExpiring
  | "002"%char => Some ReasonPassword
  | "003"%char => Some ReasonDenied
  | "004"%char => Some ReasonQuit
  | "005"%char => Some ReasonIdle
  | "006"%char => Some ReasonDrop
  | "007"%char => Some ReasonBad
  | _ => None
  end.

Definition ascii_of_reason_type (rt: ReasonType) : ascii :=
  match rt with
  | ReasonNone => Ascii.ascii_of_nat 0
  | ReasonExpiring => Ascii.ascii_of_nat 1
  | ReasonPassword => Ascii.ascii_of_nat 2
  | ReasonDenied => Ascii.ascii_of_nat 3
  | ReasonQuit => Ascii.ascii_of_nat 4
  | ReasonIdle => Ascii.ascii_of_nat 5
  | ReasonDrop => Ascii.ascii_of_nat 6
  | ReasonBad => Ascii.ascii_of_nat 7
  end.

Definition parse_reason (data: string) : Result (ReasonType * string) ErrorMsg :=
  match data with
  | String b tl =>
    match reason_type_of_ascii b with
    | Some rt => Ok (rt, tl)
    | None => Error (Some "Invalid reason type"%string)
    end
  | _ => Error (Some "Invalid data format when parsing reason type"%string)
  end.

Lemma reason_ascii_id1:
  forall c r, reason_type_of_ascii c = Some r -> ascii_of_reason_type r = c.
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct b, b0, b1, b2, b3, b4, b5, b6; try inversion H; subst; reflexivity.
Qed.

Lemma reason_ascii_id2:
  forall r, reason_type_of_ascii (ascii_of_reason_type r) = Some r.
Proof.
  intros.
  destruct r; now simpl.
Qed.

Definition parse_2byte_number (data: string): option (int * string) :=
  match data with
  | String b1 (String b2 tl) =>
    (* let n1 := of_nat (nat_of_ascii b1) in
    let n2 := of_nat (nat_of_ascii b2) in
    let n := (256 * n1 + n2)%sint63 in *)
    Some (10%sint63, tl)
  | _ => None
  end.

Definition parse_nonce (data: string): Result (int * string) ErrorMsg :=
  match parse_2byte_number data with
  | Some (n, tl) => Ok (n, tl)
  | None => Error (Some "Invalid nonce format"%string)
  end.

Definition parse_user_len (data: string): Result (int * string) ErrorMsg :=
  match data with
  | String b1 tl =>
    (* let n := Uint63.of_nat (nat_of_ascii b1) in *)
    Ok (10%sint63, tl)
  | _ => Error (Some "Invalid user length format"%string)
  end.

Definition parse_password_len (data: string): Result (int * string) ErrorMsg :=
  match data with
  | String b1 tl =>
    (* let n := of_nat (nat_of_ascii b1) in *)
    Ok (100%sint63, tl)
  | _ => Error (Some "Invalid password length format"%string)
  end.

Definition parse_4byte_result (data: string) (num: string): Result (string * string) ErrorMsg :=
  match data with
  | String b1 (String b2 (String b3 (String b4 tl))) =>
    let result := String b1 (String b2 (String b3 (String b4 ""%string))) in
    Ok (result, tl)
  | _ => Error (Some ("Invalid result" ++ num ++ " format")%string)
  end.

Definition parse_2byte_result (data: string): Result (string * string) ErrorMsg :=
  match data with
  | String b1 (String b2 tl) =>
    let result := String b1 (String b2 ""%string) in
    Ok (result, tl)
  | _ => Error (Some "Invalid result3 format"%string)
  end.

Definition parse_destination_address (data: string): Result (IPAddress * string) ErrorMsg :=
  match data with
  | String b1 (String b2 (String b3 (String b4 tl))) =>
    let addr := (b1, b2, b3, b4) in
    Ok (addr, tl)
  | _ => Error (Some "Invalid destination address format"%string)
  end.

Definition parse_destination_port (data: string): Result (int * string) ErrorMsg :=
  match parse_2byte_number data with
  | Some (n, tl) => Ok (n, tl)
  | None => Error (Some "Invalid destination port format"%string)
  end.

Definition parse_line (data: string): Result (int * string) ErrorMsg :=
  match parse_2byte_number data with
  | Some (n, tl) => Ok (n, tl)
  | None => Error (Some "Invalid line format"%string)
  end.

(*
0                   1                   2                   3
0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:    Version    :     Type      :             Nonce             :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:   User len    : Password len  :   Response    :    Reason     :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:                           Result 1                            :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:                      Destination Address                      :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:           Dest Port           :             Line              :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:                           Result 2                            :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
:           Result 3            :            data...            :
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*)

Definition parse_packet (data: string): Result ParsedPacket ErrorMsg :=
  match parse_version data with
  | Error msg => Error msg
  | Ok (version, tl1) =>
    match parse_packet_type tl1 with
    | Error msg => Error msg
    | Ok (packet_type, tl2) =>
      match parse_nonce tl2 with
      | Error msg => Error msg
      | Ok (nonce, tl3) =>
        match parse_user_len tl3 with
        | Error msg => Error msg
        | Ok (user_len, tl4) =>
          match parse_password_len tl4 with
          | Error msg => Error msg
          | Ok (password_len, tl5) =>
            match parse_response tl5 with
            | Error msg => Error msg
            | Ok (response, tl6) =>
              match parse_reason tl6 with
              | Error msg => Error msg
              | Ok (reason, tl7) =>
                match parse_4byte_result tl7 "1"%string with
                | Error msg => Error msg
                | Ok (result1, tl8) =>
                  match parse_destination_address tl8 with
                  | Error msg => Error msg
                  | Ok (destination_addr, tl9) =>
                    match parse_destination_port tl9 with
                    | Error msg => Error msg
                    | Ok (destination_port, tl10) =>
                      match parse_line tl10 with
                      | Error msg => Error msg
                      | Ok (line, tl11) =>
                        match parse_4byte_result tl11 "2"%string with
                        | Error msg => Error msg
                        | Ok (result2, tl12) =>
                          match parse_2byte_result tl12 with
                          | Error msg => Error msg
                          | Ok (result3, _) =>
                            Ok ({|
                              version := version ;
                              type := packet_type ;
                              nonce := nonce ;
                              user_len := user_len ;
                              password_len := password_len ;
                              response := response ;
                              reason := reason ;
                              result1 := result1 ;
                              destination_addr := destination_addr ;
                              destination_port := destination_port ;
                              line := line ;
                              result2 := result2 ;
                              result3 := result3 ;
                            |})
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  end.