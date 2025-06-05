Require Import ZArith.
Require Import Sint63.
Require Import String.
Require Import Ascii.
Require Import Definitions.
Require Import CoqUtils.
Require Import CoqArithUtils.
Require Import Lia.

Include Protocol.

Open Scope string_scope.

(* VersionType *)

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

Definition version_to_string (v: VersionType) : string :=
  match v with
  | Simple => "Simple"%string
  | Extended => "Extended"%string
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


(* PacketType *)

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

Definition packet_type_to_string (pt: PacketType) : string :=
  match pt with
  | PacketLogin => "Login"%string
  | PacketResponse => "Response"%string
  | PacketChange => "Change"%string
  | PacketFollow => "Follow"%string
  | PacketConnect => "Connect"%string
  | PacketSuperuser => "Superuser"%string
  | PacketLogout => "Logout"%string
  | PacketReload => "Reload"%string
  | PacketSlipOn => "SlipOn"%string
  | PacketSlipOff => "SlipOff"%string
  | PacketSlipAddr => "SlipAddr"%string
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


(* ResponseType *)

Definition response_type_of_ascii (c: ascii) : option ResponseType :=
  match c with
  | "000"%char => Some ResponseNone
  | "001"%char => Some ResponseAccepted
  | "002"%char => Some ResponseRejected
  | _ => None
  end.

Definition ascii_of_response_type (rt: ResponseType) : ascii :=
  match rt with
  | ResponseNone => Ascii.ascii_of_nat 0
  | ResponseAccepted => Ascii.ascii_of_nat 1
  | ResponseRejected => Ascii.ascii_of_nat 2
  end.

Definition response_type_to_string (rt: ResponseType) : string :=
  match rt with
  | ResponseNone => "None"%string
  | ResponseAccepted => "Accepted"%string
  | ResponseRejected => "Rejected"%string
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


(* ReasonType *)

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

Definition reason_type_to_string (rt: ReasonType) : string :=
  match rt with
  | ReasonNone => "None"%string
  | ReasonExpiring => "Expiring"%string
  | ReasonPassword => "Password"%string
  | ReasonDenied => "Denied"%string
  | ReasonQuit => "Quit"%string
  | ReasonIdle => "Idle"%string
  | ReasonDrop => "Drop"%string
  | ReasonBad => "Bad"%string
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


(* Other *)

Definition parse_2byte_number (data: string): option (int * string) :=
  match data with
  | String b1 (String b2 tl) =>
    let n1 := of_nat (nat_of_ascii b1) in
    let n2 := of_nat (nat_of_ascii b2) in
    let n := (256 * n1 + n2)%sint63 in
    Some (n, tl)
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
    let n := Uint63.of_nat (nat_of_ascii b1) in
    Ok (n, tl)
  | _ => Error (Some "Invalid user length format"%string)
  end.

Definition parse_password_len (data: string): Result (int * string) ErrorMsg :=
  match data with
  | String b1 tl =>
    let n := of_nat (nat_of_ascii b1) in
    Ok (n, tl)
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

Definition destination_address_to_string (addr: IPAddress): string :=
  let '(b1, b2, b3, b4) := addr in
  let n1 := of_nat (nat_of_ascii b1) in
  let n2 := of_nat (nat_of_ascii b2) in
  let n3 := of_nat (nat_of_ascii b3) in
  let n4 := of_nat (nat_of_ascii b4) in
  int_to_string n1 ++ "." ++
  int_to_string n2 ++ "." ++
  int_to_string n3 ++ "." ++
  int_to_string n4.

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

Definition parse_username (data: string) (len: int): Ret (string * string) :=
  if (to_Z len <? 0)%Z then
    Error (Some "Invalid username length"%string)
  else
    let username := substring 0 (to_nat len) data in
    let remaining := substring (to_nat len) (String.length data - to_nat len) data in
    if ((of_nat (String.length username)) =? len)%sint63 then
      Ok (username, remaining)
    else
      Error (Some "Invalid username format"%string).

Definition parse_password (data: string) (len: int): Ret (string * string) :=
  if (to_Z len <? 0)%Z then
    Error (Some "Invalid password length"%string)
  else
    let password := substring 0 (to_nat len) data in
    let remaining := substring (to_nat len) (String.length data - to_nat len) data in
    if ((of_nat (String.length password)) =? len)%sint63 then
      Ok (password, remaining)
    else
      Error (Some "Invalid password format"%string).


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
  | Ok (version, tl) =>
    match parse_packet_type tl with
    | Error msg => Error msg
    | Ok (packet_type, tl) =>
      match parse_nonce tl with
      | Error msg => Error msg
      | Ok (nonce, tl) =>
        match parse_user_len tl with
        | Error msg => Error msg
        | Ok (user_len, tl) =>
          match parse_password_len tl with
          | Error msg => Error msg
          | Ok (password_len, tl) =>
            match parse_response tl with
            | Error msg => Error msg
            | Ok (response, tl) =>
              match parse_reason tl with
              | Error msg => Error msg
              | Ok (reason, tl) =>
                match parse_4byte_result tl "1"%string with
                | Error msg => Error msg
                | Ok (result1, tl) =>
                  match parse_destination_address tl with
                  | Error msg => Error msg
                  | Ok (destination_addr, tl) =>
                    match parse_destination_port tl with
                    | Error msg => Error msg
                    | Ok (destination_port, tl) =>
                      match parse_line tl with
                      | Error msg => Error msg
                      | Ok (line, tl) =>
                        match parse_4byte_result tl "2"%string with
                        | Error msg => Error msg
                        | Ok (result2, tl) =>
                          match parse_2byte_result tl with
                          | Error msg => Error msg
                          | Ok (result3, tl) =>
                            match parse_username tl user_len with
                            | Error msg => Error msg
                            | Ok (username, tl) =>
                              match parse_password tl password_len with
                              | Error msg => Error msg
                              | Ok (password, tl) =>
                                match tl with
                                | EmptyString => Ok ({|
                                    version := version ;
                                    kind := packet_type ;
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
                                    p_username := username ;
                                    p_password := password ;
                                  |})
                                | _ => Error (Some "Found data after end of packet")
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
        end
      end
    end
  end.

Definition char_of_int (n: int) : ascii :=
  ascii_of_nat (Z.to_nat (to_Z n)).

Definition serialize_version (vt: VersionType) : string :=
  String (ascii_of_version_type vt) "".

Definition serialize_packet_type (pt: PacketType) : string :=
  String (ascii_of_packet_type pt) "".

Definition serialize_short (n: int) : string :=
  let high := (to_Z (n / 256)%sint63) in
  let low := (to_Z (n mod 256)%sint63) in
  String (ascii_of_nat (Z.to_nat high)) (String (ascii_of_nat (Z.to_nat low)) "").

Definition serialize_byte (n: int) : string :=
  String (char_of_int n) "".

Definition serialize_ip_address (addr: IPAddress) : string :=
  let '(b1, b2, b3, b4) := addr in
  String b1 (String b2 (String b3 (String b4 ""))).

Definition serialize_response (rt: ResponseType) : string :=
  String (ascii_of_response_type rt) "".

Definition serialize_reason (rt: ReasonType) : string :=
  String (ascii_of_reason_type rt) "".

Definition serialize_packet (p: ParsedPacket) : string :=
  serialize_version p.(version) ++
  serialize_packet_type p.(kind) ++
  serialize_short p.(nonce) ++
  serialize_byte p.(user_len) ++
  serialize_byte p.(password_len) ++
  serialize_response p.(response) ++
  serialize_reason p.(reason) ++
  p.(result1) ++
  serialize_ip_address p.(destination_addr) ++
  serialize_short p.(destination_port) ++
  serialize_short p.(line) ++
  p.(result2) ++
  p.(result3) ++
  p.(p_username) ++
  p.(p_password).

Definition packet_to_string (p: ParsedPacket) : string :=
  let version_str := version_to_string p.(version) in
  let packet_type_str := packet_type_to_string p.(kind) in
  let nonce_str := int_to_string p.(nonce) in
  let user_len_str := int_to_string p.(user_len) in
  let password_len_str := int_to_string p.(password_len) in
  let response_str := response_type_to_string p.(response) in
  let reason_str := reason_type_to_string p.(reason) in
  let result1_str := p.(result1) in
  let destination_addr_str := destination_address_to_string p.(destination_addr) in
  let destination_port_str := int_to_string p.(destination_port) in
  let line_str := int_to_string p.(line) in
  let result2_str := p.(result2) in
  let result3_str := p.(result3) in
  "[PACKET]" ++ newline ++
  "Version: " ++ version_str ++ newline ++
  "Kind: " ++ packet_type_str ++ newline ++
  "Nonce: " ++ nonce_str ++ newline ++
  "User Length: " ++ user_len_str ++ newline ++
  "Password Length: " ++ password_len_str ++ newline ++
  "Response: " ++ response_str ++ newline ++
  "Reason: " ++ reason_str ++ newline ++
  "Result 1: " ++ result1_str ++ newline ++
  "Destination Address: " ++ destination_addr_str ++ newline ++
  "Destination Port: " ++ destination_port_str ++ newline ++
  "Line: " ++ line_str ++ newline ++
  "Result 2: " ++ result2_str ++ newline ++
  "Result 3: " ++ result3_str ++ newline ++
  "Username: " ++ p.(p_username) ++ newline ++
  "Password: " ++ p.(p_password).

Lemma ascii_of_version_type_non_empty:
  forall vt, (String (ascii_of_version_type vt) "") <> "".
Proof.
  intros.
  destruct vt; congruence.
Qed.

Lemma string_len_4:
  forall s,
  String.length s = 4 -> exists b1 b2 b3 b4, s = String b1 (String b2 (String b3 (String b4 ""))).
Proof.
  intros.
  destruct s as [|b1 [|b2 [|b3 [|b4 tl]]]].
  * simpl in H. congruence.
  * simpl in H. congruence.
  * simpl in H. congruence.
  * simpl in H. congruence.
  * exists b1, b2, b3, b4.
    destruct tl.
    ** reflexivity.
    ** simpl in H. congruence.
Qed.  


Lemma string_len_2:
  forall s,
  String.length s = 2 -> exists b1 b2, s = String b1 (String b2 "").
Proof.
  intros.
  destruct s as [|b1 [|b2 tl]].
  * simpl in H. congruence.
  * simpl in H. congruence.
  * exists b1, b2.
    destruct tl.
    ** reflexivity.
    ** simpl in H. congruence.
Qed.

Lemma serialize_parse_byte:
  forall (n: int),
    is_one_byte n -> of_nat (nat_of_ascii (char_of_int n)) = n.
Proof.
  intros.
  unfold char_of_int.
  simpl.
Admitted.

(* Lemma serialize_parse_two_byte:
  forall (n: int),
    is_two_byte n ->
    (256 * of_nat (nat_of_ascii (char_of_int (n / 256))) + of_nat (nat_of_ascii (char_of_int (n mod 256))))%sint63 = n.
Proof.
  intros.
  unfold char_of_int.
Admitted. *)

Lemma to_nat_of_nat2:
  forall (n: int),
    (0 <=? to_Z n)%Z = true -> of_nat (to_nat n) = n.
Proof.
  intros n H.
Admitted.

Lemma prefix_correct2:
  forall (s: string) (tl: string),
    substring 0 (String.length s) (s ++ tl) = s.
Proof.
  intros s tl.
  induction s.
  * simpl.
    destruct tl; now simpl.
  * simpl.
    now rewrite IHs.
Qed.

Lemma substring_skip:
  forall (s1 s2: string),
    substring (length s1) (length (s1 ++ s2) - length s1) (s1 ++ s2) = s2.
Proof.
  intros s1 s2.
  induction s1.
  * simpl.
    replace (length s2 - 0) with (length s2) by lia.
    apply prefix_correct.
    induction s2.
    ** now simpl.
    ** simpl.
       rewrite IHs2.
       destruct (ascii_dec a a).
       *** reflexivity.
       *** contradiction.
  * simpl.
    now rewrite IHs1.
Qed.  

Lemma substring_skip2:
  forall (s1: string),
    substring (length s1) 0 s1 = "".
Proof.
  intros.
  induction s1.
  * now simpl.
  * simpl.
    rewrite IHs1.
    reflexivity.
Qed. 

Lemma prefix_eq:
  forall (s1: string),
    prefix s1 s1 = true.
Proof.
  intros s1.
  unfold prefix.
  induction s1.
  * now simpl.
  * simpl.
    rewrite IHs1.
    destruct ascii_dec.
    ** reflexivity.
    ** contradiction.
Qed.

Lemma prefix_correct3:
  forall (s1: string),
    substring 0 (String.length s1) s1 = s1.
Proof.
  intros.
  induction s1.
  * now simpl.
  * simpl.
    now rewrite IHs1.
Qed. 

Lemma serialize_parse_packet_id:
  forall (p: ParsedPacket) (s: string),
     (String.length p.(result1) = 4) ->
     (String.length p.(result2) = 4) ->
     (String.length p.(result3) = 2) ->
     (is_one_byte p.(user_len)) ->
     (is_one_byte p.(password_len)) ->
     (is_two_byte p.(nonce)) ->
     (is_two_byte p.(destination_port)) ->
     (is_two_byte p.(line)) ->
     (String.length (p.(p_username)) = to_nat p.(user_len)) ->
     (String.length (p.(p_password)) = to_nat p.(password_len)) ->
     s = serialize_packet p -> parse_packet s = Ok p.
Proof.
  intros p s Hlen1 Hlen2 Hlen3 HUlen HUpass HNonce HDest HLine HUlenStr HUpassStr H.
  unfold serialize_packet in H.
  subst s.
  unfold parse_packet.
  unfold parse_version.
  destruct (serialize_version (version p)) eqn:Hv.
  * apply ascii_of_version_type_non_empty in Hv. contradiction.
  * remember (
    serialize_packet_type (kind p) ++
    serialize_short (nonce p) ++
    serialize_byte (user_len p) ++
    serialize_byte (password_len p) ++
    serialize_response (response p) ++
    serialize_reason (reason p) ++
    result1 p ++
    serialize_ip_address (destination_addr p) ++
    serialize_short (destination_port p) ++
    serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
  ) as rest.
    simpl. injection Hv. intros. subst a s. clear Hv.
    rewrite version_ascii_id2.
    simpl.
    remember (serialize_short (nonce p) ++
      serialize_byte (user_len p) ++
      serialize_byte (password_len p) ++
      serialize_response (response p) ++
      serialize_reason (reason p) ++
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest2 in Heqrest.
    subst rest.
    simpl.
    rewrite packet_ascii_id2.
    remember (
      serialize_byte (user_len p) ++
      serialize_byte (password_len p) ++
      serialize_response (response p) ++
      serialize_reason (reason p) ++
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest3 in Heqrest2.
    subst rest2.
    simpl.
    remember (
      serialize_byte (password_len p) ++
      serialize_response (response p) ++
      serialize_reason (reason p) ++
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest4 in Heqrest3.
    subst rest3.
    simpl.
    remember (
      serialize_response (response p) ++
      serialize_reason (reason p) ++
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest5 in Heqrest4.
    subst rest4.
    simpl.
    remember (
      serialize_reason (reason p) ++
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest6 in Heqrest5.
    subst rest5.
    simpl.
    rewrite response_ascii_id2.
    remember (
      result1 p ++
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest7 in Heqrest6.
    subst rest6.
    simpl.
    rewrite reason_ascii_id2.
    remember (
      serialize_ip_address (destination_addr p) ++
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest8 in Heqrest7.
    subst rest7.
    apply string_len_4 in Hlen1.
    destruct Hlen1 as [b11 [b12 [b13 [b14 Hlen1]]]].
    rewrite Hlen1.
    simpl.
    remember (
      serialize_short (destination_port p) ++
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest9 in Heqrest8.
    subst rest8.
    destruct (destination_addr p) as [ip1 ip4] eqn:Heqip.
    destruct ip1 as [ip1 ip3].
    destruct ip1 as [ip1 ip2].
    unfold serialize_ip_address.
    simpl.
    remember (
      serialize_short (line p) ++ result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest10 in Heqrest9.
    subst rest9.
    simpl.
    remember (
      result2 p ++ result3 p ++ p_username p ++ p_password p
    ) as rest11 in Heqrest10.
    subst rest10.
    simpl.
    remember (
      result3 p ++ p_username p ++ p_password p
    ) as rest12 in Heqrest11.
    subst rest11.
    apply string_len_4 in Hlen2.
    destruct Hlen2 as [b21 [b22 [b23 [b24 Hlen2]]]].
    rewrite Hlen2.
    simpl.
    remember (
      p_username p ++ p_password p
    ) as rest13 in Heqrest12.
    subst rest12.
    apply string_len_2 in Hlen3.
    destruct Hlen3 as [b31 [b32 Hlen3]].
    rewrite Hlen3.
    simpl.
    remember (p_password p) as rest14 in Heqrest13.
    subst rest13.
    unfold parse_username.
    rewrite serialize_parse_byte.
    all: swap 1 2.
    congruence.
    destruct (to_Z (user_len p) <? 0)%Z eqn:HUlen2.
    ** generalize (is_one_byte_negative (user_len p)). intro HNeg.
       specialize (HNeg HUlen).
       congruence.
    ** rewrite <- HUlenStr. 
       rewrite -> prefix_correct2.
       rewrite HUlenStr.
       rewrite to_nat_of_nat2.
       all: swap 1 2.
       rewrite is_one_byte_non_negative. reflexivity. congruence.
       rewrite Uint63.eqb_refl.
       rewrite serialize_parse_byte.
       all: swap 1 2.
       congruence.
       rewrite <- HUlenStr.
       rewrite substring_skip.
       subst rest14.
       unfold parse_password.
       destruct (to_Z (password_len p) <? 0)%Z eqn:HUpass2.
       ***  generalize (is_one_byte_negative (password_len p)). intro HNeg.
            specialize (HNeg HUpass).
            congruence.
       *** rewrite <- HUpassStr.
           rewrite prefix_correct3.
           rewrite HUpassStr.
           rewrite to_nat_of_nat2.
           all: swap 1 2.
           rewrite is_one_byte_non_negative. reflexivity. congruence.
           rewrite Uint63.eqb_refl.
           rewrite <- HUpassStr.
           replace (length (p_password p) - length (p_password p)) with 0 by lia.
           rewrite substring_skip2.
           remember (
            (256 * of_nat (nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (nonce p / 256))))) +
of_nat (nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (nonce p mod 256))))))%sint63
           ) as n1.
           admit.
           (* rewrite split_two_bytes_eq_init in n1.

           repeat rewrite serialize_parse_two_byte.
           rewrite <- Heqip.
           rewrite <- Hlen1.
           rewrite <- Hlen2.
           rewrite <- Hlen3.
           destruct p.
           simpl.
           reflexivity. *)
Admitted.