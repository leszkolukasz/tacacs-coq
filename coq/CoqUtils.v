Require Import String.
Require Import Uint63.
Require Import Sint63.
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Ascii.

Require Import Definitions.

Include Protocol.

Open Scope bool.
Open Scope string_scope.

Definition newline : string :=
  String (Ascii.ascii_of_nat 10) "".

Definition eqb_response_type (r1 r2: ResponseType) : bool :=
	match r1, r2 with
	| ResponseNone, ResponseNone => true
	| ResponseAccepted, ResponseAccepted => true
	| ResponseRejected, ResponseRejected => true
	| _, _ => false
	end.

Definition pipe {A B: Type} (x: A) (f: A -> B) : B := f x.

Infix "|>" := pipe (at level 50, left associativity).

Definition with_packet_type (t: PacketType) (packet: ParsedPacket) : ParsedPacket :=
	{|
		version := packet.(version);
		kind := t;
		nonce := packet.(nonce);
		user_len := packet.(user_len);
		password_len := packet.(password_len);
		response := packet.(response);
		reason := packet.(reason);
		result1 := packet.(result1);
		destination_addr := packet.(destination_addr);
		destination_port := packet.(destination_port);
		line := packet.(line);
		result2 := packet.(result2);
		result3 := packet.(result3);
		p_username := packet.(p_username);
		p_password := packet.(p_password);
	|}.

Definition with_response_type (r: ResponseType) (packet: ParsedPacket) : ParsedPacket :=
	{|
		version := packet.(version);
		kind := packet.(kind);
		nonce := packet.(nonce);
		user_len := packet.(user_len);
		password_len := packet.(password_len);
		response := r;
		reason := packet.(reason);
		result1 := packet.(result1);
		destination_addr := packet.(destination_addr);
		destination_port := packet.(destination_port);
		line := packet.(line);
		result2 := packet.(result2);
		result3 := packet.(result3);
		p_username := packet.(p_username);
		p_password := packet.(p_password);
	|}.

Definition with_reason_type (r: ReasonType) (packet: ParsedPacket) : ParsedPacket :=
	{|
		version := packet.(version);
		kind := packet.(kind);
		nonce := packet.(nonce);
		user_len := packet.(user_len);
		password_len := packet.(password_len);
		response := packet.(response);
		reason := r;
		result1 := packet.(result1);
		destination_addr := packet.(destination_addr);
		destination_port := packet.(destination_port);
		line := packet.(line);
		result2 := packet.(result2);
		result3 := packet.(result3);
		p_username := packet.(p_username);
		p_password := packet.(p_password);
	|}.

Definition with_results (r1 r2 r3: string) (packet: ParsedPacket) : ParsedPacket :=
	{|
		version := packet.(version);
		kind := packet.(kind);
		nonce := packet.(nonce);
		user_len := packet.(user_len);
		password_len := packet.(password_len);
		response := packet.(response);
		reason := packet.(reason);
		result1 := r1;
		destination_addr := packet.(destination_addr);
		destination_port := packet.(destination_port);
		line := packet.(line);
		result2 := r2;
		result3 := r3;
		p_username := packet.(p_username);
		p_password := packet.(p_password);
	|}.

Definition with_data (uname pwd : string) (packet: ParsedPacket) : ParsedPacket :=
	{|
		version := packet.(version);
		kind := packet.(kind);
		nonce := packet.(nonce);
		user_len := packet.(user_len); (* lengths need to be copied *)
		password_len := packet.(password_len);
		response := packet.(response);
		reason := packet.(reason);
		result1 := packet.(result1);
		destination_addr := packet.(destination_addr);
		destination_port := packet.(destination_port);
		line := packet.(line);
		result2 := packet.(result2);
		result3 := packet.(result3);
		p_username := uname;
		p_password := pwd;
	|}.

(* Returns a base packet which can be used to build a response packet. *)
Definition prepare_reponse_packet (r: ResponseType) (packet: ParsedPacket) : ParsedPacket :=
	packet 	|> with_packet_type PacketResponse
					|> with_response_type r
					|> with_reason_type (if eqb_response_type r ResponseAccepted then ReasonNone else ReasonDenied)
					|> with_results "" "" ""
					|> with_data "" "".

Definition rejected_packet (packet: ParsedPacket) : ParsedPacket :=
	prepare_reponse_packet ResponseRejected packet.

Definition accepted_packet (packet: ParsedPacket) : ParsedPacket :=
	prepare_reponse_packet ResponseAccepted packet.

Definition with_mode (m: ConnectionMode) (conn: Connection) : Connection :=
	{|
		client_addr := conn.(client_addr);
		mode := m;
		slip_addr := conn.(slip_addr);
	|}.

Definition with_slip_addr (addr: option Protocol.IPAddress) (conn: Connection) : Connection :=
	{|
		client_addr := conn.(client_addr);
		mode := conn.(mode);
		slip_addr := addr;
	|}.

Definition with_connections (conns: list Connection) (sdata: ServerData) : ServerData :=
	{|
		connections := conns;
		port := sdata.(port);
		socket := sdata.(socket);
	|}.

Definition find_connection (addr: sockaddr) (sdata: ServerData) : option Connection :=
  find (fun (conn: Connection) => eq_sockaddr conn.(client_addr) addr) sdata.(connections).

Definition add_connection (conn: Connection) (sdata: ServerData) : ServerData :=
	sdata |> with_connections (conn :: sdata.(connections)).

Definition remove_connection (addr: sockaddr) (sdata: ServerData) : ServerData :=
	let new_connections := filter (fun c => negb (eq_sockaddr c.(client_addr) addr)) sdata.(connections) in
		with_connections new_connections sdata.

Definition update_connection (conn: Connection) (sdata: ServerData) : ServerData :=
	sdata |> remove_connection conn.(client_addr)
				|> add_connection conn.
	
(* Definition eq_ascii (a1 a2 : Ascii.ascii) :=
  match a1, a2 with
  | Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii.Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (Bool.eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.

Fixpoint eq_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString, EmptyString  => true
  | String x1 s1, String x2 s2 => eq_ascii x1 x2 && eq_string s1 s2
  | _, _                       => false
  end. *)

(* 
Fixpoint int_to_string_acc (n: int) (acc: string) : string :=
    if (n =? 0)%sint63 then acc
    else
        let digit := String (Ascii.ascii_of_nat (to_nat (n mod 10)%sint63)) "" in
        int_to_string_acc (n / 10) (digit ++ acc).

Definition int_to_string (n: int) : string :=
    if n =? 0 then "0"%string else int_to_string_acc n "".
     *)