Require Import Uint63.
Require Import String.
Require Import Ascii.
Require Import List.

Import ListNotations.
Open Scope list_scope.

Inductive Result (a b : Type) :=
  | Ok (v: a)
  | Error (e: b).

Arguments Ok {a b}.
Arguments Error {a b}.

Definition ErrorMsg : Set := option string.

Definition Ret (a : Type) := Result a ErrorMsg.

Parameter file_descr : Set.
Parameter sockaddr : Set.
Parameter println : string -> bool.
Parameter int_to_string : int -> string.
Parameter eq_sockaddr : sockaddr -> sockaddr -> bool.

Module Protocol.

Inductive VersionType : Set :=
  | Simple
  | Extended.

Inductive PacketType : Set :=
  | PacketLogin
  | PacketResponse
  | PacketChange
  | PacketFollow
  | PacketConnect
  | PacketSuperuser
  | PacketLogout
  | PacketReload
  | PacketSlipOn
  | PacketSlipOff
  | PacketSlipAddr.

Inductive ResponseType: Set :=
  | ResponseNone
  | ResponseAccepted
  | ResponseRejected.

Inductive ReasonType : Set :=
  | ReasonNone
  | ReasonExpiring
  | ReasonPassword
  | ReasonDenied
  | ReasonQuit
  | ReasonIdle
  | ReasonDrop
  | ReasonBad.

Definition IPAddress : Set := ascii * ascii * ascii * ascii.

Record ParsedPacket: Set :=
  mkParsedPacket
    {
      version: VersionType ;
      kind: PacketType ;
      nonce: int ;
      user_len: int ;
      password_len: int ;
      response: ResponseType ;
      reason: ReasonType ;
      result1: string ;
      destination_addr: IPAddress ;
      destination_port: int ;
      line: int ;
      result2: string ;
      result3: string ;
      p_username: string ;
      p_password: string ;
    }.

End Protocol.

Record User : Set :=
  mkUser
    {
      u_username: string ;
      u_password: string ;
      superuser: bool ;
    }.

Record Packet : Set :=
  mkPacket
    {
      data: string ;
      (* len: int ; *)
      addr: sockaddr ;
    }.

Inductive ConnectionMode : Set :=
  | Normal
  | Slip (logout : bool).

Record Connection : Set :=
  mkConnection
    {
      client_addr: sockaddr ;
      mode: ConnectionMode ;
      slip_addr: option Protocol.IPAddress ;
    }.

Record ServerData : Set :=
  mkServerData
    {
      port: int ;
      socket: file_descr ;
      connections: list Connection ;
    }.

Inductive ServerState : Set :=
  | NotStarted
  | Running (data: ServerData)
  | Stopped.

Inductive ServerEvent : Set :=
  | Init (port: int) (socket: file_descr)
  | Received (data: Packet).
