Require Import Uint63.
Require Import String.
Require Import Ascii.

Inductive Result (a b : Type) :=
  | Ok (v: a)
  | Error (e: b).

Arguments Ok {a b}.
Arguments Error {a b}.

Definition ErrorMsg : Set := option string.

Parameter file_descr : Set.
Parameter sockaddr : Set.
Parameter print_string : string -> unit.

Record Packet : Set :=
  mkPacket
    {
      data: string ;
      (* len: int ; *)
      addr: sockaddr ;
    }.

Record ServerData : Set :=
  mkServerData
    {
      port: int ;
      socket: file_descr ;
    }.

Inductive ServerState : Set :=
  | NotStarted
  | Running (data: ServerData)
  | Stopped.

Inductive ServerEvent : Set :=
  | Init (port: int) (socket: file_descr)
  | Received (data: Packet).


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
      type: PacketType ;
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
    }.

End Protocol.