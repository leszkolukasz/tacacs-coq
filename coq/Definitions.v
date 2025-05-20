Require Import Uint63.
Require Import String.

Inductive Result (a b : Type) :=
  | Ok (v: a)
  | Error (e: b).

Arguments Ok {a b}.
Arguments Error {a b}.

Definition ErrorMsg : Set := option string.

Parameter file_descr : Set.
Parameter sockaddr : Set.

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