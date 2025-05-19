Require Import Uint63.
Require Import String.
Require Import Nat.

Require Import CoqServer.

Record ServerData : Set :=
  mkServerData
    {
      port: int ;
    }.


Inductive ServerState : Set :=
  | NotStarted
  | Running (data: ServerData)
  | Stopped
  | Error (msg: string).