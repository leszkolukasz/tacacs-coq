Require Import List.
Require Import String.
Require Import Definitions.

Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.

Definition database : list User := [
  {| u_username := "user1" ; u_password := "pass1" ; superuser := true|} ;
  {| u_username := "user2" ; u_password := "pass2" ; superuser := false|}
].

Definition find_user (username: string) : option User :=
  find (fun (user: User) => String.eqb user.(u_username) username) database.