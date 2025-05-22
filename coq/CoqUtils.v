Require Import String.
Require Import Uint63.
Require Import Sint63.
Require Import ZArith.


Open Scope string_scope.

Definition newline : string :=
    String (Ascii.ascii_of_nat 10) "".
(* 
Fixpoint int_to_string_acc (n: int) (acc: string) : string :=
    if (n =? 0)%sint63 then acc
    else
        let digit := String (Ascii.ascii_of_nat (to_nat (n mod 10)%sint63)) "" in
        int_to_string_acc (n / 10) (digit ++ acc).

Definition int_to_string (n: int) : string :=
    if n =? 0 then "0"%string else int_to_string_acc n "".
     *)