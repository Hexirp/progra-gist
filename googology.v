(* coqtop -nois *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition f : nat := O.

Definition f0 : nat := S f.

Definition f00 : nat := S f0.
