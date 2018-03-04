(* coqtop -nois *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition f : nat := O.

Definition f0 : nat := S f.

Definition f00 : nat := S f0.

Definition ind : forall (P : Type), P -> (P -> P) -> nat -> P :=
 fun (P : Type) (cO : P) (cS : P -> P) =>
  fix go (x : nat) : P :=
   match x return P with
   | O => cO
   | S xp => cS (go xp)
   end
.
