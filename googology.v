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

Definition comp : forall (A B C : Type), (B -> C) -> (A -> B) -> A -> C :=
 fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x)
.

Definition f01 : nat -> nat := ind nat O S.

Definition f010 : nat -> nat := comp nat nat nat S f01.

Definition f0100 : nat -> nat := comp nat nat nat S f010.
