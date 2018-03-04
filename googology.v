(* coqtop -nois *)

Set Printing Universes.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition to : Type := nat.

Definition ts : Type -> Type := fun t => nat -> t.

Definition t : Type := to.

Definition t0 : Type := ts t.

Definition o : nat := O.

Definition s : nat -> nat := S.

Definition f : nat := o.

Definition f0 : nat := s f.

Definition f00 : nat := s f0.

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

Definition o0 : nat -> nat := ind nat o s.

Definition s0 : (nat -> nat) -> (nat -> nat) := comp nat nat nat S.

Definition f01 : nat -> nat := o0.

Definition f010 : nat -> nat := s0 f01.

Definition f0100 : nat -> nat := s0 f010.

Definition o00 : nat -> nat -> nat := ind (nat -> nat) o0 s0.

Definition s00 : (nat -> nat -> nat) -> (nat -> nat -> nat) :=
 comp nat (nat -> nat) (nat -> nat) s0
.

Definition f0101 : nat -> nat -> nat := o00.

Definition f01010 : nat -> nat -> nat := s00 f0101.

Definition f010100 : nat -> nat -> nat := s00 f01010.

Definition o000 : nat -> nat -> nat -> nat := ind (nat -> nat -> nat) o00 s00.

Definition s000 : (nat -> nat -> nat -> nat) -> (nat -> nat -> nat -> nat) :=
 comp nat (nat -> nat -> nat) (nat -> nat -> nat) s00
.

Definition f010101 : nat -> nat -> nat -> nat := o000.

Definition f0101010 : nat -> nat -> nat -> nat := s000 f010101.

Definition f01010100 : nat -> nat -> nat -> nat := s000 f0101010.
