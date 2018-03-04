(* coqtop -nois *)

Set Printing Universes.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition to : Type := nat.

Definition ts : Type -> Type := fun t => nat -> t.

Definition t : Type := to.

Definition o : t := O.

Definition s : t -> t := S.

Definition f : t := o.

Definition f0 : t := s f.

Definition f00 : t := s f0.

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

Definition t0 : Type := ts t.

Definition o0 : t0 := ind t o s.

Definition s0 : t0 -> t0 := comp nat t t S.

Definition f01 : t0 := o0.

Definition f010 : t0 := s0 f01.

Definition f0100 : t0 := s0 f010.

Definition t00 : Type := ts t0.

Definition o00 : t00 := ind t0 o0 s0.

Definition s00 : t00 -> t00 := comp nat t0 t0 s0.

Definition f0101 : t00 := o00.

Definition f01010 : t00 := s00 f0101.

Definition f010100 : t00 := s00 f01010.

Definition o000 : nat -> nat -> nat -> nat := ind (nat -> nat -> nat) o00 s00.

Definition s000 : (nat -> nat -> nat -> nat) -> (nat -> nat -> nat -> nat) :=
 comp nat (nat -> nat -> nat) (nat -> nat -> nat) s00
.

Definition f010101 : nat -> nat -> nat -> nat := o000.

Definition f0101010 : nat -> nat -> nat -> nat := s000 f010101.

Definition f01010100 : nat -> nat -> nat -> nat := s000 f0101010.
