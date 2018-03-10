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

Definition s0 : t0 -> t0 := comp nat t t s.

Definition f01 : t0 := o0.

Definition f010 : t0 := s0 f01.

Definition f0100 : t0 := s0 f010.

Definition t00 : Type := ts t0.

Definition o00 : t00 := ind t0 o0 s0.

Definition s00 : t00 -> t00 := comp nat t0 t0 s0.

Definition f0101 : t00 := o00.

Definition f01010 : t00 := s00 f0101.

Definition f010100 : t00 := s00 f01010.

Definition t000 : Type := ts t00.

Definition o000 : t000 := ind t00 o00 s00.

Definition s000 : t000 -> t000 := comp nat t00 t00 s00.

Definition f010101 : t000 := o000.

Definition f0101010 : t000 := s000 f010101.

Definition f01010100 : t000 := s000 f0101010.

Definition indD
 :
  forall (P : nat -> Type), P O -> (forall (x : nat), P x -> P (S x)) -> forall (x : nat), P x
 :=
  nat_rect
.

Definition compD
 :
  forall (A : Type) (B : A -> Type) (C : A -> Type),
   (forall (x : A), B x -> C x) -> (forall (x : A), B x) -> forall x, C x
 :=
  fun
   (A : Type)
   (B : A -> Type)
   (C : A -> Type)
   (f : forall (x : A), B x -> C x)
   (g : forall (x : A), B x)
   (x : A)
  => f x (g x)
.

Definition to0 : nat -> Type := ind Type to ts.

Definition ts0 : nat -> Type := fun (x : nat) => to0 x -> to0 x.

Definition t01 : Type := forall (x : nat), to0 x.

Definition s01D : forall (x : nat), ts0 x :=
 indD
  ts0
  s
  (fun (xp : nat) => comp nat (to0 xp) (to0 xp))
.

Definition s01 : t01 -> t01 := compD nat to0 to0 s01D.

Definition o01 : t01 :=
 indD
  to0
  o
  (fun (xp : nat) (go : to0 xp) => ind (to0 xp) go (s01D xp))
.

Definition f011 : t01 := o01.

Definition f0110 : t01 := s01 f011.

Definition f01100 : t01 := s01 f0110.

Definition t010 : Type := ts t01.

Definition f01101 : t010 := ind t01 o01 s01.

Definition s01101 : t010 -> t010 := comp nat t01 t01 s01.

Definition f011010 : t010 := s01101 f01101.
