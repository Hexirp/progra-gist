Set Printing Universes.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Definition ind : forall (P : Type), P -> (P -> P) -> nat -> P :=
 fun (P : Type) (cO : P) (cS : P -> P) =>
  fix go (x : nat) : P :=
   match x return P with
   | O => cO
   | S xp => cS (go xp)
   end
.

Definition comp : forall (A : Type), (A -> A) -> (nat -> A) -> nat -> A :=
 fun (A : Type) (f : A -> A) (g : nat -> A) (x : nat) => f (g x)
.

Definition to : Type := nat.

Definition ts : Type -> Type := fun t => nat -> t.

Definition t : Type := to.

Definition o : t := O.

Definition s : t -> t := S.

Definition f : t := o.

Definition f0 : t := s f.

Definition f00 : t := s f0.

Definition t0 : Type := ts t.

Definition o0 : t0 := ind t o s.

Definition s0 : t0 -> t0 := comp t s.

Definition f01 : t0 := o0.

Definition f010 : t0 := s0 f01.

Definition f0100 : t0 := s0 f010.

Definition t00 : Type := ts t0.

Definition o00 : t00 := ind t0 o0 s0.

Definition s00 : t00 -> t00 := comp t0 s0.

Definition f0101 : t00 := o00.

Definition f01010 : t00 := s00 f0101.

Definition f010100 : t00 := s00 f01010.

Definition ts0 : nat -> Type := ind Type to ts.

Definition t01 : Type := forall m, ts0 m.

Definition o01 : t01.
Proof.
 refine (fix o01 m := _).
 refine (match m as m' return ts0 m' with O => _ | S mp => _ end).
 -
  refine o.
 -
  refine (ind (ts0 mp) (o01 mp) _).
  refine ((_ : forall m, ts0 m -> ts0 m) mp).
  refine (fix scheme n := _).
  refine (match n as n' return ts0 n' -> ts0 n' with O => _ | S np => _ end).
  +
   refine s.
  +
   refine (comp (ts0 np) (scheme np)).
Defined.

Definition s01 : t01 -> t01.
Proof.
 refine (fun f m => _).
 refine (_ (f m)).
 refine ((_ : forall n, ts0 n -> ts0 n) m).
 refine (fix scheme n := _).
 refine (match n as n' return ts0 n' -> ts0 n' with O => _ | S np => _ end).
 -
  refine s.
 -
  refine (comp (ts0 np) (scheme np)).
Defined.

Definition f011 : forall (x : nat), t01 x := o01.

Definition f0110 : forall (x : nat), t01 x := s01 f011.

Definition f01100 : forall (x : nat), t01 x := s01 f0110.

Definition t010 : Type := ts (forall m, t01 m).

Definition o010 : t010 :=
 indD t010 s (fun (xp : nat) (go : t010 xp) => ind (t010 xp) go (s010 xp)).

Definition s010 : forall (x : nat), t010 x -> t010 x :=
 fun (x : nat) => comp nat (t01 x) (t01 x) (s01 x).


Definition f01101 : forall (x : nat), t010 x := o010.

Definition f011010 : forall (x : nat), t010 x := compD nat t010 t010 s010 f01101.

Definition f0110100 : forall (x : nat), t010 x := compD nat t010 t010 s010 f011010.

Definition t0100 : nat -> Type := ts0 t010.

Definition s0100 : t0100 -> t0100 := comp nat t010 t010 s010.

Definition o0100 : forall (x : nat), t0100 x := ind t010 o010 s010.

Definition to00 : nat -> Type := ind Type t01 ts.

Definition t0101 : Type := forall (x : nat), to00 x.
