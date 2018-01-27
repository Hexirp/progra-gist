Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fo : forall n, fin n
| fs : forall n, fin n -> fin (S n)
.

Inductive nats' (f : nat -> Type) : nat -> Type :=
| no' : nats' f O
| ns' : forall n, f n -> nats' f (S n)
.

Inductive nats : nat -> Type :=
| no : nats O
| ns : forall n, nats n -> nats (S n)
.

Definition fix_nats : forall P, (forall n, nats' P n -> P n) -> forall n, nats n -> P n.
Proof.
 refine (
  fun P H => _
 ).
 refine (
  fix go n x {struct x} := _
 ).
 refine (
  match x in nats n' return P n' with
  | no => _
  | ns np xp => _
  end
 ).
 -
  refine (
   H 0 (no' P)
  ).
 -
  refine (
   H (S np) (ns' P np _)
  ).
  refine (
   go np xp
  ).
Defined.

Definition nats_nat : forall n, nats n.
Proof.
 refine (
  fix go n {struct n} := _
 ).
 refine (
  match n as n' return nats n' with
  | O => no
  | S np => ns np (go np)
  end
 ).
Defined.

Definition cut_nats : forall P, (forall n, nats n -> P n) -> forall n, P n.
Proof.
 refine (
  fun P H n => _
 ).
 refine (
  H n (nats_nat n)
 ).
Defined.

Definition fin_nats_nat : forall n, nats n -> fin n.
Proof.
 refine (
  fix_nats fin _
 ).
 refine (
  fun n x => _
 ).
 refine (
  match x in nats' _ n' return fin n' with
  | no' _ => fo 0
  | ns' _ np xp => _
  end
 ).
 refine (
  fs np xp
 ).
Defined.

Definition fin_nat : forall n, fin n := cut_nats fin fin_nats_nat.

Definition fin_nats_ex : forall m, nats m -> forall n, fin n -> fin (m + n).
Proof.
 refine (
  fix_nats (fun m => forall n, fin n -> fin (m + n)) _
 ).
 refine (
  fun n x => _
 ).
Admitted.

Definition fin_ex : forall m n, fin n -> fin (m + n).
Proof.
Admitted.

(*
fin_ O O = fo O
fin_ (S O) O = fo (S O)
fin_ (S (S O)) O = fo (S (S O))
fin_ O (S O) = fs O (fo O)
fin_ O (S (S O)) = fs (S O) (fs O (fo O))
fin_ (S O) (S O) = fs (S O) (fo (S O))
*)
Fixpoint fin_ (m n : nat) : fin (m + n).
Proof.
Admitted.

Inductive ter : nat -> Type :=
| var : forall n, fin n -> ter (S n)
| abs : forall n, ter (S n) -> ter n
| app : forall n, ter n -> ter n -> ter n
.

Definition betav : forall m n, fin (m + n) -> ter m -> ter m.
Proof.
 refine (
  fix go m n x y {struct x} := _
 ).
 refine (
  match m as m' return m' = m -> ter m with
  | O => fun mH => _
  | S mp => fun mH => _
  end eq_refl
 ).
Admitted.

Definition beta3 : forall m n, ter (S m + n) -> ter m -> ter m.
Proof.
 refine (
  fix go m n x y {struct x} := _
 ).
 refine (
  match x in ter nx' return nx' = S m + n -> ter m with
  | var nx xa => fun xH => _
  | abs nx xp => fun xH => _
  | app nx xl xr => fun xH => _
  end eq_refl
 ).
 -
  refine (
   betav m n _ y
  ).
  refine (
   eq_rect nx fin xa (m + n) (eq_add_S nx (m + n) xH)
  ).
 -
  admit.
 -
  refine (
   (fun f => app m (go m n (f xl) y) (go m n (f xr) y)) _
  ).
  refine (
   fun x => eq_rect nx ter x (S m + n) xH
  ).
Admitted.

Definition beta2 : forall m, ter (S m) -> ter m -> ter m.
Proof.
 refine (
  (fun m x y => beta3 m 0 (_ x) y)
 ).
 refine (
  fun x' => eq_rect (S m) ter x' (S m + 0) (plus_n_O (S m))
 ).
Defined.

Definition beta1 : forall m, ter m -> ter m -> ter m.
Proof.
 refine (
  fun m x y => _
 ).
 refine (
  match x in ter m' return m' = m -> ter m with
  | var nx xa => fun xH => _
  | abs nx xp => fun xH => _
  | app nx xl xr => fun xH => _
  end eq_refl
 ).
 -
  refine (
   app m x y
  ).
 -
  refine (
   beta2 m (eq_rect (S nx) ter xp (S m) (eq_S nx m xH)) y
  ).
 -
  refine (
   app m x y
  ).
Defined.

Definition beta0 : ter 0 -> ter 0 -> ter 0.
Proof.
 refine (
  beta1 0
 ).
Defined.

(** \f \x x *)
Definition ter_0 : ter 0 := abs 0 (abs 1 (var 1 (fo 1))).

(** \f \x f x *)
Definition ter_1 : ter 0 := abs 0 (abs 1 (app 2 (var 1 (fs 0 (fo 0))) (var 1 (fo 1)))).

(** \f \x f (f x) *)
Definition ter_2 : ter 0 :=
 abs 0 (abs 1 (app 2
  (var 1 (fs 0 (fo 0)))
  (app 2
   (var 1 (fs 0 (fo 0)))
   (var 1 (fo 1)))
 ))
.

(** \m \f \x f (m f x) *)
Definition ter_s : ter 0 :=
 abs 0 (abs 1 (abs 2 (app 3
  (var 2 (fs 1 (fo 1)))
  (app 3
   (app 3
    (var 2 (fs 1 (fs 0 (fo 0))))
    (var 2 (fs 1 (fo 1))))
   (var 2 (fo 2)))
 )))
.
