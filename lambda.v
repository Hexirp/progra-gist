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

Definition cut_fix : forall P, (forall n, nats n -> P n) -> forall n, P n.
Proof.
 refine (
  fun P H => _
 ).
 admit.

Definition fin_nat : forall n, nats n -> fin n.
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

(*
fin_nat O = fo O
fin_nat (S O) = fs O (fo O)
fin_nat (S (S O)) = fs (S O) (fs O (fo O))
*)
Definition fin_nat (m : nat) : fin m.
Proof.
 induction m.
 -
  apply fo.
 -
  apply fs.
  apply IHm.
Defined.

(*
fin_ O O = fo O
fin_ (S O) O = fo (S O)
fin_ (S (S O)) O = fo (S (S O))
fin_ O (S O) = fs O (fo O)
fin_ O (S (S O)) = fs (S O) (fs O (fo O))
fin_ (S O) (S O) = fs (S O) (fo (S O))
*)
Fixpoint fin_ (m n : nat) : fin (m + n).
admit.

Inductive ter : nat -> Type :=
| var : forall n, fin n -> ter (S n)
| abs : forall n, ter (S n) -> ter n
| app : forall n, ter n -> ter n -> ter n
.

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