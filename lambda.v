Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fo : forall n, fin n
| fs : forall n, fin n -> fin (S n)
.

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