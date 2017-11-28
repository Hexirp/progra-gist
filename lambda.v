Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
 | Fino : forall n, fin n
 | Fins : forall n, fin n -> fin (S n)
.

Inductive ter : nat -> Type :=
 | Var : forall n, fin n -> ter (S n)
 | Abs : forall n, ter (S n) -> ter n
 | App : forall n, ter n -> ter n -> ter n
.

Definition fin_destruct n p (x : fin n) (co : p n) (cs : forall xn, fin xn -> p (S xn)) : p n.
Proof.
 destruct x.
 -
  apply co.
 -
  apply cs.
  apply x.
Qed.

(** fは裸の関数。イメージしづらいけど\x -> foo xをfoo xに変えたようなもの。

(\ 1 1) (\ 1 1)
(1 1) B0 (\ 1 1)
(1 B0 (\ 1 1)) (1 B0 (\ 1 1))
(\ 1 1) (\ 1 1)

\ (\ \ \ 1 2 3) 1
\ (\ \ 1 2 3) B0 1
\ \ (\ 1 2 3) B1 2
\ \ \ (1 2 3) B2 3
\ \ \ 1 2 3

\ (\ \ 2 1) 1
\ (\ 2 1) B0 1
\ \ (2 1) B1 2
\ \ 2 1

*)
Definition beta n (f : ter (S n)) (x : ter n) : ter n.
Proof.
 inversion f.
 -
  apply replace.
  +
   apply H0.
  +
   apply x.
 -
  apply beta_rec.
  +
   apply H.
  +
   apply x.
 -
  apply (undefined (ter n)).
Qed.
