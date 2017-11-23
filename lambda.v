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

(**
(\ v2) foo
\ (v1 foo)+
\ (replace 0 foo)+
\ foo+

nはxに左右される。
*)
Definition replace n (x : fin n) (y : ter n) : ter n := fin_destruct _ _ x y Var.

Definition beta_rec n (x : ter (S (S n))) (y : ter n) : ter n := undefined (ter n).

(** fは裸の関数。イメージしづらいけど\x -> foo xをfoo xに変えたようなもの。 *)
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

Print beta.