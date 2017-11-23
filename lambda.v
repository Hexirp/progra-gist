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

(** fは裸の関数。イメージしづらいけど\x -> foo xをfoo xに変えたようなもの。 *)
Fixpoint beta n (f : ter (S n)) (x : ter n) : ter n :=
 match f with
 | Var _ var => undefined (ter n)
 | Abs _ abs => undefined (ter n)
 | App _ lef rig => undefined (ter n)
 end
.