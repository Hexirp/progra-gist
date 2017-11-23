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

(**
(\ v2) foo
\ (v1 foo)+
\ (replace 0 foo)+
\ foo+

nはxに左右される。
*)
Definition replace n (x : fin n) (y : ter n) : ter n :=
 match x in (fin xn) return ter xn -> ter xn with
 | Fino _ => fun i => i
 | Fins _ xp => fun _ => Var _ xp
 end y
.

Print replace.

(** fは裸の関数。イメージしづらいけど\x -> foo xをfoo xに変えたようなもの。 *)
Fixpoint beta n (f : ter (S n)) (x : ter n) : ter n :=
 match f with
 | Var _ var => undefined (ter n)
 | Abs _ abs => undefined (ter n)
 | App _ lef rig => undefined (ter n)
 end
.