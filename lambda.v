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

0n B0 xn
xn

1n B0 xn
v2n

0n B1 xn
v1n

1n B1 xn
xn

*)
Definition beta_var : forall n, fin n -> fin n -> ter n -> ter n.
Proof.
 fix go 3.
 intros n h f x.
 inversion f.
 - (* f = 0 *)
  inversion h.
  + (* h = 0 *)
   apply x.
  + (* h = n *)
   apply Var.
   apply H0.
 - (* f = n *)
  inversion h.
  + (* h = 0 *)
   apply Var.
   apply H.
  + (* h = n *)
   apply go.
   
   *
    rewrite H0.
    rewrite <- H2.
    apply Fins.
    apply H1.
   *
    

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

1. 外側で定義されている変数の数
2. 置き換えるべき変数
3. 適用する項
4. 適用される項

*)
Definition beta : forall n, fin n -> ter (S n) -> ter n -> ter n.
Proof.
 fix go 3.
 intros n h f x.
 inversion f as [fn fv fnH | fn fv fnH | fn fvl fvr fnH].
 -
  apply (undefined (forall n, fin n -> fin n -> ter n -> ter n) _ h fv x).
 -
  apply (undefined _).
 -
  apply (undefined _).
Qed.
