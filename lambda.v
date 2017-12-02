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

(h = 0, f = 0)
---|
---|

   #

(h = 0, f = n)
---|===
------|

---|==

(h = n, f = 0)
-----|
---|==

----|

1. 外側で定義されている変数の数
2. 置き換えるべき変数
3. 対象の変数
4. 置き換える項

*)
Fixpoint beta_var m n (H : m <= n) (h : fin m) (f : fin m) (x : ter n) : ter n.
Proof.
 inversion h as [hm hH | hm hp hH]; clear h.
 - (* h = 0 *)
  inversion f as [fm fH | fm fp fH]; clear f.
  + (* f = 0 *)
   refine x.
  + (* f = n *)
   refine (
    undefined (forall m n, S m <= n -> fin m -> ter n) fm _ _ _
   ).
   *
    rewrite -> fH.
    refine H.
   *
   refine fp.
 - (* h = n *)
  inversion f as [fm fH | fm fp fH]; clear f.
  + (* f = 0 *)
   refine (
    undefined (forall m n, S m <= n -> fin m -> ter n) hm _ _ _
   ).
   *
    rewrite -> hH.
    refine H.
   *
    refine (Fino _).
  + (* f = n *)
   refine (beta_var fm n _ _ _ _).
   *
    inversion H as [HH | Hn Hp HH]; clear H.
    --
     rewrite <- HH.
     rewrite <- fH.
     refine (le_S _ _ _).
     refine (le_n _).
    --
     refine (le_S _ _ _).
     refine (
      undefined (forall m n, S m <= n -> m <= n) _ _ _
     ).
     rewrite -> fH.
     refine Hp.
   *
    replace fm with hm.
    --
     refine hp.
    --
     refine (eq_add_S _ _ _).
     rewrite -> fH.
     refine hH.
   *
    refine fp.
   *
    refine x.
Qed.

Print beta_var.

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
