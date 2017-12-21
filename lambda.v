Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fino : forall n, fin n
| fins : forall n, fin n -> fin (S n)
.

Inductive ter : nat -> Type :=
| var : forall n, fin n -> ter (S n)
| abs : forall n, ter (S n) -> ter n
| app : forall n, ter n -> ter n -> ter n
.

Inductive le (m : nat) : nat -> Type :=
| leo : le m m
| les : forall n, le m n -> le m (S n)
.

Definition les_l m n (x : le (S m) n) : le m n.
Proof.
 induction x as [ | xn xp].
 -
  apply les.
  apply leo.
 -
  apply les.
  apply IHxp.
Defined.

Definition fin_le m n (H : le m n) (x : fin m) : fin n.
Proof.
 induction H as [ | xn xp].
 -
  apply x.
 -
  apply fins.
  apply IHxp.
Defined.

Definition var_le_S m n (H : le m n) (x : fin m) : ter (S n).
Proof.
 apply var.
 apply (fin_le _ _ H x).
Defined.

Definition var_le m n (H : le (S m) n) (x : fin m) : ter n.
Proof.
 inversion H as [HH | Hn Hp HH]; clear H.
 -
  apply var.
  apply x.
 -
  apply var_le_S with (S m).
  +
   refine Hp.
  +
   apply fins.
   refine x.
Defined.

(**

(h = 0, f = 0)
---|
---|

  #

(h = 0, f = x)
---|===
------|

---|==

(h = x, f = 0)
-----|
---|==

----|

(h = x, f = x)
----|==
--|====

----|=
--|===

----|
--|==

---| ==

1. 外側で定義されている変数の数
2. 置き換えるべき変数
3. 対象の変数
4. 置き換える項

*)
Definition beta_var_le m n (H : le m n) (h : fin m) (f : fin m) (x : ter n) : ter n.
Proof.
 induction f as [ fn | fn fp ].
 - (* f = 0 *)
  inversion h as [hm hH | hm hp hH]; clear h.
  + (* h = 0 *)
   apply x.
  + (* h = n *)
   apply var_le with hm.
   *
    rewrite -> hH.
    apply H.
   *
    apply hp.
 - (* f = n *)
  inversion h as [hm hH | hm hp hH]; clear h.
  + (* h = 0 *)
   apply var_le with fn.
   *
    apply H.
   *
    apply fino.
  + (* h = n *)
   apply IHfp.
   *
    apply les_l.
    apply H.
   *
    apply hp.
Defined.

Print beta_var_le.

Definition beta_var n (h : fin n) (f : fin n) (x : ter n) : ter n
 := beta_var_le _ _ (leo _) h f x.

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
Definition beta n (h : fin n) (f : ter (S n)) (x : ter n) : ter n.
Proof.
 induction f as [ fn fv | fn fv | fn fvl fvr ].
 -
  apply beta_var.
  +
   apply h.
  +
   admittd.
 -
  refine (abs _ _).
  refine (beta _ _ _ _).
  +
   refine (fins _ _).
   refine h.
  +
   refine fv.
  +
   refine (undefined (forall n, ter n -> ter (S n)) _ _).
   refine x.
 -
  apply (undefined _).
Qed.

Print beta.
