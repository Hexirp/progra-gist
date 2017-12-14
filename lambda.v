Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fino : forall n, fin n
| fins : forall n, fin n -> fin (S n)
.

Derive Inversion fin_inv with (forall n, fin n) Sort Type.

Print fin_inv.

Section fin_inversion.
 Variable n : nat.
 Variable P : forall n, fin n -> Type.
 Variable Case_fino : fin n -> forall xn, xn = n -> P xn (fino xn).
 Variable Case_fins : fin n -> forall xn, forall xp : fin xn, S xn = n -> P (S xn) (fins xn xp).

 Definition fin_inv : 

Inductive ter : nat -> Type :=
| var : forall n, fin n -> ter (S n)
| abs : forall n, ter (S n) -> ter n
| app : forall n, ter n -> ter n -> ter n
.

Inductive le (m : nat) : nat -> Type :=
| leo : le m m
| les : forall n, le m n -> le m (S n)
.

Fixpoint les_l m n (x : le (S m) n) : le m n.
Proof.
 inversion x as [HH | Hn Hp HH]; clear x.
 -
  refine (les _ _ _).
  refine (leo _).
 -
  refine (les _ _ _).
  refine (les_l _ _ _).
  refine Hp.
Defined.

Fixpoint fin_le m n (H : le m n) (x : fin m) : fin n.
Proof.
 inversion H as [HH | Hn Hp HH]; clear H.
 -
  rewrite <- HH.
  refine x.
 -
  refine (fins _ _).
  refine (fin_le _ _ _ _).
  +
   refine Hp.
  +
   refine x.
Defined.

Definition var_le_S m n (H : le m n) (x : fin m) : ter (S n).
Proof.
 refine (var _ _).
 refine (fin_le _ _ H x).
Defined.

Definition var_le m n (H : le (S m) n) (x : fin m) : ter n.
Proof.
 inversion H as [HH | Hn Hp HH]; clear H.
 -
  refine (var _ _).
  refine x.
 -
  refine (var_le_S _ _ _ _).
  +
   refine Hp.
  +
   refine (fins _ _).
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
Fixpoint beta_var_le m n (H : le m n) (h : fin m) (f : fin m) (x : ter n) : ter n.
Proof.
 inversion h as [hm hH | hm hp hH]; clear h.
 - (* h = 0 *)
  inversion f as [fm fH | fm fp fH]; clear f.
  + (* f = 0 *)
   refine x.
  + (* f = n *)
   refine (var_le fm _ _ _).
   *
    rewrite -> fH.
    refine H.
   *
    refine fp.
 - (* h = n *)
  inversion f as [fm fH | fm fp fH]; clear f.
  + (* f = 0 *)
   refine (var_le hm _ _ _).
   *
    rewrite -> hH.
    refine H.
   *
    refine (fino _).
  + (* f = n *)
   refine (beta_var_le fm n _ _ _ _).
   *
    inversion H as [HH | Hn Hp HH]; clear H.
    --
     rewrite <- HH.
     rewrite <- fH.
     refine (les _ _ _).
     refine (leo _).
    --
     refine (les _ _ _).
     refine (les_l _ _ _).
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
Defined.

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
Fixpoint beta n (h : fin n) (f : ter (S n)) (x : ter n) : ter n.
Proof.
 inversion f as [fn fv fnH | fn fv fnH | fn fvl fvr fnH].
 -
  refine (beta_var _ h fv x).
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
