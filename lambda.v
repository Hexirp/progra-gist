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

Inductive nat_max : nat -> nat -> Type :=
| NMe : nat_max 0 0
| NMl : forall n, nat_max (S n) 0
| NMr : forall n, nat_max 0 (S n)
| NMs : forall m n, nat_max m n -> nat_max (S m) (S n)
.

Fixpoint max m n : nat_max m n.
Proof.
 destruct m as [ | m]; destruct n as [ | n].
 -
  refine NMe.
 -
  refine (NMr _).
 -
  refine (NMl _).
 -
  refine (NMs _ _ _).
  refine (max _ _).
Defined.

Inductive fin_max : forall n, fin n -> fin n -> Type :=
| FMe : forall n, fin_max n (Fino n) (Fino n)
| FMl : forall n (fi : fin n), fin_max (S n) (Fins n fi) (Fino (S n))
| FMr : forall n (fi : fin n), fin_max (S n) (Fino (S n)) (Fins n fi)
| FMs : forall n (fi : fin n), fin_max n fi fi -> fin_max (S n) (Fins n fi) (Fins n fi)
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

----|====
---|=====

---*|====
 ---|====

----|====
-----|===

----|*===
 ----|===

----|====
----|====

----*====
        #

----|====
---|=====

----|===
---|====

----|==
---|===

----|=
---|==

----|
---|=

---|====

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
Fixpoint beta_var n (h : fin n) (f : fin n) (x : ter n) : ter n.
Proof.
 refine (
  match h in fin hn' return n = hn' -> ter hn' with
  | Fino hn => _
  | Fins hn hp => _
  end (eq_refl n)
 ); clear h.
 - (* h = 0 *)
  refine (
   match f in fin fn' return n = fn' -> fn' = hn -> ter hn with
   | Fino fn => _
   | Fins fn fp => _
   end (eq_refl n)
  ); clear f.
  + (* f = 0 *)
   intros fH hH.
   refine (
    match hH in _ = hn' return ter hn' with
    | eq_refl _ => _
    end
   ); clear hH hn.
   refine (
    match fH in _ = fn' return ter fn' with
    | eq_refl _ => _
    end
   ); clear fH fn.
   apply x.
  + (* f = n *)
   intros fH hH.
   refine (
    match hH in _ = hn' return ter hn' with
    | eq_refl _ => _
    end
   ); clear hH hn.
   refine (Var _ _).
   refine fp.
 - (* h = n *)
  refine (
   match f in fin fn' return n = fn' -> fn' = S hn -> ter (S hn) with
   | Fino fn => _
   | Fins fn fp => _
   end (eq_refl n)
  ); clear f.
  + (* f = 0 *)
   intros fH hH.
   refine (Var _ _).
   refine (Fino _).
  + (* f = n *)
   intros fH hH.
   
 -
  intro fH.
  refine (
   match fH in @eq _ _ n' return ter n' with
   | @eq_refl _ _ => _
   end
  ); clear fH fn.
  apply (undefined _).
 -
  apply (undefined _).
 Show Proof.
    

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
