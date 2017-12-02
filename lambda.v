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
| NMs : forall n, nat_max n n -> nat_max (S n) (S n)
.

Definition max m0 n0 (st0 : nat_max m0 n0) : nat.
Proof.
 refine (
  (fix go m n (st : nat_max m n) {struct st} := _) m0 n0 st0
 );
 clear st0 n0 m0.
 generalize (eq_refl m) (eq_refl n).
 refine (
  match st in nat_max stm0 stn0 return m = stm0 -> n = stn0 -> nat with
  | NMe => _
  | NMl stl => _
  | NMr str => _
  | NMs sts st' => _
  end
 );
 clear st;
 intros _ _.
 -
  apply 0.
 -
  apply (S stl).
 -
  apply (S str).
 -
  apply (go sts sts st').
Defined.

Print max.

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

 ---|====
 --|=====

  --|====
  -|=====

   -|====
   |=====

    |====

*)
Definition beta_var n0 (h0 : fin n0) (f0 : fin n0) (x0 : ter n0) : ter n0.
Proof.
 refine (
  (fix go n (h : fin n) (f : fin n) (x : ter n) {struct n} := _) n0 h0 f0 x0
 ); clear x0 f0 h0 n0.
 refine (
  _ (eq_refl n)
 ).
 refine (
  match f in fin fn0 return n = fn0 -> ter fn0 with
  | Fino fn => _
  | Fins fn fp => _
  end
 ).
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
