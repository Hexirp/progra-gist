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

Inductive le (m : nat) : nat -> Type :=
| Leo : le m m
| Les : forall n, le m n -> le m (S n)
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
Fixpoint beta_var m n (H : le m n) (h : fin m) (f : fin m) (x : ter n) : ter n.
Proof.
 refine (
  match h in fin hm' return m = hm' -> ter n with
  | Fino hm => _
  | Fins hm hp => _
  end (eq_refl m)
 ); clear h.
 - (* h = 0 *)
  refine (
   match f in fin fm' return m = fm' -> fm' = hm -> ter n with
   | Fino fm => _
   | Fins fm fp => _
   end (eq_refl m)
  ); clear f.
  + (* f = 0 *)
   intros fH hH.
   apply x.
  + (* f = n *)
   intros fH hH.
   refine (
    undefined (forall m n, le (S m) n -> fin m -> ter n) fm _ _ _
   ).
   *
    refine (
     match fH in _ = m' return le m' n with
     | eq_refl _ => _
     end
    ); clear fH.
    apply H.
   *
   refine fp.
 - (* h = n *)
  refine (
   match f in fin fm' return m = fm' -> fm' = S hm -> ter n with
   | Fino fm => _
   | Fins fm fp => _
   end (eq_refl m)
  ); clear f.
  + (* f = 0 *)
   intros fH hH.
   refine (
    undefined (forall m n, le (S m) n -> fin m -> ter n) hm _ _ _
   ).
   *
    refine (
     match hH in _ = fm' return le fm' n with
     | eq_refl _ => _
     end
    ); clear hH.
    refine (
     match fH in _ = m' return le m' n with
     | eq_refl _ => _
     end
    ).
    refine H.
   *
    refine (Fino _).
  + (* f = n *)
   intros fH hH.
   refine (beta_var fm n _ _ _ _).
   *
    refine (
     match H in le _ n' return le fm n' with
     | Leo _ => _
     | Les _ Hn Hp => _
     end
    ).
    --
     refine

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
