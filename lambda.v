Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fo : forall n, fin n
| fs : forall n, fin n -> fin (S n)
.

Inductive ter : nat -> Type :=
| var : forall n, fin n -> ter (S n)
| abs : forall n, ter (S n) -> ter n
| app : forall n, ter n -> ter n -> ter n
.

Definition betav0 : forall n, fin n -> ter 0 -> ter 0.
Proof.
Admitted.

Definition betav : forall m n, fin (m + n) -> ter m -> ter m.
Proof.
 refine (
  fix go m n x y {struct x} := _
 ).
 refine (
  match m as m' return m' = m -> ter m with
  | O => fun mH => _
  | S mp => fun mH => _
  end eq_refl
 ).
 -
  refine (
   eq_rect 0 ter (betav0 n _ (eq_rect_r ter y mH)) m mH
  ).
  refine (
   eq_rect_r (fun m' => fin (m' + n)) x mH
  ).
Admitted.

Definition beta3 : forall m n, ter (S m + n) -> ter m -> ter m.
Proof.
 refine (
  fix go m n x y {struct x} := _
 ).
 refine (
  match x in ter nx' return nx' = S m + n -> ter m with
  | var nx xa => fun xH => _
  | abs nx xp => fun xH => _
  | app nx xl xr => fun xH => _
  end eq_refl
 ).
 -
  refine (
   betav m n _ y
  ).
  refine (
   eq_rect nx fin xa (m + n) (eq_add_S nx (m + n) xH)
  ).
 -
  refine (
   go m (S n) (_ xp) y
  ).
  refine (
   fun x' => _ (eq_rect (S nx) ter x' (S (S m + n)) (eq_S nx (S m + n) xH))
  ).
  refine (
   fun x' => eq_rect (S (S m + n)) ter x' (S m + S n) (plus_n_Sm (S m) n)
  ).
 -
  refine (
   (fun f => app m (go m n (f xl) y) (go m n (f xr) y)) _
  ).
  refine (
   fun x => eq_rect nx ter x (S m + n) xH
  ).
Defined.

Definition beta2 : forall m, ter (S m) -> ter m -> ter m.
Proof.
 refine (
  (fun m x y => beta3 m 0 (_ x) y)
 ).
 refine (
  fun x' => eq_rect (S m) ter x' (S m + 0) (plus_n_O (S m))
 ).
Defined.

Definition beta1 : forall m, ter m -> ter m -> ter m.
Proof.
 refine (
  fun m x y => _
 ).
 refine (
  match x in ter m' return m' = m -> ter m with
  | var nx xa => fun xH => _
  | abs nx xp => fun xH => _
  | app nx xl xr => fun xH => _
  end eq_refl
 ).
 -
  refine (
   app m x y
  ).
 -
  refine (
   beta2 m (eq_rect (S nx) ter xp (S m) (eq_S nx m xH)) y
  ).
 -
  refine (
   app m x y
  ).
Defined.

Definition beta0 : ter 0 -> ter 0 -> ter 0.
Proof.
 refine (
  beta1 0
 ).
Defined.

(** \f \x x *)
Definition ter_0 : ter 0 := abs 0 (abs 1 (var 1 (fo 1))).

(** \f \x f x *)
Definition ter_1 : ter 0 := abs 0 (abs 1 (app 2 (var 1 (fs 0 (fo 0))) (var 1 (fo 1)))).

(** \f \x f (f x) *)
Definition ter_2 : ter 0 :=
 abs 0 (abs 1 (app 2
  (var 1 (fs 0 (fo 0)))
  (app 2
   (var 1 (fs 0 (fo 0)))
   (var 1 (fo 1)))
 ))
.

(** \m \f \x f (m f x) *)
Definition ter_s : ter 0 :=
 abs 0 (abs 1 (abs 2 (app 3
  (var 2 (fs 1 (fo 1)))
  (app 3
   (app 3
    (var 2 (fs 1 (fs 0 (fo 0))))
    (var 2 (fs 1 (fo 1))))
   (var 2 (fo 2)))
 )))
.

Eval cbv in beta0 ter_s ter_0.
