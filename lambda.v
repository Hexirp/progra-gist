Require Import Coq.Init.Prelude.

Axiom undefined : forall a : Type, a.

Inductive fin : nat -> Type :=
| fo : forall n, fin (S n)
| fs : forall n, fin n -> fin (S n)
.

Definition ind_fin :
    forall P : forall n : nat, fin n -> Type,
    (forall n : nat, P (S n) (fo n)) ->
    (forall n : nat, forall xp : fin n, P n xp -> P (S n) (fs n xp)) ->
    forall n : nat, forall x : fin n, P n x.
Proof.
 intros P cfo cfs.
 fix go 2.
 intros n x.
 refine (
  match x as x' in fin n' return P n' x' with
  | fo n' => _
  | fs n' xp => _
  end
 ).
 -
  apply cfo.
 -
  apply cfs.
  apply go.
Defined.

Definition not_fin_0 : fin 0 -> False.
Proof.
 intros x.
 refine (
  match x in fin n' return 0 = n' -> False with | fo N => _ | fs N xp => _ end
  eq_refl
 ).
 -
  apply O_S.
 -
  apply O_S.
Defined.

Definition fin_S : forall P m, fin m -> (forall n, S n = m -> P) -> P.
Proof.
 intros P m [ m' | m' xp ] r; apply r with m'; apply eq_refl.
Defined.

Definition fin_up : forall m, fin m -> fin (S m).
Proof.
 refine (ind_fin _ _ _).
 -
  intros M.
  apply fo.
 -
  intros M xp IH.
  apply fs.
  apply IH.
Defined.

Definition fin_succ_R : forall m, fin m -> fin m -> Prop
    := fun m x y => fs m x = fin_up m y.

Definition fin_succ_R_Wf : forall m, well_founded (fin_succ_R m).
Proof.
 refine (ind_fin _ _ _).
 -
  intros M.
  apply Acc_intro.
  intros y H.
  admit.
 -
  admit.
Admitted.

Inductive lam : nat -> Type :=
| var : forall n, fin n -> lam n
| abs : forall n, lam (S n) -> lam n
| app : forall n, lam n -> lam n -> lam n
.

Definition ind_lam :
    forall P : forall n, lam n -> Type,
    (forall n : nat, forall v : fin n, P n (var n v)) ->
    (forall n : nat, forall x : lam (S n), P (S n) x -> P n (abs n x)) ->
    (forall n : nat, forall a : lam n, forall b : lam n, P n a -> P n b -> P n (app n a b)) ->
    forall n : nat, forall x : lam n, P n x.
Proof.
 intros P cvar cabs capp.
 fix go 2.
 intros n x.
 refine (
  match x as x' in lam n' return P n' x' with
  | var n' v => _
  | abs n' x => _
  | app n' a b => _
  end
 ).
 -
  apply cvar.
 -
  apply cabs.
  apply go.
 -
  apply capp.
  +
   apply go.
  +
   apply go.
Defined.

Definition plus_1_mn : forall m n, S (m + n) = m + (S n).
Proof.
 refine (nat_ind _ _ _).
 -
  intros n.
  apply eq_refl.
 -
  intros mp IH n.
  cbv.
  fold plus.
  case IH with n.
  apply eq_refl.
Defined.

(**
    f 4 3<4 3<4 y = y
    f 4 2<4 2<4 y = y
    f 4 1<4 1<4 y = y
    f 4 0<4 0<4 y = y

    f 4 3<4 2<4 y = var 3 2<3
    f 4 3<4 1<4 y = var 3 1<3
    f 4 3<4 0<4 y = var 3 0<3
    f 4 2<4 1<4 y = var 3 1<3
    f 4 2<4 0<4 y = var 3 0<3
    f 4 1<4 0<4 y = var 3 0<3

    f 4 2<4 3<4 y = var 3 2<3
    f 4 1<4 2<4 y = var 3 1<3
    f 4 1<4 3<4 y = var 3 2<3
    f 4 0<4 1<4 y = var 3 0<3
    f 4 0<4 2<4 y = var 3 1<3
    f 4 0<4 3<4 y = var 3 2<3

    これらを、 [f m a<m b<m y] の [a] と [b] を同時に減らしていくことで定義する。
    考えるのは [a] が [0] 、または [b] が [0] の時、どうするか。

    f 4 3<4 3<4 y = f 4 2<4 2<4 y = f 4 1<4 1<4 y = f 4 0<4 0<4 y = y
*)
Definition loose_gen_beta_red_var_by_comp
    : forall n, fin n -> fin n -> forall np, S np = n -> option (fin np).
Proof.
 refine (ind_fin _ _ _).
 -
  intros ni y np pnp.
  refine (
   match y in fin n' return n' = S ni -> option (fin np) with | fo n' => _ | fs n' yp => _ end
   eq_refl
  ).
  +
   intros pn'.
   apply None.
  +
   intros pn'.
   apply Some.
   revert yp pn'.
   case (eq_add_S np ni pnp).
   intros yp pn'.
   case (eq_add_S n' np pn').
   apply yp.
 -
  intros ni xp IH y np pnp.
  refine (
   match y in fin n' return n' = S ni -> option (fin np) with | fo n' => _ | fs n' yp => _ end
   eq_refl
  ).
  +
   intros pn'.
   apply Some.
   apply fin_S with np.
   *
    revert xp.
    case (eq_add_S np ni pnp).
    intros xp.
    apply xp.
   *
    intros npp pnpp.
    case pnpp.
    apply fo.
  +
   intros pn'.
   assert (yp' : fin ni).
   *
    case (eq_add_S n' ni pn').
    apply yp.
   *
    apply fin_S with ni.
    --
     apply yp'.
    --
     intros nip pnip.
     assert (IH' := IH yp' nip pnip).
     case IH'.
     ++
      intros IH_S.
      apply Some.
      revert pnip.
      case (eq_add_S np ni pnp).
      intros pnip.
      case pnip.
      apply fs.
      apply IH_S.
     ++
      apply None.
Defined.

Definition loose_gen_beta_red_var_by_ind
    : forall N, fin N -> forall m n, m + S n = N -> lam (m + n) -> lam (m + n).
Proof.
 refine (ind_fin _ _ _).
 -
  intros N m n p y.
  destruct n as [ | np ].
  +
   apply y.
  +
   apply var.
   case plus_1_mn with m np.
   apply fo.
 -
  intros N vp H m n p y.
  destruct n as [ | np ].
  +
   destruct m as [ | mp ].
   *
    exfalso.
    revert vp.
    case (eq_add_S 0 N p).
    apply not_fin_0.
   *
    apply var.
    cbv.
    fold plus.
    case (eq_sym (plus_1_mn mp 0)).
    case (eq_sym (eq_add_S (mp + 1) N p)).
    apply vp.
  +
   case (plus_1_mn m np).
   case (H m np).
   

Definition loose_gen_beta_red_by_ind
    : forall N, lam N -> forall m n, m + S n = N -> lam (m + n) -> lam (m + n).
Proof.
 refine (ind_lam _ _ _ _).
 -
  intros N v m n H y.
 -
  admit.
 -
  admit.
Admitted.

Definition betav0 : forall n, fin n -> ter n -> ter 0.
Proof.
 refine (
  fix go n x y {struct x} := _
 ).
 refine (
  match x in fin n' return n' = n -> ter 0 with
  | fo nx => fun xH => _
  | fs nx xp => fun xH => _
  end eq_refl
 ).
 -
Admitted.

Definition betav : forall m n, fin (m + n) -> ter (m + n) -> ter m.
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
Admitted.

Definition betab : forall m n, ter (m + n) -> ter (S (m + n)).
Proof.
Admitted.

Definition beta3 : forall m n, ter (S m + n) -> ter (m + n) -> ter m.
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
   go m (S n) (_ xp) (_ y)
  ).
  +
   refine (
    fun x' => _ (eq_rect (S nx) ter x' (S (S m + n)) (eq_S nx (S m + n) xH))
   ).
   refine (
    fun x' => eq_rect (S (S m + n)) ter x' (S m + S n) (plus_n_Sm (S m) n)
   ).
  +
   refine (
    fun x' => eq_rect (S (m + n)) ter (betab m n x') (m + S n) (plus_n_Sm m n)
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
  (fun f : forall m, ter m -> ter (m + 0) => (fun m x y => beta3 m 0 (f (S m) x) (f m y))) _
 ).
 refine (
  fun m' x' => eq_rect m' ter x' (m' + 0) (plus_n_O m')
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
