Require Import Coq.Init.Prelude.

(** * Lemmas *)

Lemma plus_1_mn : forall m n, S (m + n) = m + (S n).
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

Lemma plus_comm : forall m n, m + n = n + m.
Proof.
 refine (nat_ind _ _ _).
 -
  intros n.
  apply plus_n_O.
 -
  intros mi IH n.
  cbv.
  fold plus.
  case plus_1_mn.
  case IH.
  apply eq_refl.
Defined.

(** * fin *)

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

Definition fin_ups : forall m n, fin n -> fin (m + n).
Proof.
 intros m.
 induction m as [ | mp IH ].
 -
  intros n x.
  apply x.
 -
  intros n x.
  apply fin_up.
  fold plus.
  apply IH.
  apply x.
Defined.

Definition fin_full : forall m, fin (S m).
Proof.
 intros m.
 induction m as [ | mp IH ].
 -
  apply fo.
 -
  apply fs.
  apply IH.
Defined.

(** * lam *)

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

Definition lam_succ : forall n, lam n -> lam (S n).
Proof.
 refine (ind_lam _ _ _ _).
 -
  intros ni v.
  apply var.
  apply fs.
  apply v.
 -
  intros ni x IH.
  apply abs.
  apply IH.
 -
  intros ni a b IHa IHb.
  apply app.
  +
   apply IHa.
  +
   apply IHb.
Defined.

Definition lam_succs : forall m n, lam n -> lam (m + n).
Proof.
 refine (nat_rect _ _ _).
 -
  intros n x.
  apply x.
 -
  intros mi IH n x.
  apply lam_succ.
  fold plus.
  apply IH.
  apply x.
Defined.

(** * beta *)

Definition loose_gen_beta_var_comp_by_ind
    : forall n, fin n -> fin n -> forall np, S np = n -> option (fin np).
Proof.
 refine (ind_fin _ _ _).
 -
  intros ni y np pnp.
  refine (
   match y in fin n' return n' = S ni -> option (fin np) with
   | fo n' => _
   | fs n' yp => _
   end
   eq_refl
  ).
  +
   intros pn'.
   apply None.
  +
   intros pn'.
   apply Some.
   case (eq_sym (eq_add_S np ni pnp)).
   case (eq_add_S n' ni pn').
   apply yp.
 -
  intros ni xp IH y np pnp.
  refine (
   match y in fin n' return n' = S ni -> option (fin np) with
   | fo n' => _
   | fs n' yp => _
   end
   eq_refl
  ).
  +
   intros pn'.
   apply Some.
   apply fin_S with np.
   *
    case (eq_sym (eq_add_S np ni pnp)).
    apply xp.
   *
    intros npp pnpp.
    case pnpp.
    apply fo.
  +
   intros pn'.
   refine (fin_S _ ni _ _).
   *
    case (eq_add_S n' ni pn').
    apply yp.
   *
    intros nip pnip.
    apply option_map with (fin nip).
    --
     intros IH'.
     case (eq_sym (eq_add_S np ni pnp)).
     case pnip.
     apply fs.
     apply IH'.
    --
     apply IH.
     ++
      case (eq_add_S n' ni pn').
      apply yp.
     ++
      apply pnip.
Defined.

Definition loose_gen_beta_var_comp
    : forall m n, fin (m + S n) -> option (fin (m + n)).
Proof.
 intros m n x.
 apply loose_gen_beta_var_comp_by_ind with (m + S n).
 -
  apply fin_ups.
  apply fin_full.
 -
  apply x.
 -
  apply plus_1_mn.
Defined.

Definition loose_gen_beta_var
    : forall m n, fin (m + S n) -> lam (m + n) -> lam (m + n).
Proof.
 intros m n v y.
 case (loose_gen_beta_var_comp m n v).
 -
  intros v'.
  apply var.
  apply v'.
 -
  apply y.
Defined.

Definition loose_gen_beta_by_ind
    : forall N, lam N -> forall m n, m + S n = N -> lam (m + n) -> lam (m + n).
Proof.
 refine (ind_lam _ _ _ _).
 -
  intros Ni v m n p y.
  apply loose_gen_beta_var.
  +
   case (eq_sym p).
   apply v.
  +
   apply y.
 -
  intros Ni x IH m n p y.
  apply abs.
  case (eq_sym (plus_1_mn m n)).
  apply IH.
  +
   case p.
   case plus_1_mn with m (S n).
   apply eq_refl.
  +
   case plus_1_mn with m n.
   apply lam_succ.
   apply y.
 -
  intros Ni a b IHa IHb m n p y.
  apply app.
  +
   apply IHa.
   *
    apply p.
   *
    apply y.
  +
   apply IHb.
   *
    apply p.
   *
    apply y.
Defined.

Definition loose_gen_beta
    : forall m n, lam (m + S n) -> lam (m + n) -> lam (m + n).
Proof.
 intros m n x y.
 apply loose_gen_beta_by_ind with (m + S n).
 -
  apply x.
 -
  apply eq_refl.
 -
  apply y.
Defined.

Definition strict_gen_beta
    : forall m n, lam (m + S n) -> lam m -> lam (m + n).
Proof.
 intros m n x y.
 apply loose_gen_beta.
 -
  apply x.
 -
  case plus_comm.
  apply lam_succs.
  apply y.
Defined.

Definition beta
    : forall m, lam (S m) -> lam m -> lam m.
Proof.
 intros m.
 case (eq_sym (plus_n_O m)).
 case (eq_sym (plus_1_mn m 0)).
 apply (loose_gen_beta m 0).
Defined.

(** lam's functions *)

Definition apply
    : forall m, lam (S m) -> lam m -> lam m.
Proof.
 intros m x y.
 apply app.
 -
  apply abs.
  apply x.
 -
  apply y.
Defined.
