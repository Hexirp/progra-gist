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

Definition fin_S : forall P m, fin m -> (forall n, S n = m -> P) -> P.
Proof.
 intros P m [ m' | m' xp ] r; apply r with m'; apply eq_refl.
Defined.

Definition fin_up : forall m, fin m -> fin (S m).
Proof.
 refine (fin_rect _ _ _).
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
 refine (nat_rect _ _ _).
 -
  intros n x.
  apply x.
 -
  intros mp IH n x.
  cbv.
  fold plus.
  apply fin_up.
  fold plus.
  apply IH.
  apply x.
Defined.

Definition fin_full : forall m, fin (S m).
Proof.
 refine (nat_rect _ _ _).
 -
  apply fo.
 -
  intros mp IH.
  apply fs.
  apply IH.
Defined.

(** * lam *)

Inductive lam : nat -> Type :=
| var : forall n, fin n -> lam n
| abs : forall n, lam (S n) -> lam n
| app : forall n, lam n -> lam n -> lam n
.

Definition lam_succ : forall n, lam n -> lam (S n).
Proof.
 refine (lam_rect _ _ _ _).
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
  intros ni a IHa b IHb.
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
 refine (fin_rect _ _ _).
 -
  intros ni y np pnp.
  case (eq_sym (eq_add_S np ni pnp)).
  clear pnp np.
  refine (
   match y in fin (S ni') return option (fin ni') with
   | fo ni'    => None
   | fs ni' yp => Some _
   end
  ); clear y.
  apply yp.
 -
  intros ni xp IHx y np pnp.
  case (eq_sym (eq_add_S np ni pnp)).
  clear pnp np.
  revert xp IHx.
  refine (
   match y in fin (S ni')
    return fin ni' -> (fin ni' -> forall np, S np = ni' -> option (fin np)) -> option (fin ni')
   with
   | fo ni'    => fun xp IHx => fin_S _ ni' xp (fun ni'p pni'p => Some _)
   | fs ni' yp => fun xp IHx => fin_S _ ni' xp (fun ni'p pni'p => _     )
   end
  ); clear y.
  +
   case pni'p.
   apply fo.
  +
   apply option_map with (fin ni'p).
   *
     clear IHx.
     intros IHx.
     case pni'p.
     apply fs.
     apply IHx.
   *
    apply (IHx yp ni'p pni'p).
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
 refine (lam_rec _ _ _ _).
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
  intros Ni a IHa b IHb m n p y.
  apply (app _ (IHa _ _ p y) (IHb _ _ p y)).
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
 apply (app _ (abs _ x) y).
Defined.

(** lam's reduction relation *)

Inductive Head_Reduced {m : nat} : lam m -> lam m -> Prop :=
| head_reduction : forall f x y, beta m f x = y -> Head_Reduced (apply m f x) y
.

Inductive Reduced {m : nat} : lam m -> lam m -> Prop :=
| head_red : forall x y, Head_Reduced x y -> Reduced x y
| abs_red : forall x y, @Reduced (S m) x y -> Reduced (abs m x) (abs m y)
| app_red_l : forall xl xr yl yr, Reduced xl yl -> Reduced (app m xl xr) (app m yl yr)
| app_red_r : forall xl xr yl yr, Reduced xr yr -> Reduced (app m xl xr) (app m yl yr)
.
