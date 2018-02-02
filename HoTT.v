Local Unset Elimination Schemes.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.
Definition nat_rect := nat_ind.

Inductive eq (A : Type) (a : A) : A -> Type :=
| eq_refl : eq A a a
.

Scheme eq_ind := Induction for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Type.
Definition eq_rect := eq_ind.

Definition eq_xy_zx_zy : forall A x y z, eq A z x -> eq A z y -> eq A x y.
Proof.
 intros A x y z zx zy.
 destruct zx.
 destruct zy.
 apply eq_refl.
Defined.

Definition eq_eq_xy_zx_zy : forall A x y (p : eq A y x),
    eq (eq A x x) (eq_xy_zx_zy A x x y p p) (eq_refl A x).
Proof.
 intros A x y p.
 destruct p.
 apply eq_refl.
Defined.

Inductive contr (A : Type) : Type :=
| contr_intro : forall x, (forall y, eq A x y) -> contr A
.

Inductive trunc : nat -> Type -> Type :=
| trunc_contr : forall A, contr A -> trunc O A
| trunc_up : forall n A, (forall x y, trunc n (eq A x y)) -> trunc (S n) A
.

Definition contr_trunc : forall A, trunc O A -> contr A.
Proof.
 intros A H.
 inversion H as [HA Hc HnH HAH |].
 apply Hc.
Defined.

Definition trunc_down : forall n A, trunc (S n) A -> forall x y, trunc n (eq A x y).
Proof.
 intros n A H.
 inversion H as [| Hn HA Ht HnH HAH].
 apply Ht.
Defined.

Scheme trunc_ind := Induction for trunc Sort Type.
Scheme trunc_rec := Minimality for trunc Sort Type.
Definition trunc_rect := trunc_ind.

Definition eq_contr : forall A, contr A -> forall x y, eq A x y.
Proof.
 intros A H x y.
 destruct H as [Hc HH].
 apply eq_xy_zx_zy with Hc.
 -
  apply HH.
 -
  apply HH.
Defined.

Definition eq_eq_contr : forall A H x y p, eq (eq A x y) (eq_contr A H x y) p.
Proof.
 intros A H x y p.
 destruct p.
 destruct H as [Hc HH].
 apply eq_eq_xy_zx_zy.
Defined.

Definition contr_eq_contr : forall A, contr A -> forall x y, contr (eq A x y).
Proof.
 intros A H x y.
 apply contr_intro with (eq_contr A H x y).
 apply eq_eq_contr.
Defined.

Definition trunc_succ : forall n A, trunc n A -> trunc (S n) A.
Proof.
 intros n.
 induction n as [| n IH].
 -
  intros A H.
  apply trunc_up.
  intros x y.
  apply trunc_contr.
  apply contr_eq_contr.
  apply contr_trunc.
  apply H.
 -
  intros A H.
  apply trunc_up.
  intros x y.
  apply IH.
  revert x y.
  apply trunc_down.
  apply H.
Defined.
