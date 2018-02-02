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

Inductive ex (A : Type) (P : A -> Type) : Type :=
| ex_intro : forall x, P x -> ex A P
.

Scheme ex_ind := Induction for ex Sort Type.
Scheme ex_rec := Minimality for ex Sort Type.
Definition ex_rect := ex_ind.

Definition contr (A : Type) : Type := ex A (fun x => forall y, eq A x y).

Fixpoint trunc (n : nat) (A : Type) : Type :=
 match n with 
 | O => contr A
 | S np => forall x y, trunc np (eq A x y)
 end
.

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

Definition eq_eq_contr : forall A, contr A -> forall x y p q, eq (eq A x y) p q.
Proof.
 intros A H x y p q.
 assert (K : forall r, eq (eq A x y) (eq_contr A H x y) r).
 -
  intros r.
  destruct r.
  destruct H as [Hc HH].
  unfold eq_contr.
  apply eq_eq_xy_zx_zy.
 -
  apply eq_xy_zx_zy with (eq_contr A H x y).
  +
   apply K.
  +
   apply K.
Defined.

Definition contr_eq_contr : forall A, contr A -> forall x y, contr (eq A x y).
Proof.
 intros A H x y.
 apply ex_intro with (eq_contr A H x y).
 intros c.
 apply eq_eq_contr.
 apply H.
Defined.

Definition trunc_succ : forall n A, trunc n A -> trunc (S n) A.
Proof.
 intros n.
 induction n as [| n IH].
 -
  intros A.
  unfold trunc.
  intros H.
  apply contr_eq_contr.
  apply H.
 -
  intros A H x y.
  apply IH.
  apply H.
Defined.
