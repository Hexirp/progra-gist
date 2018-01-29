Require Import Init.

Inductive var : Type :=
 | S : var
 | K : var
.

Inductive tre : Type -> Type :=
 | V : forall {a}, a -> tre a
 | A : forall {a}, tre a -> tre a -> tre a
.

Definition ter : Type := tre var.

Definition S_beta : var -> var -> var -> ter := fun x y z => A (A (V x) (V z)) (A (V y) (V z)).

Definition K_beta : var -> var -> ter := fun x y => V x.

Definition head_beta : ter -> ter :=
 fun x => match x with
 | V xv => V xv
 | A xl xr => match xl with
  | V xlv => A (V xlv) xr
  | A xll xlr => match xl