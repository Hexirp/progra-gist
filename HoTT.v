Local Unset Elimination Schemes.

Inductive eq (A : Type) (a : A) : A -> Type :=
| eq_refl : eq A a a
.

Scheme eq_ind := Induction for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Type.
Definition eq_rect := eq_ind.

Inductive ex (A : Type) (P : A -> Type) : Type :=
| ex_intro : forall x, P x -> ex A P
.

Definition contr (A : Type) : Type := ex A (fun x => forall y , eq A x y).

Fixpoint trunc (n : nat) (A : Type) : Type :=
 match n with 
 | O => contr A
 | S np => forall x y, trunc np (eq A x y)
 end
.

Inductive Unit : Type :=
| tt : Unit
.

Definition unit_trunc : trunc 0 Unit.
Proof.
 unfold trunc.
 unfold contr.
 refine (
  ex_intro Unit (fun x => forall y, eq Unit x y) tt _
 ).
 refine (
  fun y => _
 ).
 refine (
  match y as y' return eq Unit tt y' with
  | tt => _
  end
 ).
 refine (
  eq_refl Unit tt
 ).
Qed.

Inductive Empty : Type :=
.

Definition empty_trunc : trunc 1 Empty.
Proof.
 unfold trunc.
 refine (
  fun x y => _
 ).
 refine (
  match x as x' return contr (eq Empty x' y) with
  end
 ).
Qed.

Definition trunc_up : forall n A, trunc n A -> trunc (S n) A.
Proof.
 refine (
  fun n A H => _
 ).
 unfold trunc.
 fold (forall x y, trunc n (eq A x y)).
 refine (
  fun x y => _
 ).
 unfold trunc.