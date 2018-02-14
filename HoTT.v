(* coqide -nois *)

Global Unset Elimination Schemes.

Module Pre.
 Delimit Scope type_scope with type.

 Open Scope type_scope.

 Notation "x -> y"
   := (forall (_ : x), y) (at level 99, right associativity, y at level 200) : type_scope.
End Pre.

Module Function.
 Import Pre.

 Definition idmap A : A -> A := fun x => x.

 Definition const A B : A -> B -> A := fun x _ => x.

 Definition compose A B C : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

 Definition flip A B C : (B -> A -> C) -> A -> B -> C := fun f x y => f y x.

 Definition dep A B : (A -> A -> B) -> A -> B := fun f x => f x x.
End Function.

Module Unit.
 Inductive unit : Type :=
 | I : unit
 .

 Scheme unit_ind := Induction for unit Sort Type.
 Scheme unit_rec := Minimality for unit Sort Type.
 Definition unit_rect := unit_ind.
End Unit.

Module Empty.
 Import Pre.

 Inductive empty : Type :=
 .

 Scheme empty_ind := Induction for empty Sort Type.
 Scheme empty_rec := Minimality for empty Sort Type.
 Definition empty_rect := empty_ind.

 Definition not (A : Type) : Type := A -> empty.

 Notation "~ x" := (not x) (at level 75, right associativity) : type_scope.

 Definition exfalso := empty_rec.

 Definition absurd A B : A -> ~ A -> B := fun H nH => exfalso B (nH H).
End Empty.

Module And.
 Import Pre.

 Inductive and (A B : Type) : Type :=
 | prod : A -> B -> and A B
 .

 Scheme and_ind := Induction for and Sort Type.
 Scheme and_rec := Minimality for and Sort Type.
 Definition and_rect := and_ind.

 Notation "x /\ y" := (and x y) (at level 80, right associativity) : type_scope.

 Definition first A B : A /\ B -> A := fun H => match H with prod _ _ Ha _ => Ha end.

 Definition second A B : A /\ B -> B := fun H => match H with prod _ _ _ Hb => Hb end.
End And.

Module Or.
 Import Pre.

 Inductive or (A B : Type) : Type :=
 | left : A -> or A B
 | right : B -> or A B
 .

 Scheme or_ind := Induction for or Sort Type.
 Scheme or_rec := Minimality for or Sort Type.
 Definition or_rect := or_ind.

 Notation "x \/ y" := (or x y) (at level 85, right associativity) : type_scope.
End Or.

Module Iff.
 Import Pre And.

 Definition iff A B := A -> B /\ B -> A.

 Notation "x <-> y" := (iff x y) (at level 95, no associativity) : type_scope.
End Iff.

Module Eq.
 Import Pre.

 Inductive eq (A : Type) (a : A) : A -> Type :=
 | eq_refl : eq A a a
 .

 Scheme eq_ind := Induction for eq Sort Type.
 Scheme eq_rec := Minimality for eq Sort Type.
 Definition eq_rect := eq_ind.

 Definition eq_sym : forall A x y, eq A x y -> eq A y x := fun A x y p =>
  match p with
  | eq_refl _ _ => eq_refl A x
  end
 .

 Definition eq_trans : forall A x y z, eq A x y -> eq A y z -> eq A x z := fun A x y z p =>
  match p with
  | eq_refl _ _ => fun q =>
   match q with
   | eq_refl _ _ => eq_refl A x
   end
  end
 .

 Definition eq_stepl : forall A x y z, eq A z x -> eq A z y -> eq A x y := fun A x y z p =>
  match p with
  | eq_refl _ _ => fun q =>
   match q with
   | eq_refl _ _ => eq_refl A z
   end
  end
 .

 Definition eq_stepr := eq_trans.
End Eq.

Module Ex.
 Import Pre.

 Inductive ex (A : Type) (P : A -> Type) : Type :=
 | ex_intro : forall x, P x -> ex A P
 .

 Scheme ex_ind := Induction for ex Sort Type.
 Scheme ex_rec := Minimality for ex Sort Type.
 Definition ex_rect := ex_ind.
End Ex.

Module Nat.
 Import Pre.

 Inductive nat : Type :=
 | O : nat
 | S : nat -> nat
 .

 Scheme nat_ind := Induction for nat Sort Type.
 Scheme nat_rec := Minimality for nat Sort Type.
 Definition nat_rect := nat_ind.
End Nat.

Module Path.
 Import Pre Eq.

 Definition eq_eq_stepl : forall A x y (p : eq A y x),
     eq (eq A x x) (eq_stepl A x x y p p) (eq_refl A x) := fun A x y p =>
  match p with
  | eq_refl _ _ => eq_refl (eq A y y) (eq_refl A y)
  end
 .

 Definition inverse := eq_sym.

 Definition concat := eq_trans.

 Definition transport : forall A (P : A -> Type) x y,
     eq A x y -> P x -> P y := fun A P x y p xP =>
  match p with
  | eq_refl _ _ => xP
  end
 .

 Definition ap : forall A B (f : A -> B) x y,
     eq A x y -> eq B (f x) (f y) := fun A B f x y p =>
  match p with
  | eq_refl _ _ => eq_refl B (f x)
  end
 .

 Definition ap01 := ap.

 Definition apD10 : forall A (B : A -> Type) (f g : forall x : A, B x),
     eq (forall x : A, B x) f g -> forall x, eq (B x) (f x) (g x) := fun A B f g p x =>
  match p with
  | eq_refl _ _ => eq_refl (B x) (f x)
  end
 .

 Definition ap10 : forall A B (f g : A -> B), eq (A -> B) f g -> forall x, eq B (f x) (g x)
     := fun A B => apD10 A (fun _ => B).

 Definition ap11 : forall A B (f g : A -> B),
     eq (A -> B) f g -> forall x y, eq A x y -> eq B (f x) (g y) := fun A B f g p x y q =>
  match p with
  | eq_refl _ _ =>
   match q with
   | eq_refl _ _ => eq_refl B (f x)
   end
  end
 .

 Definition eq_pointwise A (P : A -> Type) (f g : forall x, P x) x := eq (P x) (f x) (g x).
End Path.

Module Contr.
 Import Pre Ex Eq Path.

 Definition contr (A : Type) : Type := ex A (fun x => forall y, eq A x y).

 Definition eq_contr : forall A, contr A -> forall x y, eq A x y := fun A H x y =>
  match H with
  | ex_intro _ _ Hc HH => eq_stepl A x y Hc (HH x) (HH y)
  end
 .

 Definition eq_eq_contr : forall A H x y (p : eq A x y),
     eq (eq A x y) (eq_contr A H x y) p := fun A H x y p =>
  match H with
  | ex_intro _ _ Hc HH =>
   match p with
   | eq_refl _ _ => eq_eq_stepl A x Hc (HH x)
   end
  end
 .

 Definition contr_eq_contr : forall A, contr A -> forall x y, contr (eq A x y) := fun A H x y =>
  ex_intro
   (eq A x y)
   (fun p => forall q, eq (eq A x y) p q)
   (eq_contr A H x y)
   (fun q => eq_eq_contr A H x y q).
End Contr.

Module Trunc.
 Export Pre Ex Nat Eq Contr.

 Definition trunc : nat -> Type -> Type :=
  nat_ind (fun _ => Type -> Type)
   (fun      A => contr A)
   (fun _ IH A => forall x y, IH (eq A x y))
 .

 Definition trunc_succ : forall n A, trunc n A -> trunc (S n) A :=
  nat_ind (fun n => forall A, trunc n A -> forall x y, trunc n (eq A x y))
   (fun A H x y => contr_eq_contr A H x y)
   (fun np IH A H x y => IH (eq A x y) (H x y))
 .
End Trunc.

Module Truncs.
 Export Trunc.
 Import Unit Empty.

 Print trunc_succ.

Import Pre Function Unit And Or Iff Eq Ex.

Definition trunc_unit : trunc O unit.
Proof.
 apply ex_intro with tt.
 intros y.
 destruct y.
 apply eq_refl.
Defined.

Definition trunc_empty : trunc (S O) empty.
Proof.
 intros x.
 destruct x.
Defined.

Definition dec (A : Type) : Type := or A (not A).

Definition not_eq_o_s : forall n, not (eq nat O (S n)).
Proof.
 intros n H.
 refine (eq_rec _ O (fun x => match x return Type with O => unit | S xp => empty end) _ (S n) _).
 -
  apply tt.
 -
  apply H.
Defined.

Definition eq_s : forall m n, eq nat m n -> eq nat (S m) (S n).
Proof.
 intros m n p.
 destruct p.
 apply eq_refl.
Defined.

Definition pred (n : nat) : nat := match n with O => O | S np => np end.

Definition eq_s_inv : forall m n, eq nat (S m) (S n) -> eq nat m n.
Proof.
 intros m n p.
 stepl (pred (S m)).
 -
  apply eq_refl.
 -
  stepr (pred (S n)).
  +
   destruct p.
   apply eq_refl.
  +
   apply eq_refl.
Defined.

Definition dec_eq_nat : forall m n, dec (eq nat m n).
Proof.
 apply (nat_ind (fun m => forall n, dec (eq nat m n))).
 -
  intros n.
  destruct n.
  +
   apply left.
   apply eq_refl.
  +
   apply right.
   apply not_eq_o_s.
 -
  intros mp IH n.
  destruct n.
  +
   apply right.
   intros p.
   apply not_eq_o_s with mp.
   apply eq_sym.
   apply p.
  +
   destruct (IH n) as [p | np].
   *
    apply left.
    apply eq_s.
    apply p.
   *
    apply right.
    intros p.
    apply np.
    apply eq_s_inv.
    apply p.
Defined.

Definition trunc_eq_nat : forall m n, trunc (S O) (eq nat m n).
Proof.
 intros m n.
 destruct (dec_eq_nat m n) as [H | nH].
 -
  destruct H.
  apply trunc_succ.
  apply ex_intro with (eq_refl nat m).
  intros p.
  admit.
 -
  intros p.
  apply exfalso.
  apply nH.
  apply p.
Admitted.

(** ** 等価性 *)

Definition fiber (A B : Type) (f : A -> B) (b : B) : Type :=
 ex A (fun a => eq B (f a) b)
.

Definition equiv (A B : Type) (f : A -> B) : Type := forall b, contr (fiber A B f b).

Definition equiv_hom (A B : Type) (f : A -> B) (g : B -> A) : Type :=
 and (forall a, eq A (g (f a)) a) (forall b, eq B (f (g b)) b)
.

Definition equiv_adj (A B : Type) (f : A -> B) (g : B -> A) : Type.
Proof.
Admitted.

Definition iso_hom (A B : Type) (f : A -> B) : Type :=
 and
  (ex (B -> A) (fun g => forall a, eq A (g (f a)) a))
  (ex (B -> A) (fun h => forall b, eq B (f (h b)) b))
.
