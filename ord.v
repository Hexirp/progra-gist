(* -*- mode: coq; coq-prog-args: ("-nois") -*- *)

Declare ML Module "ltac_plugin".

Global Set Default Proof Mode "Classic".

Module Pre.
 Reserved Notation "'exists' x .. y , p" (
   at level 200,
   x binder,
   right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'").

 Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
 Reserved Notation "x <-> y" (at level 95, no associativity).
 Reserved Notation "x /\ y" (at level 80, right associativity).
 Reserved Notation "x \/ y" (at level 85, right associativity).
 Reserved Notation "~ x" (at level 75, right associativity).

 Reserved Notation "x = y :> T" (at level 70, y at next level, no associativity).
 Reserved Notation "x = y" (at level 70, no associativity).

 Reserved Notation "x <> y :> T"(at level 70, y at next level, no associativity).
 Reserved Notation "x <> y" (at level 70, no associativity).

 Reserved Notation "x <= y" (at level 70, no associativity).
 Reserved Notation "x < y" (at level 70, no associativity).
 Reserved Notation "x >= y" (at level 70, no associativity).
 Reserved Notation "x > y" (at level 70, no associativity).

 Reserved Notation "x + y" (at level 50, left associativity).
 Reserved Notation "x - y" (at level 50, left associativity).
 Reserved Notation "x * y" (at level 40, left associativity).
 Reserved Notation "x / y" (at level 40, left associativity).
 Reserved Notation "x ^ y" (at level 30, right associativity).

 Reserved Notation "- x" (at level 35, right associativity).
 Reserved Notation "/ x" (at level 35, right associativity).

 Delimit Scope type_scope with type.
 Delimit Scope function_scope with function.
 Delimit Scope core_scope with core.

 Bind Scope type_scope with Sortclass.
 Bind Scope function_scope with Funclass.

 Open Scope core_scope.
 Open Scope function_scope.
 Open Scope type_scope.
End Pre.

Module Predicate.
 Export Pre.

 Notation "A -> B" := (forall (_ : A), B) : type_scope.

 Definition arrow (A B : Type) : Type := A -> B.

 Definition idfunc : forall A, A -> A := fun _ x => x.

 Inductive Empty : Type :=
 .

 Definition not (A : Type) : Type := A -> Empty.

 Notation "~ x" := (not x) : type_scope.

 Inductive Unit : Type :=
 | tt : Unit
 .

 Inductive and (A B : Type) : Type :=
 | pair : A -> B -> A /\ B
 where
   "A /\ B" := (and A B) : type_scope
 .

 Definition first : forall A B, A /\ B -> A :=
  fun _ _ x => match x with pair _ _ xL _ => xL end
 .

 Definition second : forall A B, A /\ B -> B :=
  fun _ _ x => match x with pair _ _ _ xR => xR end
 .

 Inductive or (A B : Type) : Type :=
 | left : A -> A \/ B
 | right : B -> A \/ B
 where
   "A \/ B" := (or A B) : type_scope
 .

 Definition iff (A B : Type) : Type := (A -> B) /\ (B -> A).

 Notation "A <-> B" := (iff A B) : type_scope.

 Definition iff_apply_l : forall A B, A <-> B -> A -> B.
 Proof.
  intros A B x.
  apply first with (B -> A).
  apply x.
 Qed.

 Definition iff_apply_r : forall A B, A <-> B -> B -> A.
 Proof.
  intros A B x.
  apply second with (A -> B).
  apply x.
 Qed.

 Definition iff_refl : forall A, A <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply idfunc.
  -
   apply idfunc.
 Qed.

 Definition iff_sym : forall A B, (A <-> B) -> (B <-> A).
 Proof.
  intros A B x.
  apply pair.
  -
   apply (iff_apply_r _ _ x).
  -
   apply (iff_apply_l _ _ x).
 Qed.

 Definition iff_trans : forall A B C, (A <-> B) -> (B <-> C) -> (A <-> C).
 Proof.
  intros A B C x y.
  apply pair.
  -
   intros a.
   apply (iff_apply_l _ _ y).
   apply (iff_apply_l _ _ x).
   apply a.
  -
   intros c.
   apply (iff_apply_r _ _ x).
   apply (iff_apply_r _ _ y).
   apply c.
 Qed.

 Inductive ex (A : Type) (P : A -> Type) : Type :=
 | ex_pair : forall x, P x -> ex A P
 .

 Notation "'exists' x .. y , p" := (ex _ (fun x => .. (ex _ (fun y => p)) ..)) : type_scope.

 Definition all (A : Type) (P : A -> Type) : Type := forall x, P x.

 Inductive eq (A : Type) (x : A) : A -> Type :=
 | eq_refl : x = x :> A
 where
   "x = y :> A" := (eq A x y) : type_scope
 .

 Notation "x = y" := (x = y :> _) : type_scope.
 Notation "x <> y :> T" := (~ x = y :> T) : type_scope.
 Notation "x <> y" := (x <> y :> _) : type_scope.

 Definition eq_sym : forall A (x y : A), x = y -> y = x.
 Proof.
  intros A x y p.
  case p.
  apply eq_refl.
 Qed.

 Definition eq_trans : forall A (x y z : A), x = y -> y = z -> x = z.
 Proof.
  intros A x y z p q.
  case q.
  apply p.
 Qed.

 Definition not_and_then : forall A B, (A -> ~ B) -> ~ (A /\ B).
 Proof.
  intros A B H x.
  case x.
  apply H.
 Qed.

 Definition not_then_and : forall A B, ~ (A /\ B) -> A -> ~ B.
 Proof.
  intros A B H a b.
  apply H.
  apply pair.
  -
   apply a.
  -
   apply b.
 Qed.

 Definition map_not : forall A B, (A -> B) -> ~ B -> ~ A.
 Proof.
  intros A B H nb a.
  apply nb.
  apply H.
  apply a.
 Qed.

 Definition not_then_then : forall A B, (A -> ~ B) -> B -> ~ A.
 Proof.
  intros A B H b a.
  apply H.
  -
   apply a.
  -
   apply b.
 Qed.

 Definition intro_double_not : forall A, A -> ~ ~ A.
 Proof.
  intros A a na.
  apply na.
  apply a.
 Qed.

 Definition map_double_not : forall A B, (A -> B) -> ~ ~ A -> ~ ~ B.
 Proof.
  intros A B H.
  apply map_not.
  apply map_not.
  apply H.
 Qed.

 Definition apply_double_not : forall A B, ~ ~ (A -> B) -> ~ ~ A -> ~ ~ B.
 Proof.
  intros A B nnH nna nb.
  apply nnH.
  intros H.
  revert nb.
  revert nna.
  apply map_double_not.
  apply H.
 Qed.
End Predicate.

Module Peano.
 Export Predicate.

 Inductive nat : Type :=
 | O : nat
 | S : nat -> nat
 .

 Definition not_eq_O_S : forall n, O <> S n.
 Proof.
  intros n p.
  refine (
   match p in _ = x' return (match x' with O => Unit | S xp => Empty end) with
   | eq_refl _ _ => _
   end
  ).
  apply tt.
 Qed.

 Definition pred : nat -> nat :=
  fun x =>
   match x with
   | O => O
   | S xp => xp
   end
 .

 Inductive le (m : nat) : nat -> Type :=
 | le_n : le m m
 | le_S : forall n, le m n -> le m (S n)
 .

 Definition le_rect_simple : forall (m : nat) (P : nat -> Type),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P cN cS.
  apply le_rect.
  -
   apply cN.
  -
   apply cS.
 Qed.

 Definition le_ind_simple : forall (m : nat) (P : nat -> Prop),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P cN cS.
  apply le_rect.
  -
   apply cN.
  -
   apply cS.
 Qed.

 Definition le_rec_simple : forall (m : nat) (P : nat -> Set),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P.
  apply le_rect_simple.
 Qed.

 Definition le_0_n : forall n : nat, le O n.
 Proof.
  intros n.
  induction n as [ | n IHn ].
  -
   apply le_n.
  -
   apply le_S.
   apply IHn.
 Qed.

 Definition le_n_S : forall m n : nat, le m n -> le (S m) (S n).
 Proof.
  intros m.
  apply le_rect_simple.
  -
   apply le_n.
  -
   intros n nH H.
   apply le_S.
   apply H.
 Qed.

 Definition le_pred : forall m n : nat, le m n -> le (pred m) (pred n).
 Proof.
  intros m.
  apply le_rect_simple.
  -
   apply le_n.
  -
   intros [ | np ] nH H.
   +
    apply H.
   +
    cut (forall k, S (pred (S k)) = pred (S (S k))).
    *
     intros Lem.
     case (Lem np).
     apply le_S.
     apply H.
    *
     intros k.
     apply eq_refl.
 Qed.

 Definition le_S_n : forall m n : nat, le (S m) (S n) -> le m n.
 Proof.
  intros m n H.
  apply (le_pred (S m) (S n)).
  apply H.
 Qed.

 Definition le_trans : forall m n o, le m n -> le n o -> le m o.
 Proof.
  intros m n o H.
  revert o.
  apply le_rect_simple.
  -
   apply H.
  -
   intros o oH IH.
   apply le_S.
   apply IH.
 Qed.

 Definition lt m n := le (S m) n.

 Definition not_lt_n_0 : forall n, ~ lt n O.
 Proof.
  intros n nH.
  cut (O = O).
  -
   refine (
    match nH in le _ o' return O <> o' with
    | le_n _ => _
    | le_S _ o pH => _
    end
   ).
   +
    apply not_eq_O_S.
   +
    apply not_eq_O_S.
  -
   apply eq_refl.
 Qed.
End Peano.

Export Peano.

Module Type Ord.
 Parameter ord : Type.
 Parameter lt : ord -> ord -> Type.
End Ord.

Module Ord_Defs (Export Model : Ord).
 Definition le : ord -> ord -> Type := fun a b => lt a b \/ a = b.

 Definition le_lt : forall a b, lt a b -> le a b.
 Proof.
  intros a b H.
  apply left.
  apply H.
 Qed.

 Definition le_eq : forall a b, a = b -> le a b.
 Proof.
  intros a b H.
  apply right.
  apply H.
 Qed.

 Definition le_refl : forall a, le a a.
 Proof.
  intros a.
  apply le_eq.
  apply eq_refl.
 Qed.
End Ord_Defs.

Module Type Induction (Export Model : Ord).
 Axiom ind
   : forall p : ord -> Type, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
End Induction.

Module Induction_Defs (Model : Ord) (Export IndModel : Induction Model).
 Module Model_Ord_Defs := Ord_Defs Model.
 Export Model_Ord_Defs.

 Definition not_lt_refl : forall a, ~ lt a a.
 Proof.
  apply (ind (fun a => ~ lt a a)).
  intros a IHa H.
  apply IHa with a.
  -
   apply H.
  -
   apply H.
 Qed.

 Definition not_lt_sym : forall a b, lt a b -> ~ lt b a.
 Proof.
  apply (ind (fun a => forall b, lt a b -> ~ lt b a)).
  intros a IHa b Ha Hb.
  apply IHa with b a.
  -
   apply Hb.
  -
   apply Hb.
  -
   apply Ha.
 Qed.

 Definition not_lt_sym_and : forall a b, ~ (lt a b /\ lt b a).
 Proof.
  intros a b.
  apply not_and_then.
  apply not_lt_sym.
 Qed.

 Definition not_lt_inf_dec_chain : forall f, ~ (forall n, lt (f (S n)) (f n)).
 Proof.
  intros f inf_dec_chain.
  cut (forall a x, f x <> a).
  -
   intros H.
   apply H with (f O) O.
   apply eq_refl.
  -
   apply (ind (fun a => forall x, f x <> a)).
   intros a IHa x H.
   apply IHa with (f (S x)) (S x).
   +
    case H.
    apply inf_dec_chain.
   +
    apply eq_refl.
 Qed.

 Definition not_le_lt : forall a b, lt a b -> ~ le b a.
 Proof.
  intros a b H [L | R].
  -
   apply not_lt_sym with a b.
   +
    apply H.
   +
    apply L.
  -
   revert H.
   case R.
   apply not_lt_refl.
 Qed.

 Definition not_and_lt_le : forall a b, ~ (lt a b /\ le b a).
 Proof.
  intros a b.
  apply not_and_then.
  apply not_le_lt.
 Qed.

 Definition not_lt_le : forall a b, le a b -> ~ lt b a.
 Proof.
  intros a b.
  apply not_then_then.
  apply not_le_lt.
 Qed.

 Section Not_exists_latter.
  Variable base : ord.
  Variable ex_latter : forall x, exists y, lt y x.

  Definition f : nat -> ord.
  Proof.
   apply (nat_rect (fun _ => ord)).
   -
    apply base.
   -
    intros n IHn.
    case (ex_latter IHn).
    intros IHnp IHnpH.
    apply IHnp.
  Defined.

  Definition f_inf_dec_chain : forall n, lt (f (S n)) (f n).
  Proof.
   intros n.
   cbn.
   case (ex_latter (f n)).
   intros x xH.
   apply xH.
  Qed.

  Definition not_exists_latter : Empty.
  Proof.
   apply not_lt_inf_dec_chain with f.
   apply f_inf_dec_chain.
  Qed.
 End Not_exists_latter.

 Print f.
End Induction_Defs.

Module Type Extensionality (Export Model : Ord).
 Axiom extension : forall a b, (forall x, lt x a <-> lt x b) -> a = b.
End Extensionality.

Module Extensionality_Defs (Model : Ord) (ExModel : Extensionality Model).
End Extensionality_Defs.

Module Nat_Ord <: Ord.
 Definition ord : Type := nat.
 Definition lt : ord -> ord -> Type := lt.
End Nat_Ord.

Module Nat_Induction <: Induction Nat_Ord.
 Export Nat_Ord.

 Definition ind
   : forall p : ord -> Type, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
 Proof.
  intros p f.
  cut (forall n k, lt k n -> p k).
  -
   intros Lem a.
   apply f.
   apply Lem.
  -
   apply (nat_rect (fun n => forall k, lt k n -> p k)).
   +
    intros k kH.
    apply Empty_rect.
    apply not_lt_n_0 with k.
    apply kH.
   +
    intros n IHn k kH.
    apply f.
    intros x xH.
    apply IHn.
    apply le_trans with k.
    *
     apply xH.
    *
     apply le_S_n.
     apply kH.
 Qed.
End Nat_Induction.
