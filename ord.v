(* -*- mode: coq; coq-prog-args: ("-nois") -*- *)

(* in Coq 8.8.0 *)

Module Pre.

 (** 事前に定義すべきもの。演算子の優先順位などを一貫させたり、スコープを定義する。 *)

 (** 述語論理の記号 *)

 Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
 Reserved Notation "x <-> y" (at level 95, no associativity).
 Reserved Notation "x /\ y" (at level 80, right associativity).
 Reserved Notation "x \/ y" (at level 85, right associativity).
 Reserved Notation "~ x" (at level 75, right associativity).

 (* 等号及び不等号、大小関係 *)

 Reserved Notation "x = y :> T" (at level 70, y at next level, no associativity).
 Reserved Notation "x = y" (at level 70, no associativity).

 Reserved Notation "x <> y :> T"(at level 70, y at next level, no associativity).
 Reserved Notation "x <> y" (at level 70, no associativity).

 Reserved Notation "x <= y" (at level 70, no associativity).
 Reserved Notation "x < y" (at level 70, no associativity).
 Reserved Notation "x >= y" (at level 70, no associativity).
 Reserved Notation "x > y" (at level 70, no associativity).

 (** 算術演算子 *)

 Reserved Notation "x + y" (at level 50, left associativity).
 Reserved Notation "x - y" (at level 50, left associativity).
 Reserved Notation "x * y" (at level 40, left associativity).
 Reserved Notation "x / y" (at level 40, left associativity).
 Reserved Notation "x ^ y" (at level 30, right associativity).

 Reserved Notation "- x" (at level 35, right associativity).
 Reserved Notation "/ x" (at level 35, right associativity).

 (** スコープ *)

 Delimit Scope type_scope with type.
 Delimit Scope function_scope with function.
 Delimit Scope core_scope with core.

 Bind Scope type_scope with Sortclass.
 Bind Scope function_scope with Funclass.

 Open Scope core_scope.
 Open Scope function_scope.
 Open Scope type_scope.

 (** タクティックの設定 *)

 Declare ML Module "ltac_plugin".

 Export Set Default Proof Mode "Classic".

End Pre.

Module Predicate.

 Export Unset Bracketing Last Introduction Pattern.

 Export Set Typeclasses Strict Resolution.

 Export Unset Elimination Schemes.

 Export Set Keyed Unification.

 Export Unset Refine Instance Mode.

 Export Unset Strict Universe Declaration.

 Export Unset Universe Minimization ToSet.

 Set Implicit Arguments.

 Export Pre.

 (** 関数型 *)

 Definition arrow (A B : Type) : Type := forall (_ : A), B.

 Notation "A -> B" := (forall (_ : A), B) : type_scope.

 (** 汎用関数 *)

 Definition id : forall A, A -> A := fun _ x => x.

 Definition const : forall A B, A -> B -> A := fun _ _ x _ => x.

 Definition compose
     : forall A B C, (A -> B) -> (C -> A) -> C -> B
     := fun _ _ _ f g x => f (g x).

 Definition flip : forall A B C, (A -> B -> C) -> B -> A -> C := fun _ _ _ f x y => f y x.

 Definition apply : forall A B, (A -> B) -> A -> B := fun _ _ f x => f x.

 Inductive Empty : Type :=
 .

 Scheme Empty_ind := Induction for Empty Sort Type.
 Scheme Empty_rec := Minimality for Empty Sort Type.
 Definition Empty_rect := Empty_ind.

 Definition not (A : Type) : Type := A -> Empty.

 Notation "~ x" := (not x) : type_scope.

 Inductive Unit : Type :=
 | tt : Unit
 .

 Scheme Unit_ind := Induction for Unit Sort Type.
 Scheme Unit_rec := Minimality for Unit Sort Type.
 Definition Unit_rect := Unit_ind.

 Inductive and (A B : Type) : Type :=
 | pair : A -> B -> A /\ B
 where
   "A /\ B" := (and A B) : type_scope
 .

 Scheme and_ind := Induction for and Sort Type.
 Scheme and_rec := Minimality for and Sort Type.
 Definition and_rect := and_ind.

 Definition first : forall A B, A /\ B -> A :=
  fun _ _ x => match x with pair xL _ => xL end
 .

 Definition second : forall A B, A /\ B -> B :=
  fun _ _ x => match x with pair _ xR => xR end
 .

 Inductive or (A B : Type) : Type :=
 | left : A -> A \/ B
 | right : B -> A \/ B
 where
   "A \/ B" := (or A B) : type_scope
 .

 Scheme or_ind := Induction for or Sort Type.
 Scheme or_rec := Minimality for or Sort Type.
 Definition or_rect := or_ind.

 Theorem and_map_l : forall A B C : Type, (A -> B) -> A /\ C -> B /\ C.
 Proof.
  intros A B C f [xl xr]; apply (pair (f xl) xr).
 Qed.

 Theorem and_map_r : forall A B C : Type, (A -> B) -> C /\ A -> C /\ B.
 Proof.
  intros A B C f [xl xr]; apply (pair xl (f xr)).
 Qed.

 Theorem or_map_l : forall A B C : Type, (A -> B) -> A \/ C -> B \/ C.
 Proof.
  intros A B C f [xl | xr]; [> apply (left _ (f xl)) | apply (right _ xr) ].
 Qed.

 Theorem or_map_r : forall A B C : Type, (A -> B) -> C \/ A -> C \/ B.
 Proof.
  intros A B C f [xl | xr]; [> apply (left _ xl) | apply (right _ (f xr)) ].
 Qed.

 Theorem imp_map_l : forall A B C : Type, (A -> B) -> (B -> C) -> (A -> C).
 Proof.
  intros A B C f g; apply (compose g f).
 Qed.

 Theorem imp_map_r : forall A B C : Type, (A -> B) -> (C -> A) -> (C -> B).
 Proof.
  intros A B C f g; apply (compose f g).
 Qed.

 Theorem not_map : forall A B : Type, (A -> B) -> ~ B -> ~ A.
 Proof.
  intros A B f x; unfold not; unfold not in x; apply (compose x f).
 Qed.

 Definition iff (A B : Type) : Type := (A -> B) /\ (B -> A).

 Notation "A <-> B" := (iff A B) : type_scope.

 Theorem iff_refl : forall A, A <-> A.
 Proof.
  intros A.
  apply (pair (@id A) (@id A)).
 Qed.

 Theorem iff_sym : forall A B, (A <-> B) -> (B <-> A).
 Proof.
  intros A B x.
  apply (pair (second x) (first x)).
 Qed.

 Theorem iff_trans : forall A B C, (A <-> B) -> (C <-> A) -> (C <-> B).
 Proof.
  intros A B C x y.
  apply pair.
  -
   apply (compose (first x) (first y)).
  -
   apply (compose (second y) (second x)).
 Qed.

 Theorem and_iff_map_l
     : forall A B C : Type, (A <-> B) -> (A /\ C <-> B /\ C).
 Proof.
  intros A B C [xl xr]; apply (pair (and_map_l xl) (and_map_l xr)).
 Qed.

 Theorem and_iff_map_r
     : forall A B C : Type, (A <-> B) -> (C /\ A <-> C /\ B).
 Proof.
  intros A B C [xl xr]; apply (pair (and_map_r xl) (and_map_r xr)).
 Qed.

 Theorem or_iff_map_l
     : forall A B C : Type, (A <-> B) -> (A \/ C <-> B \/ C).
 Proof.
  intros A B C [xl xr]; apply (pair (or_map_l xl) (or_map_l xr)).
 Qed.

 Theorem or_iff_map_r : forall A B C : Type, (A <-> B) -> (C \/ A <-> C \/ B).
 Proof.
  intros A B C [xl xr]; apply (pair (or_map_r xl) (or_map_r xr)).
 Qed.

 Theorem imp_iff_map_l : forall A B C : Type, (A <-> B) -> ((A -> C) <-> (B -> C)).
 Proof.
  intros A B C [xl xr]; apply (pair (imp_map_l xr) (imp_map_l xl)).
 Qed.

 Theorem imp_iff_map_r : forall A B C : Type, (A <-> B) -> ((C -> A) <-> (C -> B)).
 Proof.
  intros A B C [xl xr]; apply (pair (imp_map_r xl) (imp_map_r xr)).
 Qed.

 Theorem not_iff_map : forall A B : Type, (A <-> B) -> (~ A <-> ~B).
 Proof.
  intros A B [xl xr]; apply (pair (not_map xr) (not_map xl)).
 Qed.

 Theorem neg_false : forall A : Type, ~ A <-> (A <-> Empty).
 Proof.
 Admitted.

 Theorem and_cancel_l : forall A B C : Prop,
   (B -> A) -> (C -> A) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
 Proof.
 Admitted.

 Theorem and_cancel_r : forall A B C : Prop,
   (B -> A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
 Proof.
 Admitted.

 Theorem and_comm : forall A B : Prop, A /\ B <-> B /\ A.
 Proof.
 Admitted.

 Theorem and_assoc : forall A B C : Prop, (A /\ B) /\ C <-> A /\ B /\ C.
 Proof.
 Admitted.

 Theorem or_cancel_l : forall A B C : Prop,
   (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
 Proof.
 Admitted.

 Theorem or_cancel_r : forall A B C : Prop,
   (B -> ~ A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
 Proof.
 Admitted.

 Theorem or_comm : forall A B : Prop, (A \/ B) <-> (B \/ A).
 Proof.
 Admitted.

 Theorem or_assoc : forall A B C : Prop, (A \/ B) \/ C <-> A \/ B \/ C.
 Proof.
 Admitted.

 Inductive ex (A : Type) (P : A -> Type) : Type :=
 | ex_pair : forall x, P x -> ex P
 .

 Notation "'exists' x .. y , p"
   :=
     (ex (fun x => .. (ex (fun y => p)) ..))
   (
     at level 200,
     x binder,
     right associativity,
     format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
   :
     type_scope.

 Scheme ex_ind := Induction for ex Sort Type.
 Scheme ex_rec := Minimality for ex Sort Type.
 Definition ex_rect := ex_ind.

 Definition all (A : Type) (P : A -> Type) : Type := forall x, P x.

 Inductive eq (A : Type) (x : A) : A -> Type :=
 | eq_refl : x = x :> A
 where
   "x = y :> A" := (@eq A x y) : type_scope
 .

 Scheme eq_ind := Induction for eq Sort Type.
 Scheme eq_rec := Minimality for eq Sort Type.
 Definition eq_rect := eq_ind.

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
End Induction_Defs.

Module Type Extensionality (Export Model : Ord).
 Axiom extension : forall a b, (forall x, lt x a <-> lt x b) -> a = b.
End Extensionality.

Module Extensionality_Defs (Model : Ord) (Export ExModel : Extensionality Model).
End Extensionality_Defs.

Module Type Transitivity (Export Model : Ord).
 Axiom transition : forall a b c, lt a b -> lt b c -> lt a c.
End Transitivity.

Module Transitivity_Defs (Model : Ord) (Export TransModel : Transitivity Model).
End Transitivity_Defs.

Module IndExTrans_Defs
  (Model : Ord)
  (Export IndModel : Induction Model)
  (Export ExModel : Extensionality Model)
  (Export TransModel : Transitivity Model).

 Module IndDefs := Induction_Defs Model IndModel.
 Export IndDefs.

 Module ExDefs := Extensionality_Defs Model ExModel.
 Export ExDefs.

 Module TransDefs := Transitivity_Defs Model TransModel.
 Export TransDefs.

 (*
  double-negation translated [forall x y, x = y \/ lt x y \/ lt y x] (Gödel–Gentzen translation)
 *)
 Definition trichotomy : forall x y, ~ (~ ~ ~ x = y /\ ~ ~ (~ ~ ~ lt x y /\ ~ ~ ~ lt y x)).
 Proof.
  intros x y H.
  case H.
  intros HL HR.
  apply HL.
  intros HL'.
  apply HR.
  intros HR'.
  case HR'.
  intros HR'L HR'R.
  apply HR'L.

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
