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

 Export Set Implicit Arguments.

 Export Unset Strict Implicit.

 Export Set Contextual Implicit.

 Export Set Reversible Pattern Implicit.

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
 Definition Empty_rect := @Empty_ind.

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

 Definition exfalso : forall A : Type, Empty -> A := Empty_rec.

 Definition unit_const : forall A : Type, A -> Unit := fun A => const tt.

 Theorem and_map_l : forall A B C : Type, (A -> B) -> A /\ C -> B /\ C.
 Proof.
  intros A B C f [xl xr]; refine (pair (f xl) xr).
 Qed.

 Theorem and_map_r : forall A B C : Type, (A -> B) -> C /\ A -> C /\ B.
 Proof.
  intros A B C f [xl xr]; refine (pair xl (f xr)).
 Qed.

 Theorem or_map_l : forall A B C : Type, (A -> B) -> A \/ C -> B \/ C.
 Proof.
  intros A B C f [xl | xr]; [> refine (left (f xl)) | refine (right xr) ].
 Qed.

 Theorem or_map_r : forall A B C : Type, (A -> B) -> C \/ A -> C \/ B.
 Proof.
  intros A B C f [xl | xr]; [> refine (left xl) | refine (right (f xr)) ].
 Qed.

 Theorem imp_map_l : forall A B C : Type, (A -> B) -> (B -> C) -> (A -> C).
 Proof.
  intros A B C f g; refine (compose g f).
 Qed.

 Theorem imp_map_r : forall A B C : Type, (A -> B) -> (C -> A) -> (C -> B).
 Proof.
  intros A B C f g; refine (compose f g).
 Qed.

 Theorem not_map : forall A B : Type, (A -> B) -> ~ B -> ~ A.
 Proof.
  intros A B f x; refine (compose x f).
 Qed.

 Definition iff (A B : Type) : Type := (A -> B) /\ (B -> A).

 Notation "A <-> B" := (iff A B) : type_scope.

 Theorem iff_refl : forall A, A <-> A.
 Proof.
  intros A.
  refine (pair (@id _) (@id _)).
 Qed.

 Theorem iff_sym : forall A B, (A <-> B) -> (B <-> A).
 Proof.
  intros A B x.
  refine (pair (second x) (first x)).
 Qed.

 Theorem iff_trans : forall A B C, (A <-> B) -> (C <-> A) -> (C <-> B).
 Proof.
  intros A B C x y.
  apply pair.
  -
   refine (compose (first x) (first y)).
  -
   refine (compose (second y) (second x)).
 Qed.

 Theorem and_iff_map_l
     : forall A B C : Type, (A <-> B) -> (A /\ C <-> B /\ C).
 Proof.
  intros A B C [xl xr]; refine (pair (and_map_l xl) (and_map_l xr)).
 Qed.

 Theorem and_iff_map_r
     : forall A B C : Type, (A <-> B) -> (C /\ A <-> C /\ B).
 Proof.
  intros A B C [xl xr]; refine (pair (and_map_r xl) (and_map_r xr)).
 Qed.

 Theorem or_iff_map_l
     : forall A B C : Type, (A <-> B) -> (A \/ C <-> B \/ C).
 Proof.
  intros A B C [xl xr]; refine (pair (or_map_l xl) (or_map_l xr)).
 Qed.

 Theorem or_iff_map_r : forall A B C : Type, (A <-> B) -> (C \/ A <-> C \/ B).
 Proof.
  intros A B C [xl xr]; refine (pair (or_map_r xl) (or_map_r xr)).
 Qed.

 Theorem imp_iff_map_l : forall A B C : Type, (A <-> B) -> ((A -> C) <-> (B -> C)).
 Proof.
  intros A B C [xl xr]; refine (pair (imp_map_l xr) (imp_map_l xl)).
 Qed.

 Theorem imp_iff_map_r : forall A B C : Type, (A <-> B) -> ((C -> A) <-> (C -> B)).
 Proof.
  intros A B C [xl xr]; refine (pair (imp_map_r xl) (imp_map_r xr)).
 Qed.

 Theorem not_iff_map : forall A B : Type, (A <-> B) -> (~ A <-> ~B).
 Proof.
  intros A B [xl xr]; refine (pair (not_map xr) (not_map xl)).
 Qed.

 Theorem neg_false : forall A : Type, ~ A <-> (A <-> Empty).
 Proof.
  intros A.
  apply pair.
  -
   intros x.
   refine (pair x (@exfalso _)).
  -
   apply first.
 Qed.

 Theorem and_comm : forall A B : Type, A /\ B <-> B /\ A.
 Proof.
  assert (comm : forall A B, A /\ B -> B /\ A).
  -
   intros A B [xl xr]; refine (pair xr xl).
  -
   intros A B.
   apply pair.
   +
    apply comm.
   +
    apply comm.
 Qed.

 Theorem and_assoc : forall A B C : Type, (A /\ B) /\ C <-> A /\ B /\ C.
 Proof.
  intros A B C.
  apply pair.
  -
   intros [[xll xlr] xr]; refine (pair xll (pair xlr xr)).
  -
   intros [xl [xrl xrr]]; refine (pair (pair xl xrl) xrr).
 Qed.

 Theorem and_fanout : forall A B C, (A -> B) -> (A -> C) -> A -> B /\ C.
 Proof.
  intros A B C f g x; refine (pair (f x) (g x)).
 Qed.

 Theorem and_unit_l : forall A : Type, A /\ Unit <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply first.
  -
   apply and_fanout.
   +
    apply id.
   +
    apply unit_const.
 Qed.

 Theorem and_unit_r : forall A : Type, Unit /\ A <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply second.
  -
   apply and_fanout.
   +
    apply unit_const.
   +
    apply id.
 Qed.

 Theorem or_comm : forall A B : Type, (A \/ B) <-> (B \/ A).
 Proof.
  assert (comm : forall A B, A \/ B -> B \/ A).
  -
   intros A B [xl | xr]; [> refine (right xl) | refine (left xr) ].
  -
   intros A B.
   apply pair.
   +
    apply comm.
   +
    apply comm.
 Qed.

 Theorem or_assoc : forall A B C : Type, (A \/ B) \/ C <-> A \/ B \/ C.
 Proof.
  intros A B C.
  apply pair.
  -
   intros [[xll | xlr] | xr]; [>
    refine (left xll) |
    refine (right (left xlr)) |
    refine (right (right xr)) ].
  -
   intros [xl | [xrl | xrr]]; [>
    refine (left (left xl)) |
    refine (left (right xrl)) |
    refine (right xrr) ].
 Qed.

 Theorem or_fanin : forall A B C, (A -> B) -> (C -> B) -> A \/ C -> B.
 Proof.
  intros A B C f g [xl | xr]; [> refine (f xl) | refine (g xr) ].
 Qed.

 Theorem or_empty_l : forall A : Type, A \/ Empty <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply or_fanin.
   +
    apply id.
   +
    apply exfalso.
  -
   apply left.
 Qed.

 Theorem or_empty_r : forall A : Type, Empty \/ A <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply or_fanin.
   +
    apply exfalso.
   +
    apply id.
  -
   apply right.
 Qed.

 Theorem double_not : forall A : Type, A -> ~ ~ A.
 Proof.
  intros A a na.
  apply na.
  apply a.
 Qed.

 Theorem iff_double_not : forall A : Type, ~ ~ ~ A <-> ~ A.
 Proof.
  intros A.
  apply pair.
  -
   apply not_map.
   apply double_not.
  -
   apply double_not.
 Qed.

 Theorem de_morgan : forall A B, ~ (A \/ B) <-> ~ A /\ ~ B.
 Proof.
  intros A B.
  apply pair.
  -
   apply and_fanout.
   +
    apply not_map.
    apply left.
   +
    apply not_map.
    apply right.
  -
   intros [xl xr].
   refine (or_rec _ _).
   +
    apply xl.
   +
    apply xr.
 Qed.

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
     format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
   :
     type_scope.

 Scheme ex_ind := Induction for ex Sort Type.
 Scheme ex_rec := Minimality for ex Sort Type.
 Definition ex_rect := ex_ind.

 Definition all (A : Type) (P : A -> Type) : Type := forall x, P x.

 Theorem quant_de_morgan
     : forall (A : Type) (P : A -> Type), ~ (exists x, P x) <-> forall x, ~ P x.
 Proof.
  intros A P.
  apply pair.
  -
   intros H x xH.
   apply H.
   apply (ex_pair xH).
  -
   intros H [x xH].
   apply (H x).
   apply xH.
 Qed.

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
End Predicate.

(* Module Peano.
 Export Predicate.

 Inductive nat : Type :=
 | O : nat
 | S : nat -> nat
 .

 Scheme nat_ind := Induction for nat Sort Type.
 Scheme nat_rec := Minimality for nat Sort Type.
 Definition nat_rect := nat_ind.

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

Export Peano. *)

Module Relation.
 Export Predicate.

 Definition relation (A : Type) := A -> A -> Type.

 Definition mere (A : Type) (R : relation A) := forall x y : A, forall p q : R x y, p = q.

 Section Classes.
  Variable A : Type.
  Variable R : relation A.

  Class Reflexive : Type :=
    reflexivity : forall x, R x x.

  Class Irreflexive :=
    irreflexivity : forall x, ~ R x x.

  Class Symmetric :=
    symmetry : forall x y, R x y -> R y x.

  Class Asymmetric :=
    asymmetry : forall x y, R x y -> ~ R y x.

  Class Antisymmetric :=
    antisymmetry : forall x y, R x y -> R y x -> x = y.

  Class Transitive :=
    transitivity : forall x y z, R x y -> R y z -> R x z.

  Class Well_Founded :=
    well_foundness : forall P, (forall x, (forall y, R y x -> P y) -> P x) -> (forall x, P x).

  Class Trichotomous :=
    trichotomy : forall x y, x = y \/ R x y \/ R y x.

  Class Extensional :=
    extensionality : forall x y, (forall a, R a x <-> R a y) -> x = y.

  Theorem th_0 `{WF : Well_Founded} : Irreflexive.
  Proof.
   unfold Irreflexive.
   apply well_foundness.
   intros x IH H.
   apply IH with x.
   -
    apply H.
   -
    apply H.
  Qed.

  Theorem th_1 `{WF : Well_Founded} : Asymmetric.
  Proof.
   unfold Asymmetric.
   apply (@well_foundness _ (fun x => forall y, R x y -> ~ R y x)).
   intros x IH y Hl Hr.
   apply IH with y x.
   -
    apply Hr.
   -
    apply Hr.
   -
    apply Hl.
  Qed.

  Theorem th_2 `{IR : Irreflexive} `{T : Trichotomous} : Extensional.
  Proof.
   unfold Extensional.
   intros x y H.
   destruct (@trichotomy _ x y) as [both | [left | right]].
   -
    apply both.
   -
    apply exfalso.
    apply irreflexivity with x.
    apply (second (H _)).
    apply left.
   -
    apply exfalso.
    apply irreflexivity with y.
    apply (first (H _)).
    apply right.
  Qed.

  Theorem th_3 `{WF : Well_Founded} `{T : Trichotomous} : Transitive.
  Proof.
   unfold Transitive.
   intros x y z Hl Hr.
   destruct (@trichotomy _ x z) as [both | [left | right]].
   -
    apply exfalso.
    assert (AS : Asymmetric).
    +
     apply th_1.
    +
     apply asymmetry with y z.
     *
      apply Hr.
     *
      case both.
      apply Hl.
  -
   apply left.
  -
   assert (tri_loop : forall x y z, R x y -> R y z -> R z x -> Empty).
   +
    clear x y z Hl Hr right.
    apply (@well_foundness _ (fun x => forall y z, R x y -> R y z -> R z x -> Empty)).
    intros x IH y z Hx Hy Hz.
    apply IH with z x y.
    *
     apply Hz.
    *
     apply Hz.
    *
     apply Hx.
    *
     apply Hy.
   +
    apply exfalso.
    apply tri_loop with x y z.
    *
     apply Hl.
    *
     apply Hr.
    *
     apply right.
  Qed.
 End Classes.

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
