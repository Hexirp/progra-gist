Require Import Coq.Init.Prelude.

Definition not_and_then : forall A B : Prop, (A -> ~ B) -> ~ (A /\ B).
Proof.
 intros A B H I.
 apply (@and_ind A B False H I).
Qed.

Definition not_then_and : forall A B : Prop, ~ (A /\ B) -> A -> ~ B.
Proof.
 intros A B H a b.
 apply H, (conj a b).
Qed.

Definition not_map : forall A B : Prop, (A -> B) -> ~ B -> ~ A.
Proof.
 intros A B H nb a.
 apply nb, H, a.
Qed.

Definition not_then_then : forall A B : Prop, (A -> ~ B) -> B -> ~ A.
Proof.
 intros A B H b a.
 apply (H a b).
Qed.

Module Type Ord.
 Parameter ord : Type.
 Parameter lt : ord -> ord -> Prop.
End Ord.

Module Ord_Defs (Export Model : Ord).
 Definition le : ord -> ord -> Prop := fun a b => lt a b \/ a = b.

 Definition le_lt : forall a b, lt a b -> le a b.
 Proof.
  intros a b H.
  apply (or_introl H).
 Qed.

 Definition le_eq : forall a b, a = b -> le a b.
 Proof.
  intros a b H.
  apply (or_intror H).
 Qed.
End Ord_Defs.

Module Type Induction (Export Model : Ord).
 Axiom ind
   : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
End Induction.

Module Induction_Defs (Model : Ord) (Export IndModel : Induction Model).
 Module Model_Ord_Defs := Ord_Defs Model.
 Export Model_Ord_Defs.

 Definition not_lt_refl : forall a, ~ lt a a.
 Proof.
  apply (ind (fun a => ~ lt a a)).
  intros a IH H.
  apply IH with a.
  -
   apply H.
  -
   apply H.
 Qed.

 Definition not_lt_sym : forall a b, lt a b -> ~ lt b a.
 Proof.
  apply (ind (fun a => forall b, lt a b -> ~ lt b a)).
  intros a IH b Ha Hb.
  apply IH with b a.
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
   apply H with (f 0) 0.
   apply eq_refl.
  -
   apply (ind (fun a => forall x, f x <> a)).
   intros a IH x H.
   apply IH with (f (S x)) (S x).
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
   apply not_lt_refl with a.
   refine (match R in _ = a' return lt a a' with eq_refl => _ end).
   apply H.
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

Definition le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
 intros m n o H0.
 revert o.
 apply le_ind.
 -
  apply H0.
 -
  intros o IH H1.
  apply le_S.
  apply H1.
Qed.

Module Nat_Ord <: Ord.
 Definition ord : Type := nat.
 Definition lt : ord -> ord -> Prop := Peano.lt.
End Nat_Ord.

Module Nat_Induction <: Induction Nat_Ord.
 Export Nat_Ord.

 Definition ind
   : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
 Proof.
  intros p f.
  (* Π x (lt x n -> p x) <~> P 0 /\ P 1 ... /\ P (n - 1) is cumulative. *)
  cut (forall n k, lt k n -> p k).
  -
   intros H a.
   apply f.
   apply H.
  -
   apply (nat_ind (fun n => forall k, lt k n -> p k)).
   +
    intros k kH.
    inversion kH.
   +
    intros n Hp k kH.
    apply f.
    intros x xH.
    apply Hp.
    apply le_trans with k.
    *
     apply xH.
    *
     apply le_S_n.
     apply kH.
 Qed.
End Nat_Induction.
