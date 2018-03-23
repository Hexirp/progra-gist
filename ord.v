Require Import Coq.Init.Prelude.

Definition not_and_then : forall A B : Prop, (A -> ~ B) -> ~ (A /\ B).
Proof.
 intros A B H I.
 apply (@and_ind A B False H I).
Qed.

Definition not_then_and : forall A B : Prop, ~ (A /\ B) -> A -> ~ B.
Proof.
 intros A B H a b.
 apply H.
 apply (conj a b).
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

Module Ord_Defs (Model : Ord).
 Export Model.

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

Module Type Induction (Model : Ord).
 Export Model.

 Axiom ind
   : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
End Induction.

Module Induction_Defs (X : Ord) (Model : Induction X).
 Export Model.

 Module X_Ord_Defs := Ord_Defs X.
 Export X_Ord_Defs.

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

 Section Not_lt_inf_dec_chain.
  Variable f : nat -> ord.
  Variable inf_dec_chain : forall n, lt (f (S n)) (f n).

  Definition not_lt_inf_dec_chain : False.
  Proof.
   apply (ind (fun a => forall n, ~ f n = a)) with (f 0) 0.
   -
    intros a IH n H.
    apply IH with (f (S n)) (S n).
    +
     case H.
     apply inf_dec_chain.
    +
     apply eq_refl.
   -
    apply eq_refl.
  Qed.
 End Not_lt_inf_dec_chain.

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

Module Nat_Ord <: Ord.
 Definition ord : Type := nat.
 Definition lt : ord -> ord -> Prop := Peano.lt.
End Nat_Ord.

Module Nat_Induction <: Induction Nat_Ord.
 Module Nat_Ord_Defs := Ord_Defs Nat_Ord.
 Export Nat_Ord_Defs.

 Definition ind
   : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
 Proof.
  intros p f.
  apply nat_ind.
  -
   apply f.
   intros x H.
   refine (
    match H in Peano.le _ y' return 0 = y' -> p x with le_n _ => _ | le_S _ y pH => _ end _
   ).
   +
    intros HH.
    apply False_ind.
    apply O_S with x.
    apply HH.
   +
    intros HH.
    apply False_ind.
    apply O_S with y.
    apply HH.
   +
    apply eq_refl.
  -
   intros n nH.
   apply f.
   intros x xH.
   refine (
    match xH in Peano.le _ y' return S n = y' -> p x with le_n _ => _ | le_S _ y pH => _ end _
   ).
   +
    intro HH.
    replace x with n.
    *
     apply nH.
    *
     apply eq_add_S.
     apply HH.
   +
    admit.
   +
    apply eq_refl.
 Admitted.
End Nat_Induction.
