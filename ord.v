Require Import Coq.Init.Prelude.

Axiom ord : Type.
Axiom lt : ord -> ord -> Prop.

Axiom ind
  : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.

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

Definition not_lt_sym : forall a b, ~ (lt a b /\ lt b a).
Proof.
 apply (ind (fun a => forall b, ~ (lt a b /\ lt b a))).
 intros a IHa.
 intros b [Hl Hr].
 apply IHa with b a.
 -
  apply Hr.
 -
  split.
  +
   apply Hr.
  +
   apply Hl.
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

Section Not_not_least_element.
 Variable p : ord -> Prop.
 Variable non_empty : ~ forall x, ~ p x.

 Definition not_not_least_element
   : ~ forall a, p a -> (forall x, p x -> lt a x \/ a = x) -> False.
 Proof.
  intros not_least_element.
  apply non_empty.
  apply (ind (fun a => ~ p a)).
  intros a IH Ha.
  apply not_least_element with a.
  -
   apply Ha.
  -
   intros x.
   admit.
 Admitted.
End Not_not_least_element.
