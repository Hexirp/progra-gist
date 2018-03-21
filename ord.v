Require Import Coq.Init.Prelude.

Axiom ord : Type.
Axiom lt : ord -> ord -> Prop.

Axiom ind : forall p : ord -> Prop, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.

Definition not_lt_refl : forall a, ~ lt a a.
Proof.
 apply (ind _).
 intros a IH H.
 apply IH with a.
 -
  apply H.
 -
  apply H.
Qed.
