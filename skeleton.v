Inductive kleisli (m : Type -> Type) (a : Type) (b : Type) : Type :=
| kleisliC : (a -> m b) -> kleisli m a b.

Inductive cat (k : Type -> Type -> Type) (a : Type) (b : Type) : Type :=
| leaf : k a b -> cat k a b
| tree : forall x, k x b -> cat k a x -> cat k a b.

Inductive skeleton (t : Type -> Type) (a : Type) : Type :=
| returnS : a -> skeleton t a
| bindS : forall x, t x -> cat (kleisli (skeleton t)) x a -> skeleton t a.

Definition fmap t a b : (a -> b) -> skeleton t a -> skeleton t b.
Proof.
 intros F X.
 case X; clear X.
 -
  intros A.
  apply returnS.
  apply F.
  apply A.
 -
  intros x T C.
  apply bindS with x.
  +
   apply T.
  +
   apply tree with a.
   *
    apply kleisliC.
    intros A.
    apply returnS.
    apply F.
    apply A.
   *
    apply C.
Defined.

Definition pure t a : a -> skeleton t a := returnS t a.

Definition join t a : skeleton t (skeleton t a) -> skeleton t a.
Proof.
 intros X.
 case X; clear X.
 -
  intros A.
  apply A.
 -
  intros x T C.
  apply bindS with x.
  +
   apply T.
  + (*
   Fail apply tree with (skeleton t a).
   *
    apply kleisliC.
    apply returnS.
   *
    apply C.
*) Abort.