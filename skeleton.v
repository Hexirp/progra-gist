Require Import Init.

Inductive skeleta (t : Type -> Type) (a : Type) : Type :=
| returns : a -> skeleta t a
| binds : forall x, t x -> (x -> skeleta t a) -> skeleta t a.

Fixpoint fmap t a b (f : a -> b) (x : skeleta t a) : skeleta t b :=
 match x with
 | returns _ _ xr => returns _ _ (f xr)
 | binds _ _ xt xv xf => binds _ _ xt xv (fun x => fmap _ _ _ f (xf x))
 end
.
