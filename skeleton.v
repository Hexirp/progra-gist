Definition kleisli (t : Type -> Type) : Type -> Type -> Type := fun a b => a -> t b.

Section skeleton.
 Variable composed : (Type -> Type -> Type) -> Type -> Type -> Type.
 Variable leaf : forall k a b, k a b -> composed k a b.
 Variable tree : forall k a b x, k x b -> composed k a x -> composed k a b.
 Variable match_composed
     : forall k a b r, (k a b -> r) -> (forall x, k x b -> composed k a x -> r)
     -> composed k a b -> r.

 Variable skeleta : (Type -> Type) -> Type -> Type.
 Variable returns : forall t a, a -> skeleta t a.
 Variable binds : forall t a x, composed (kleisli (skeleta t)) x a -> t x -> skeleta t a.
 Variable match_skeleta
     : forall t a r, (a -> r) -> (forall x, composed (kleisli (skeleta t)) x a -> t x -> r)
     -> skeleta t a -> r.

 Definition skeleta_map (t : Type -> Type) (a : Type) (b : Type) (f : a -> b) (x : skeleta t a)
     : skeleta t b :=
 match_skeleta _ _ _
  (fun xp => returns _ _ (f xp))
  (fun xt xc xv => _)
 x.