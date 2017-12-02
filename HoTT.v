Inductive paths (A : Type) (a : A) : A -> Type :=
| idpath : paths A a a
.

Definition paths_ind' (A : Type) (P : forall a b, paths A a b -> Type)
  : (forall a, P a a (idpath A a)) -> forall a b (p : paths A a b), P a b p.
Proof.
 refine (
  fun I a b p => _
 ).
 refine (
  match p as p' in paths _ _ a' return P a a' p' with
  | idpath _ _ => _
  end
 ).
 refine (
  I _
 ).
Defined.

Print paths_ind'.