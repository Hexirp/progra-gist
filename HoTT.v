Inductive paths (A : Type) (a : A) : A -> Type :=
| idpath : paths A a a
.

Definition paths_ind' A (P : forall a b, paths A a b -> Type)
  : (forall a, P a a (idpath A a)) -> forall a b (p : paths A a b), P a b p.
Proof.
 intros I a b p.
 destruct p.
 apply I.
Defined.

Definition inverse A (x y : A) (p : paths A x y) : paths A y x.
Proof.
 destruct p.
 apply idpath.
Defined.

Definition concat A (x y z : A) (p : paths A x y) (q : paths A y z) : paths A x z.
Proof.
 destruct p.
 apply q.
Defined.

Definition transport (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P x) : P y.
Proof.
 destruct p.
 apply u.
Defined.

Definition ap A B (f : A -> B) (x y : A) (p : paths A x y) : paths B (f x) (f y).
Proof.
 destruct p.
 apply idpath.
Defined.

Definition Sect A B (s : A -> B) (r : B -> A) : Type
  := forall x, paths A (r (s x)) x.

(* 普通の同型 *)
Class Qinv (A B : Type) (f : A -> B) := BuildQinv {
 qinv_inv : B -> A;
 qinvl : Sect _ _ qinv_inv f;
 qinvr : Sect _ _ f qinv_inv;
}.

(* 両側可逆性 *)
Class Isequiv (A B : Type) (f : A -> B) := BuildIsequiv {
 linv : sigT (fun g => Sect _ _ g f) ;
 rinv : sigT (fun g => Sect _ _ f g) ;
}.

(* 半随伴同値 *)
Class IsEquiv (A B : Type) (f : A -> B) := BuildIsEquiv {
 equiv_inv : B -> A;
 eisretr : Sect _ _ equiv_inv f;
 eissect : Sect _ _ f equiv_inv;
 eisadj : forall x, paths _ (eisretr (f x)) (ap _ _ f _ _ (eissect x))
}.