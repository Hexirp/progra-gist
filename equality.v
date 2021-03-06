(* in Coq 8.8.0 with "-no-is" *)

(* 除去規則が自動的に定義されるのを止める。 *)
Unset Elimination Schemes.

(* タクティックを使う。 *)
Declare ML Module "ltac_plugin".

(* 証明の仕方を設定する。 *)
Export Set Default Proof Mode "Classic".

(* 関数型の記法 *)
Notation "x -> y" := (forall (_ : x), y)
 (at level 99, right associativity, y at level 200)
.

(* 等式を表す型
  Haskellでの(:~:)に対応する。 *)
Inductive eq (A : Type) (a : A) : A -> Type :=
| eq_refl : eq A a a
.

(* eqの除去規則 *)
Definition eq_elim
 (A : Type) (x : A) (P : forall y : A, eq A x y -> Type)
 (c : P x (eq_refl A x)) (y : A) (p : eq A x y)
 : P y p
:=
 match p as p' in eq _ _ y' return P y' p' with
 | eq_refl _ _ => c
 end
.

Definition eq_elim_nodep
 (A : Type) (x : A) (P : A -> Type)
 (c : P x) (y : A) (p : eq A x y)
 : P y
:=
 eq_elim A x (fun y' _ => P y') c y p
.

Definition eq_sym
 (A : Type) (x y : A) (p : eq A x y) : eq A y x
:=
 eq_elim_nodep A x (fun y' => eq A y' x) (eq_refl A x) y p
.

Definition eq_trans
 (A : Type) (x y z : A) (p : eq A y z) (q : eq A x y) : eq A x z
.
Proof.
 refine (
  eq_elim_nodep A y (fun z' => eq A x z') _ z p
 ).
 refine (
  eq_elim_nodep A x (fun y' => eq A x y') _ y q
 ).
 refine (
  eq_refl A x
 ).
Defined.

(* Heteroな等式を表す型
  Haskellでの(:~~:)に対応する *)
Inductive JMeq (A : Type) (a : A) : forall B : Type, B -> Type :=
| JMeq_refl : JMeq A a A a
.

(* JMeqの除去規則 *)
Definition JMeq_elim
 (A : Type) (a : A) (P : forall (B : Type) (b : B), JMeq A a B b -> Type)
 (c : P A a (JMeq_refl A a)) (B : Type) (b : B) (p : JMeq A a B b)
 : P B b p
:=
 match p as p' in JMeq _ _ B' b' return P B' b' p' with
 | JMeq_refl _ _ => c
 end
.

Definition JMeq_elim_nodep
 (A : Type) (a : A) (P : forall (B : Type), B -> Type)
 (c : P A a) (B : Type) (b : B) (p : JMeq A a B b)
 : P B b
:=
 JMeq_elim A a (fun B' b' _ => P B' b') c B b p
.

Definition JMeq_sym
 (A B : Type) (a : A) (b : B) (p : JMeq A a B b) : JMeq B b A a
:=
 JMeq_elim_nodep A a (fun B' b' => JMeq B' b' A a) (JMeq_refl A a) B b p
.

Definition JMeq_trans
 (A B C : Type) (a : A) (b : B) (c : C) (p : JMeq B b C c) (q : JMeq A a B b)
 : JMeq A a C c
.
Proof.
 refine (
  JMeq_elim_nodep B b (fun C' c' => JMeq A a C' c') _ C c p
 ).
 refine (
  JMeq_elim_nodep A a (fun B' b' => JMeq A a B' b') _ B b q
 ).
 refine (
  JMeq_refl A a
 ).
Defined.

(* JMeqからeqを導く
  証明不可能で公理として追加するしかない。
  Coq.Logic.JMeq.JMeq_eqとしてライブラリに存在。 *)
Definition JMeq_eq
 (A : Type) (x y : A) (p : JMeq A x A y) : eq A x y
.
Proof.
Abort.

(* JMeqのeqのような依存無しの除去規則 *)
Definition JMeq_elim_eqlike_nodep
 (A : Type) (x : A) (P : A -> Type)
 (c : P x) (y : A) (p : JMeq A x A y)
 : P y
.
Proof.
Abort.

(* JMeqのeqのような除去規則 *)
Definition JMeq_elim_eqlike
 (A : Type) (x : A) (P : forall y : A, JMeq A x A y -> Type)
 (c : P x (JMeq_refl A x)) (y : A) (p : JMeq A x A y)
 : P y p
.
Proof.
Abort.

(* axiom UIP (UIP axiom, the axiom of uniqueness of identity proofs)
  全てのeqは等しいという公理。
  https://ncatlab.org/nlab/show/axiom+UIP *)
Definition UIP (A : Type) (x y : A) (p q : eq A x y) : eq (eq A x y) p q.
Proof.
Abort.

(* axiom K
  https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29 *)
Definition K
 (A : Type) (x : A) (P : eq A x x -> Type)
 (c : P (eq_refl A x)) (p : eq A x x)
 : P p
.
Proof.
Abort.

(* UIPの等しい対象がeq_reflになったバージョン
  Kから簡単に導ける。
  http://adam.chlipala.net/cpdt/html/Equality.html (Heterogeneous Equality) *)
Definition UIP_refl
 (A : Type) (x : A) (p : eq A x x) : eq (eq A x x) (eq_refl A x) p
.
Proof.
Abort.

(* UIPをJMeqを使って定義したバージョン *)
Definition UIP' (A : Type) (x y : A) (p q : eq A x y) : JMeq (eq A x y) p (eq A x y) q.
Proof.
 refine (
  eq_elim
   A x (fun y' p' => JMeq (eq A x y') p' (eq A x y) q)
   _ y p
 ).
 refine (
  eq_elim
   A x (fun y' q' => JMeq (eq A x x) (eq_refl A x) (eq A x y') q')
   _ y q
 ).
 refine (
  JMeq_refl (eq A x x) (eq_refl A x)
 ).
Defined.

(* UIP_reflをJMeqで定義したバージョン *)
Definition UIP'_refl
 (A : Type) (x : A) (p : eq A x x) : JMeq (eq A x x) (eq_refl A x) (eq A x x) p
.
Proof.
 refine (
  eq_elim
   A x (fun x' p' => JMeq (eq A x x) (eq_refl A x) (eq A x x') p')
   _ x p
 ).
 refine (
  JMeq_refl (eq A x x) (eq_refl A x)
 ).
Defined.

Definition JMeq_UIP
 (A B : Type) (a : A) (b : B) (p q : JMeq A a B b) : eq (JMeq A a B b) p q
.
Proof.
Abort.

Definition JMeq_K
 (A : Type) (x : A) (P : JMeq A x A x -> Type)
 (c : P (JMeq_refl A x)) (p : JMeq A x A x)
 : P p
.
Proof.
Abort.

Definition JMeq_UIP_refl
 (A : Type) (x : A) (p : JMeq A x A x) : eq (JMeq A x A x) (JMeq_refl A x) p
.
Proof.
Abort.

Definition JMeq_UIP'
 (A B : Type) (a : A) (b : B) (p q : JMeq A a B b)
 : JMeq (JMeq A a B b) p (JMeq A a B b) q
.
Proof.
 refine (
  JMeq_elim
   A a (fun B' b' p' => JMeq (JMeq A a B' b') p' (JMeq A a B b) q)
   _ B b p
 ).
 refine (
  JMeq_elim
   A a (fun B' b' q' => JMeq (JMeq A a A a) (JMeq_refl A a) (JMeq A a B' b') q')
   _ B b q
 ).
 refine (
  JMeq_refl (JMeq A a A a) (JMeq_refl A a)
 ).
Defined.

Definition JMeq_UIP'_refl
 (A : Type) (x : A) (p : JMeq A x A x)
 : JMeq (JMeq A x A x) (JMeq_refl A x) (JMeq A x A x) p
.
Proof.
 refine (
  JMeq_elim
   A x (fun A' x' p' => JMeq (JMeq A x A x) (JMeq_refl A x) (JMeq A x A' x') p')
   _ A x p
 ).
 refine (
  JMeq_refl (JMeq A x A x) (JMeq_refl A x)
 ).
Defined.

(* eqからJMeqを導く *)
Definition eq_JMeq
 (A : Type) (x y : A) (p : eq A x y) : JMeq A x A y
:=
 eq_elim_nodep A x (fun y' => JMeq A x A y') (JMeq_refl A x) y p
.

(* JMeq_eqを仮定して他の公理を導く *)
Section Declare_JMeq_eq.
 Variable JMeq_eq : forall A x y, JMeq A x A y -> eq A x y.

 Definition JMeq_elim_eqlike_nodep_from_
  (A : Type) (x : A) (P : A -> Type)
  (c : P x) (y : A) (p : JMeq A x A y)
  : P y
 .
 Proof.
  refine (
   eq_elim_nodep A x P c y (JMeq_eq A x y p)
  ).
 Defined.

 (* 証明不可能？ *)
 Definition JMeq_elim_eqlike
  (A : Type) (x : A) (P : forall y : A, JMeq A x A y -> Type)
  (c : P x (JMeq_refl A x)) (y : A) (p : JMeq A x A y)
  : P y p
 .
 Proof.
 Abort.

 Definition UIP (A : Type) (x y : A) (p q : eq A x y) : eq (eq A x y) p q.
 Proof.
  refine (JMeq_eq (eq A x y) p q _).
  refine (UIP' A x y p q).
 Defined.

 Definition K
  (A : Type) (x : A) (P : eq A x x -> Type)
  (c : P (eq_refl A x)) (p : eq A x x)
  : P p
 .
 Proof.
   refine (
    eq_elim_nodep
     (eq A x x) (eq_refl A x) (fun p' => P p')
     c p (UIP A x x (eq_refl A x) p)
   ).
 Defined.

 Definition UIP_refl
  (A : Type) (x : A) (p : eq A x x) : eq (eq A x x) (eq_refl A x) p
 .
 Proof.
  refine (JMeq_eq (eq A x x) (eq_refl A x) p _).
  refine (UIP'_refl A x p).
 Defined.

 Definition JMeq_UIP
  (A B : Type) (a : A) (b : B) (p q : JMeq A a B b) : eq (JMeq A a B b) p q
 .
 Proof.
  refine (JMeq_eq (JMeq A a B b) p q _).
  refine (JMeq_UIP' A B a b p q).
 Defined.

 Definition JMeq_K
  (A : Type) (x : A) (P : JMeq A x A x -> Type)
  (c : P (JMeq_refl A x)) (p : JMeq A x A x)
  : P p
 .
 Proof.
  refine (
   eq_elim_nodep
    (JMeq A x A x) (JMeq_refl A x) P
    c p (JMeq_UIP A A x x (JMeq_refl A x) p)
  ).
 Defined.

 Definition JMeq_UIP_refl
  (A : Type) (x : A) (p : JMeq A x A x) : eq (JMeq A x A x) (JMeq_refl A x) p
 .
 Proof.
  refine (JMeq_eq (JMeq A x A x) (JMeq_refl A x) p _).
  refine (JMeq_UIP'_refl A x p).
 Defined.

 (* JMeq_eqがどう簡約されるか *)
 Definition reduce_JMeq_eq
  (A : Type) (x : A) : eq (eq A x x) (JMeq_eq A x x (JMeq_refl A x)) (eq_refl A x)
 .
 Proof.
  refine (eq_sym (eq A x x) (eq_refl A x) (JMeq_eq A x x (JMeq_refl A x)) _).
  refine (UIP_refl A x (JMeq_eq A x x (JMeq_refl A x))).
 Defined.

 (* JMeq_eqを適用してeq_JMeqを適用すると元に戻る
   証明不可能？ *)
 Definition JMeq_eq_JMeq
  (A : Type) (x y : A) (p : JMeq A x A y)
  : eq (JMeq A x A y) (eq_JMeq A x y (JMeq_eq A x y p)) p
 .
 Proof.
 Abort.

 Definition eq_JMeq_eq
  (A : Type) (x y : A) (p : eq A x y)
  : eq (eq A x y) (JMeq_eq A x y (eq_JMeq A x y p)) p
 .
 Proof.
  refine (
   eq_elim
    A x (fun y' p' => eq (eq A x y') (JMeq_eq A x y' (eq_JMeq A x y' p')) p')
    _ y p
  ).
  refine (
   reduce_JMeq_eq A x
  ).
 Defined.

 Section Declare_JMeq_elim_eqlike.
  Variable JMeq_elim_eqlike
   : forall A x (P : forall y, JMeq A x A y -> Type),
   P x (JMeq_refl A x) -> forall y p, P y p.

  Definition JMeq_eq_JMeq
   (A : Type) (x y : A) (p : JMeq A x A y)
   : eq (JMeq A x A y) (eq_JMeq A x y (JMeq_eq A x y p)) p
  .
  Proof.
   refine (
    JMeq_elim_eqlike
     A x (fun y' p' => eq (JMeq A x A y') (eq_JMeq A x y' (JMeq_eq A x y' p')) p')
     _ y p
   ).
   refine (
    eq_elim_nodep
     (eq A x x) (eq_refl A x)
     (fun p' => eq (JMeq A x A x) (eq_JMeq A x x p') (JMeq_refl A x))
     _ (JMeq_eq A x x (JMeq_refl A x))
     (eq_sym (eq A x x) (JMeq_eq A x x (JMeq_refl A x)) (eq_refl A x) (reduce_JMeq_eq A x))
   ).
   refine (
    eq_refl (JMeq A x A x) (JMeq_refl A x)
   ).
  Defined.
 End Declare_JMeq_elim_eqlike.

 Section Declare_JMeq_eq_JMeq.
  (* この仮定をさらに弱められるかどうかは分かんない *)
  Variable JMeq_eq_JMeq
   : forall A x y p, eq (JMeq A x A y) (eq_JMeq A x y (JMeq_eq A x y p)) p.

  Definition JMeq_elim_eqlike
   (A : Type) (x : A) (P : forall y : A, JMeq A x A y -> Type)
   (c : P x (JMeq_refl A x)) (y : A) (p : JMeq A x A y)
   : P y p
  .
  Proof.
   refine (
    eq_elim
     (JMeq A x A y) (eq_JMeq A x y (JMeq_eq A x y p)) (fun p' _ => P y p')
     _ p (JMeq_eq_JMeq A x y p)
   ).
   refine (
    eq_elim A x (fun y' p' => P y' (eq_JMeq A x y' p')) _ y (JMeq_eq A x y p)
   ).
   refine c.
  Defined.
 End Declare_JMeq_eq_JMeq.
End Declare_JMeq_eq.

(* JMeq_elim_nodep_eqlikeを仮定して他の公理を導く *)
Section Declare_JMeq_elim_nodep_eqlike.
 Variable JMeq_elim_nodep_eqlike
  : forall A x P, P x -> forall y, JMeq A x A y -> P y.

 Definition JMeq_eq_from_JMeq_elim_nodep_eqlike
  (A : Type) (x y : A) (p : JMeq A x A y) : eq A x y
 .
 Proof.
  refine (
   JMeq_elim_nodep_eqlike
    A x (fun y' => eq A x y')
    (eq_refl A x) y p
  ).
 Defined.

 (* 証明不可能？ *)
 Definition reduce_JMeq_elim_nodep_eqlike
  (A : Type) (x : A) (P : A -> Type) (c : P x)
  : eq (P x) (JMeq_elim_nodep_eqlike A x P c x (JMeq_refl A x)) c
 .
 Proof.
 Abort.
End Declare_JMeq_elim_nodep_eqlike.

(* JMeqを使って定義されたeq
  Coq.Logic.JMeq.JMeq_homとしてライブラリに存在。 *)
Definition JMeqH (A : Type) (x y : A) := JMeq A x A y.

(* eqと違い、示せる *)
Definition JMeq_JMeqH
 (A : Type) (x y : A) (p : JMeq A x A y) : JMeqH A x y
:=
 p
.

Inductive ex (A : Type) (P : A -> Type) : Type :=
| ex_pair : forall x : A, P x -> ex A P
.

Definition ex_elim
 (A : Type) (P : A -> Type) (Q : ex A P -> Type)
 (c : forall (x : A) (xH : P x), Q (ex_pair A P x xH)) (x : ex A P)
 : Q x
:=
 match x as x' return Q x' with
 | ex_pair _ _ a aH => c a aH
 end
.

Definition ex_elim_nodep
 (A : Type) (P : A -> Type) (Q : Type)
 (c : forall (x : A), P x -> Q) (x : ex A P)
 : Q
:=
 match x with
 | ex_pair _ _ a aH => c a aH
 end
.

Definition eq_elim_nopoint
 (A : Type) (P : forall (x y : A), eq A x y -> Type)
 (c : forall a : A, P a a (eq_refl A a)) (x y : A) (p : eq A x y)
 : P x y p
:=
 match p as p' in eq _ _ y' return P x y' p' with
 | eq_refl _ _ => c x
 end
.

Definition eq_elim_nopoint_nodep
 (A : Type) (P : A -> A -> Type)
 (c : forall a : A, P a a) (x y : A) (p : eq A x y)
 : P x y
:=
 match p with
 | eq_refl _ _ => c x
 end
.

(* eqを使って定義されたJMeqもどき *)
Definition eqJM
 (A : Type) (a : A) (B : Type) (b : B)
:=
 ex
  (eq Type A B)
  (fun p => (eq_elim_nopoint_nodep Type (fun A' B' => A' -> B' -> Type) eq A B p) a b)
.

(* 証明不可能？ *)
Definition eqJM_JMeq
 (A B : Type) (a : A) (b : B) (p : eqJM A a B b) : JMeq A a B b
.
Proof.
Abort.

Definition JMeq_eqJM
 (A B : Type) (a : A) (b : B) (p : JMeq A a B b) : eqJM A a B b
.
Proof.
 refine (
  JMeq_elim_nodep A a (eqJM A a) _ B b p
 ).
 refine (
  ex_pair
   (eq Type A A)
   (fun p => (eq_elim_nopoint_nodep Type (fun A' A'' => A' -> A'' -> Type) eq A A p) a a)
   (eq_refl Type A)
   _
 ).
 refine (
  eq_refl A a
 ).
Defined.

(* https://homotopytypetheory.org/2012/11/21/on-heterogeneous-equality/ *)

Definition pointed_type : Type := ex Type (fun A => A).

Definition unpointed (A : pointed_type) : Type :=
 ex_elim_nodep Type (fun A => A) Type (fun A a => A) A
.

Definition base_point (A : pointed_type) : unpointed A :=
 ex_elim Type (fun A => A) (fun A => unpointed A) (fun A a => a) A
.

Definition at_home (A : Type) (a : A) : pointed_type := ex_pair Type (fun A => A) A a.

Definition ptEq_JMeq
 (A B : pointed_type) (p : eq pointed_type A B)
 : JMeq (unpointed A) (base_point A) (unpointed B) (base_point B)
.
Proof.
 refine (
  eq_elim_nodep
   pointed_type A (fun B' => JMeq (unpointed A) (base_point A) (unpointed B') (base_point B'))
   _ B p
 ).
 refine (
  JMeq_refl (unpointed A) (base_point A)
 ).
Defined.

Definition eqPt (A : Type) (a : A) (B : Type) (b : B) :=
 eq pointed_type (at_home A a) (at_home B b)
.

Definition JMeq_eqPt
 (A B : Type) (a : A) (b : B) (p : JMeq A a B b) : eqPt A a B b
.
Proof.
 refine (
  JMeq_elim_nodep A a (fun B' b' => eqPt A a B' b') _ B b p
 ).
 refine (
  eq_refl pointed_type (at_home A a)
 ).
Defined.

Definition eqPt_JMeq
 (A B : Type) (a : A) (b : B) (p : eqPt A a B b) : JMeq A a B b
.
Proof.
 pose (pA := at_home A a).
 pose (pB := at_home B b).
 change (JMeq (unpointed pA) (base_point pA) (unpointed pB) (base_point pB)).
 refine (ptEq_JMeq pA pB p).
Defined.

(* この後さらにhequivであることがわかる　*)

Inductive JMeqE (A : Type) (a : A) : forall B : Type, B -> eq Type A B -> Type :=
| JMeqE_refl : JMeqE A a A a (eq_refl Type A)
.
