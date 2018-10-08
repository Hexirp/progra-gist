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

(* JMeqのeqのような除去規則？
  JMeq_eqを導くので証明不可能であるとわかる。
  ライブラリにはない。 *)
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

(* UIPをJMeqを使って定義したバージョン
  証明できる。さっきやりたかったことが出来ている。 *)
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

(* UIP_reflをJMeqで定義したバージョン
  証明できる。さっきやりたかったことが出来ている。 *)
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

(* eqからJMeqを導く *)
Definition eq_JMeq
 (A : Type) (x y : A) (p : eq A x y) : JMeq A x A y
:=
 eq_elim_nodep A x (fun y' => JMeq A x A y') (JMeq_refl A x) y p
.

(* JMeq_eqを仮定して他の公理を導く *)
Section Declare_JMeq_eq.
 Variable JMeq_eq : forall A x y, JMeq A x A y -> eq A x y.

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
    eq_elim
     (eq A x x) (eq_refl A x) (fun p' _ => P p')
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

 Section Declare_JMeq_eq_JMeq.
  (* JMeq_eqを適用してeq_JMeqを適用すると元に戻る
    この仮定をさらに弱められるかどうかは分かんない *)
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

(* JMeqを使って定義されたeq
  Coq.Logic.JMeq.JMeq_homとしてライブラリに存在。 *)
Definition JMeqH (A : Type) (x y : A) := JMeq A x A y.

(* eqと違い、示せる *)
Definition JMeq_JMeqH
 (A : Type) (x y : A) (p : JMeq A x A y) : JMeqH A x y
:=
 p
.
