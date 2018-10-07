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

Check eq_elim.

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

(* JMeqからeqを導く
  証明不可能で公理として追加するしかない。
  Coq.Logic.JMeq.JMeq_eqとしてライブラリに存在。 *)
Definition JMeq_eq
 (A : Type) (x y : A) (p : JMeq A x A y) : eq A x y
.
Proof.
 (* 単純に考えればJMeqの除去規則によってeq A x xからeq A x yを作りたいところだが *)
 (* JMeqの除去規則で書き換えたいyはどんな型でもいいようにしなければならない *)
 Fail refine (JMeq_elim A x (fun B b _ => eq A x b) (eq_refl A x) A x p).
 (* パターンマッチングしてみてもだめ（書き換えるところを推論させることと同じ） *)
 Fail refine (match p with JMeq_refl _ _ => eq_refl A x end).
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
 (* 単純に考えればJMeqの除去規則によってP x (JMeq_refl A x)からP y pを作りたいところだが *)
 (* JMeqの除去規則で書き換えたいyはどんな型でもいいようにしなければならない *)
 Fail refine (JMeq_elim A x (fun B b p => P b p) c y p).
 (* パターンマッチングしてみてもだめ（書き換えるところを推論させることと同じ） *)
 Fail refine (match p with JMeq_refl _ _ => c end).
Abort.

(* JMeqを使って定義されたeq
  Coq.Logic.JMeq.JMeq_homとしてライブラリに存在。 *)
Definition JMeqH (A : Type) (x y : A) := JMeq A x A y.

(* eqと違い、示せる *)
Definition JMeq_JMeqH
 (A : Type) (x y : A) (p : JMeq A x A y) : JMeqH A x y
:=
 p
.
