Local Unset Elimination Schemes.

(** * HoTTを自分で実装する *)

(** ** 汎用関数。SKIコンビネータ計算とB,C,K,Wシステムで使われるコンビネーターからとった。 *)

(** 恒等関数 *)
Definition idmap A : A -> A := fun x => x.

(** 定数関数 *)
Definition const A B : A -> B -> A := fun x _ => x.

(** 合成関数 *)
Definition compose A B C : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

(** 反転関数 *)
Definition flip A B C : (B -> A -> C) -> A -> B -> C := fun f x y => f y x.

(** 縮約関数 *)
Definition dep A B : (A -> A -> B) -> A -> B := fun f x => f x x.

(** ** 自然数 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.
Definition nat_rect := nat_ind.

(** ** 等式 *)
Inductive eq (A : Type) (a : A) : A -> Type :=
| eq_refl : eq A a a
.

Scheme eq_ind := Induction for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Type.
Definition eq_rect := eq_ind.

Definition eq_stepl : forall A x y z, eq A z x -> eq A z y -> eq A x y.
Proof.
 intros A x y z zx zy.
 destruct zx.
 destruct zy.
 apply eq_refl.
Defined.

Definition eq_eq_stepl : forall A x y (p : eq A y x),
    eq (eq A x x) (eq_stepl A x x y p p) (eq_refl A x).
Proof.
 intros A x y p.
 destruct p.
 apply eq_refl.
Defined.

(** ** 存在量化 *)
Inductive ex (A : Type) (P : A -> Type) : Type :=
| ex_intro : forall x, P x -> ex A P
.

Scheme ex_ind := Induction for ex Sort Type.
Scheme ex_rec := Minimality for ex Sort Type.
Definition ex_rect := ex_ind.

(** ** 可縮性と切り捨て *)

(** 可縮性 *)
Definition contr (A : Type) : Type := ex A (fun x => forall y, eq A x y).

(** 切り捨て *)
Fixpoint trunc (n : nat) (A : Type) : Type :=
 match n with 
 | O => contr A
 | S np => forall x y, trunc np (eq A x y)
 end
.

(** Aがcontrであれば、その値はどのような値でも等しい *)
Definition eq_contr : forall A, contr A -> forall x y, eq A x y.
Proof.
 intros A H x y.
 destruct H as [Hc HH].
 apply eq_stepl with Hc.
 -
  apply HH.
 -
  apply HH.
Defined.

(* [eq_contr]により構成された道はどのような道とも等しい *)
Definition eq_eq_contr : forall A H x y p, eq (eq A x y) (eq_contr A H x y) p.
Proof.
 intros A H x y p.
 destruct p.
 destruct H as [Hc HH].
 apply eq_eq_stepl.
Defined.

(* Aが可縮であればそのどのような道空間も可縮である *)
Definition contr_eq_contr : forall A, contr A -> forall x y, contr (eq A x y).
Proof.
 intros A H x y.
 apply ex_intro with (eq_contr A H x y).
 apply eq_eq_contr.
Defined.

(* n切り捨て可能なAはn+1切り捨て可能である *)
Definition trunc_succ : forall n A, trunc n A -> trunc (S n) A.
Proof.
 apply (nat_rect (fun n => forall A, trunc n A -> trunc (S n) A)).
 -
  intros A.
  unfold trunc.
  apply contr_eq_contr.
 -
  intros np IH A H x y.
  apply IH.
  apply H.
Defined.
