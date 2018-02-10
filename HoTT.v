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

(** ** 乗法単位元 *)

Inductive unit : Type :=
| tt : unit
.

Scheme unit_ind := Induction for unit Sort Type.
Scheme unit_rec := Minimality for unit Sort Type.
Definition unit_rect := unit_ind.

(** ** 空の型 *)

Inductive empty : Type :=
.

Scheme empty_ind := Induction for empty Sort Type.
Scheme empty_rec := Minimality for empty Sort Type.
Definition empty_rect := empty_ind.

Definition not (A : Type) : Type := A -> empty.

Definition exfalso := empty_rec.

Definition absurd : forall A B, A -> (not A) -> B.
Proof.
 intros A B H Hn.
 apply exfalso.
 apply Hn.
 apply H.
Defined.

(** ** 直積 *)
Inductive and (A B : Type) : Type :=
| prod : A -> B -> and A B
.

Scheme and_ind := Induction for and Sort Type.
Scheme and_rec := Minimality for and Sort Type.
Definition and_rect := and_ind.

(** ** 直和 *)
Inductive or (A B : Type) : Type :=
| left : A -> or A B
| right : B -> or A B
.

Scheme or_ind := Induction for or Sort Type.
Scheme or_rec := Minimality for or Sort Type.
Definition or_rect := or_ind.

(** ** 等式 *)
Inductive eq (A : Type) (a : A) : A -> Type :=
| eq_refl : eq A a a
.

Scheme eq_ind := Induction for eq Sort Type.
Scheme eq_rec := Minimality for eq Sort Type.
Definition eq_rect := eq_ind.

Definition eq_sym : forall A x y, eq A x y -> eq A y x.
Proof.
 intros A x y p.
 destruct p.
 apply eq_refl.
Defined.

Definition eq_trans : forall A x y z, eq A x y -> eq A y z -> eq A x z.
Proof.
 intros A x y z p q.
 destruct p.
 destruct q.
 apply eq_refl.
Defined.

Definition eq_stepl : forall A x y z, eq A z x -> eq A z y -> eq A x y.
Proof.
 intros A x y z p q.
 destruct p.
 destruct q.
 apply eq_refl.
Defined.

Declare Left Step eq_stepl.

Definition eq_stepr := eq_trans.

Declare Right Step eq_stepr.

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
Definition trunc : nat -> Type -> Type :=
 nat_ind (fun _ => Type -> Type)
  (fun      A => contr A)
  (fun _ IH A => forall x y, IH (eq A x y))
.

(** Aがcontrであれば、その値はどのような値でも等しい *)
Definition eq_contr : forall A, contr A -> forall x y, eq A x y.
Proof.
 intros A H x y.
 destruct H as [Hc HH].
 stepl Hc.
 -
  apply HH.
 -
  apply HH.
Defined.

(* 可縮であるAにおいて、[eq_contr]により構成された道はどのような道とも等しい *)
Definition eq_eq_contr : forall A H x y p, eq (eq A x y) (eq_contr A H x y) p.
Proof.
 intros A H x y p.
 destruct p.
 destruct H as [Hc HH]; unfold eq_contr.
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
  unfold trunc, nat_ind.
  apply contr_eq_contr.
 -
  intros np IH A H x y.
  apply IH.
  apply H.
Defined.

Definition unit_trunc : trunc O unit.
Proof.
 apply ex_intro with tt.
 intros y.
 destruct y.
 apply eq_refl.
Defined.

Definition empty_trunc : trunc (S O) empty.
Proof.
 intros x.
 destruct x.
Defined.

Definition dec (A : Type) : Type := or A (not A).

Definition not_eq_o_s : forall n, not (eq nat O (S n)).
Proof.
 intros n H.
 refine (eq_rec _ O (fun x => match x return Type with O => unit | S xp => empty end) _ (S n) _).
 -
  apply tt.
 -
  apply H.
Defined.

Definition eq_s : forall m n, eq nat m n -> eq nat (S m) (S n).
Proof.
 intros m n p.
 destruct p.
 apply eq_refl.
Defined.

Definition pred (n : nat) : nat := match n with O => O | S np => np end.

Definition eq_s_inv : forall m n, eq nat (S m) (S n) -> eq nat m n.
Proof.
 intros m n p.
 stepl (pred (S m)).
 -
  apply eq_refl.
 -
  stepr (pred (S n)).
  +
   destruct p.
   apply eq_refl.
  +
   apply eq_refl.
Defined.

Definition dec_eq_nat : forall m n, dec (eq nat m n).
Proof.
 apply (nat_ind (fun m => forall n, dec (eq nat m n))).
 -
  intros n.
  destruct n.
  +
   apply left.
   apply eq_refl.
  +
   apply right.
   apply not_eq_o_s.
 -
  intros mp IH n.
  destruct n.
  +
   apply right.
   intros p.
   apply not_eq_o_s with mp.
   apply eq_sym.
   apply p.
  +
   destruct (IH n) as [p | np].
   *
    apply left.
    apply eq_s.
    apply p.
   *
    apply right.
    intros p.
    apply np.
    apply eq_s_inv.
    apply p.
Defined.

Definition trunc_eq_nat : forall m n, trunc (S O) (eq nat m n).
Proof.
 intros m n.
 destruct (dec_eq_nat m n) as [H | nH].
 -
  destruct H.
  apply trunc_succ.
  apply ex_intro with (eq_refl nat m).
  intros p.
  admit.
 -
  intros p.
  apply exfalso.
  apply nH.
  apply p.
Admitted.

(** ** 等価性 *)

Definition fiber (A B : Type) (f : A -> B) (b : B) : Type :=
 ex A (fun a => eq B (f a) b)
.

Definition equiv (A B : Type) (f : A -> B) : Type := forall b, contr (fiber A B f b).

Definition equiv_hom (A B : Type) (f : A -> B) (g : B -> A) : Type :=
 and (forall a, eq A (g (f a)) a) (forall b, eq B (f (g b)) b)
.

Definition equiv_adj (A B : Type) (f : A -> B) (g : B -> A) : Type.
Proof.
Admitted.

Definition iso_hom (A B : Type) (f : A -> B) : Type :=
 and
  (ex (B -> A) (fun g => forall a, eq A (g (f a)) a))
  (ex (B -> A) (fun h => forall b, eq B (f (h b)) b))
.
