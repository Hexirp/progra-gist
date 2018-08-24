(* in Coq 8.8.0 -no-is *)

Unset Elimination Schemes.

Notation "x -> y" := (forall (_ : x), y)
 (at level 99, right associativity, y at level 200)
.

Inductive bool : Type :=
| false : bool
| true : bool
.

Definition bool_rec
 {P : Type} (cf : P) (ct : P) (x : bool) : P
:=
 match x with
 | false => cf
 | true => ct
 end
.

Definition bool_rect
 {P : bool -> Type} (cf : P false) (ct : P true) (x : bool) : P x
:=
 match x as x' return P x' with
 | false => cf
 | true => ct
 end
.

Definition and (x y : bool) : bool :=
 match x, y with
 | false, false => false
 | false, true => false
 | true, false => false
 | true, true => true
 end
.

Definition or (x y : bool) : bool :=
 match x, y with
 | false, false => false
 | false, true => true
 | true, false => true
 | true, true => true
 end
.

Definition not (x : bool) : bool :=
 match x with
 | false => true
 | true => false
 end
.

Inductive nat : Type :=
| O : nat
| S : nat -> nat
.

Fixpoint nat_rec
 {P : Type} (co : P) (cs : P -> P) (x : nat) : P
:=
 match x with
 | O => co
 | S xp => cs (nat_rec co cs xp)
 end
.

Fixpoint nat_rect
 {P : nat -> Type} (co : P O) (cs : forall xp, P xp -> P (S xp)) (x : nat) : P x
:=
 match x as x' return P x' with
 | O => co
 | S xp => cs xp (nat_rect co cs xp)
 end
.

Fixpoint plus (m n : nat) : nat :=
 match m with
 | O => n
 | S mp => S (plus mp n)
 end
.

Fixpoint mult (m n : nat) : nat :=
 match m with
 | O => O
 | S mp => plus n (mult mp n)
 end
.

Fixpoint power (m n : nat) : nat :=
 match n with
 | O => S O
 | S np => mult m (power m np)
 end
.

Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B
.

Arguments pair {A B} x y.

Definition prod_rec
 {A B P : Type} (cp : A -> B -> P) (x : prod A B) : P
:=
 match x with
 | pair a b => cp a b
 end
.

Definition prod_rect
 {A B : Type} {P : prod A B -> Type}
 (cp : forall (a : A) (b : B), P (pair a b)) (x : prod A B) : P x
:=
 match x as x' return P x' with
 | pair a b => cp a b
 end
.

Definition fst {A B : Type} (x : prod A B) : A :=
 match x with
 | pair a _ => a
 end
.

Definition snd {A B : Type} (x : prod A B) : B :=
 match x with
 | pair _ b => b
 end
.

Inductive sum (A B : Type) : Type :=
| left : A -> sum A B
| right : B -> sum A B
.

Arguments left {A B} x.
Arguments right {A B} x.

Definition sum_rec
 {A B P : Type} (cl : A -> P) (cr : B -> P) (x : sum A B) : P
:=
 match x with
 | left a => cl a
 | right b => cr b
 end
.

Definition sum_rect
 {A B : Type} {P : sum A B -> Type} (cl : forall a, P (left a)) (cr : forall b, P (right b)) (x : sum A B) : P x
:=
 match x with
 | left a => cl a
 | right b => cr b
 end
.
