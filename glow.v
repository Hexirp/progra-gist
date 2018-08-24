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

Definition and (x : bool) (y : bool) : bool :=
 match x, y with
 | false, false => false
 | false, true => false
 | true, false => false
 | true, true => true
 end
.

Definition or (x : bool) (y : bool) : bool :=
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
 | S xp => nat_rec co cs xp
 end
.

Fixpoint nat_rect
 {P : nat -> Type} (co : P O) (cs : forall xp, P xp -> P (S xp)) (x : nat) : P x
:=
 match x as x' return P x' with
 | O => co
 | S xp => nat_rect co cs xp
 end
.
