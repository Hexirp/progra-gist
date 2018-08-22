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
