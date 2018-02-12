(* coqide -nois *)

Local Unset Elimination Schemes.

Inductive kazu : Type :=
| I : kazu
| S : forall (_ : nat), nat
.

Class 