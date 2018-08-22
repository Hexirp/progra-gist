(* in Coq 8.8.0 -no-is *)

Notation "x -> y" := (forall (_ : x), y) (at level 99, right associativity, y at level 200).
