(* coqide -nois *)

Declare ML Module "ltac_plugin".

Require Import Coq.Init.Tactics.

Global Unset Elimination Schemes.

Module Pre.
 Delimit Scope type_scope with type.

 Open Scope type_scope.

 Notation "x -> y"
   := (forall (_ : x), y) (at level 99, right associativity, y at level 200) : type_scope.

 Tactic Notation "rf" uconstr(x) := refine x.
End Pre.

Module Function.
 Import Pre.

 Definition idmap A : A -> A := fun x => x.

 Definition const A B : A -> B -> A := fun x _ => x.

 Definition compose A B C : (B -> C) -> (A -> B) -> A -> C := fun f g x => f (g x).

 Definition flip A B C : (B -> A -> C) -> A -> B -> C := fun f x y => f y x.

 Definition dep A B : (A -> A -> B) -> A -> B := fun f x => f x x.
End Function.

Module Unit.
 Inductive unit : Type :=
 | I : unit
 .

 Scheme unit_ind := Induction for unit Sort Type.
 Scheme unit_rec := Minimality for unit Sort Type.
 Definition unit_rect := unit_ind.
End Unit.

Module Empty.
 Import Pre.

 Inductive empty : Type :=
 .

 Scheme empty_ind := Induction for empty Sort Type.
 Scheme empty_rec := Minimality for empty Sort Type.
 Definition empty_rect := empty_ind.

 Definition not (A : Type) : Type := A -> empty.

 Notation "~ x" := (not x) (at level 75, right associativity) : type_scope.

 Definition exfalso := empty_rec.

 Definition absurd A B : A -> ~ A -> B := fun H nH => exfalso B (nH H).
End Empty.

Module And.
 Import Pre.

 Inductive and (A B : Type) : Type :=
 | prod : A -> B -> and A B
 .

 Scheme and_ind := Induction for and Sort Type.
 Scheme and_rec := Minimality for and Sort Type.
 Definition and_rect := and_ind.

 Notation "x /\ y" := (and x y) (at level 80, right associativity) : type_scope.

 Definition first A B : A /\ B -> A := fun H => match H with prod _ _ Ha _ => Ha end.

 Definition second A B : A /\ B -> B := fun H => match H with prod _ _ _ Hb => Hb end.
End And.

Module Or.
 Import Pre.

 Inductive or (A B : Type) : Type :=
 | left : A -> or A B
 | right : B -> or A B
 .

 Scheme or_ind := Induction for or Sort Type.
 Scheme or_rec := Minimality for or Sort Type.
 Definition or_rect := or_ind.

 Notation "x \/ y" := (or x y) (at level 85, right associativity) : type_scope.
End Or.

Module Iff.
 Import Pre And.

 Definition iff A B := A -> B /\ B -> A.

 Notation "x <-> y" := (iff x y) (at level 95, no associativity) : type_scope.
End Iff.

Module Eq.
 Import Pre.

 Inductive eq (A : Type) (a : A) : A -> Type :=
 | eq_refl : eq A a a
 .

 Scheme eq_ind := Induction for eq Sort Type.
 Scheme eq_rec := Minimality for eq Sort Type.
 Definition eq_rect := eq_ind.

 Definition eq_sym A x y : eq A x y -> eq A y x.
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (eq_refl A x).
 Defined.

 Definition eq_trans A x y z : eq A x y -> eq A y z -> eq A x z.
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (fun q => _).
  rf (match q with eq_refl _ _ => _ end).
  rf (eq_refl A x).
 Defined.

 Definition eq_stepl A x y z : eq A z x -> eq A z y -> eq A x y.
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (fun q => _).
  rf (match q with eq_refl _ _ => _ end).
  rf (eq_refl A z).
 Defined.

 Definition eq_stepr := eq_trans.

 Definition eq_stepc A x y z w : eq A z w -> eq A z x -> eq A w y -> eq A x y.
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (eq_stepl A x y z).
 Defined.
End Eq.

Module Ex.
 Import Pre.

 Inductive ex (A : Type) (P : A -> Type) : Type :=
 | ex_intro : forall x, P x -> ex A P
 .

 Scheme ex_ind := Induction for ex Sort Type.
 Scheme ex_rec := Minimality for ex Sort Type.
 Definition ex_rect := ex_ind.
End Ex.

Module Nat.
 Import Pre.

 Inductive nat : Type :=
 | O : nat
 | S : nat -> nat
 .

 Scheme nat_ind := Induction for nat Sort Type.
 Scheme nat_rec := Minimality for nat Sort Type.
 Definition nat_rect := nat_ind.
End Nat.

Module Path.
 Import Pre Eq.

 Definition eq_eq_stepl A x y p : eq (eq A x x) (eq_stepl A x x y p p) (eq_refl A x).
 Proof.
  rf (match p with eq_refl _ _ => _ end).
  cbn.
  rf (eq_refl (eq A y y) (eq_refl A y)).
 Defined.

 Definition inverse := eq_sym.

 Definition concat := eq_trans.

 Definition transport A (P : A -> Type) x y : eq A x y -> P x -> P y.
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (fun H => H).
 Defined.

 Definition ap A B (f : A -> B) x y : eq A x y -> eq B (f x) (f y).
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (eq_refl B (f x)).
 Defined.

 Definition ap01 := ap.

 Definition apD10 A B f g : eq (forall x : A, B x) f g -> forall x, eq (B x) (f x) (g x).
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (fun x => eq_refl (B x) (f x)).
 Defined.

 Definition ap10 A B f g : eq (A -> B) f g -> forall x, eq B (f x) (g x).
 Proof.
  rf (apD10 A (fun _ => B) f g).
 Defined.

 Definition ap11 A B f g : eq (A -> B) f g -> forall x y, eq A x y -> eq B (f x) (g y).
 Proof.
  rf (fun p => _).
  rf (match p with eq_refl _ _ => _ end).
  rf (fun x y q => _).
  rf (match q with eq_refl _ _ => _ end).
  rf (eq_refl B (f x)).
 Defined.

 Definition wiskerL A x y z (p : eq A z x) (q r : eq A z y)
     : eq (eq A z y) q r -> eq (eq A x y) (eq_stepl A x y z p q) (eq_stepl A x y z p r).
 Proof.
  rf (fun s => _).
  rf (match s with eq_refl _ _ => _ end).
  rf (eq_refl (eq A x y) (eq_stepl A x y z p q)).
 Defined.

 Definition eq_pointwise A (P : A -> Type) (f g : forall x, P x) x := eq (P x) (f x) (g x).
End Path.

Module Contr.
 Import Pre Ex Eq Path.

 Definition contr (A : Type) : Type := ex A (fun x => forall y, eq A x y).

 Definition eq_contr A : contr A -> forall x y, eq A x y.
 Proof.
  rf (fun H x y => _).
  rf (match H with ex_intro _ _ Hc HH => _ end).
  rf (eq_stepl A x y Hc _ _).
  -
   rf (HH x).
  -
   rf (HH y).
 Defined.

 Definition eq_eq_contr A : forall H x y (p : eq A x y), eq (eq A x y) (eq_contr A H x y) p.
 Proof.
  rf (fun H x y p => _).
  rf (match H with ex_intro _ _ Hc HH => _ end).
  cbn.
  rf (match p with eq_refl _ _ => _ end).
  rf (eq_eq_stepl A x Hc (HH x)).
 Defined.

 Definition contr_eq_contr A : contr A -> forall x y, contr (eq A x y).
 Proof.
  rf (fun H x y => _).
  rf (ex_intro (eq A x y) (fun p => forall q, eq (eq A x y) p q) (eq_contr A H x y) _).
  rf (fun p => eq_eq_contr A H x y p).
 Defined.
End Contr.

Module Trunc.
 Export Pre Ex Nat Eq Contr.

 Definition trunc : nat -> Type -> Type :=
  nat_ind (fun _ => Type -> Type)
   (fun      A => contr A)
   (fun _ IH A => forall x y, IH (eq A x y))
 .

 Definition trunc_succ : forall n A, trunc n A -> trunc (S n) A.
 Proof.
  rf (nat_ind (fun n => forall A, trunc n A -> forall x y, trunc n (eq A x y)) _ _).
  -
   rf (fun A H x y => _).
   rf (contr_eq_contr A H x y).
  -
   rf (fun np go A H x y => _).
   rf (go (eq A x y) _).
   rf (H x y).
 Defined.

 Definition hprop_forall A : (forall x y, eq A x y) -> trunc (S O) A.
 Proof.
  rf (fun H x y => _).
  rf (contr_eq_contr A _ x y).
  rf (ex_intro A (fun x => forall y, eq A x y) x _).
  rf (H x).
 Defined.
End Trunc.

Module Truncs.
 Export Trunc.
 Import Unit Empty.

 Definition contr_unit : contr unit.
 Proof.
  rf (ex_intro unit (fun x => forall y, eq unit x y) I _).
  rf (fun u => match u with I => _ end).
  rf (eq_refl unit I).
 Defined.

 Definition trunc_unit : trunc O unit := contr_unit.

 Definition trunc_empty : trunc (S O) empty.
 Proof.
  rf (fun x y => _).
  rf (exfalso (trunc O (eq empty x y)) x).
 Defined.
End Truncs.

Module Collapse.
 Export Trunc Path.
 Import Unit Empty Or.

 Definition constant A B (f : A -> B) := forall x y, eq B (f x) (f y).

 Definition collapsable A := ex (A -> A) (fun f => constant A A f).

 Definition collapse A : collapsable A -> A -> A
     := fun H => match H with ex_intro _ _ f _ => f end.

 Definition collapse_H A : forall c x y, eq A (collapse A c x) (collapse A c y).
 Proof.
  rf (fun c x y => _).
  rf (match c with ex_intro _ _ cf cH => _ end).
  cbn.
  rf (cH x y).
 Defined.

 Definition path_collapsable A := forall x y, collapsable (eq A x y).

 Definition path_collapse A x y : path_collapsable A -> eq A x y -> eq A x y
     := fun H => collapse (eq A x y) (H x y).

 Definition path_collapse_H A x y
     : forall c p q, eq (eq A x y) (path_collapse A x y c p) (path_collapse A x y c q).
 Proof.
  rf (fun c p q => _).
  rf (collapse_H (eq A x y) (c x y) p q).
 Defined.

 Definition collapse_ansym A x y c p
     := eq_stepl A x y x (path_collapse A x x c (eq_refl A x)) (path_collapse A x y c p).

 Definition collapse_k A x y c p : eq (eq A x y) (collapse_ansym A x y c p) p.
 Proof.
  rf (match p with eq_refl _ _ => _ end).
  rf (eq_eq_stepl A x x (path_collapse A x x c (eq_refl A x))).
 Defined.

 Definition trunc_path_collapsable A : path_collapsable A -> trunc (S (S O)) A.
 Proof.
  rf (fun c x y => _).
  rf (hprop_forall (eq A x y) _).
  rf (fun p q => _).
  rf (eq_stepc (eq A x y) p q (collapse_ansym A x y c p) (collapse_ansym A x y c q) _ _ _).
  -
   rf (let p_co t p := path_collapse A x t c p in _).
   rf (wiskerL A x y x (p_co x (eq_refl A x)) (p_co y p) (p_co y q) _).
   rf (path_collapse_H A x y c p q).
  -
   rf (collapse_k A x y c p).
  -
   rf (collapse_k A x y c q).
 Defined.
End Collapse.
