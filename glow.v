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
 match x with
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
 match x with
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
 {A B : Type} {P : prod A B -> Type} (cp : forall a b, P (pair a b))
 (x : prod A B) : P x
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
 {A B : Type} {P : sum A B -> Type}
 (cl : forall a, P (left a)) (cr : forall b, P (right b))
 (x : sum A B) : P x
:=
 match x with
 | left a => cl a
 | right b => cr b
 end
.

Inductive Unit : Type :=
| unit : Unit
.

Definition Unit_rec
 {P : Type} (cu : P) (x : Unit) : P
:=
 match x with
 | unit => cu
 end
.

Definition Unit_rect
 {P : Unit -> Type} (cu : P unit) (x : Unit) : P x
:=
 match x with
 | unit => cu
 end
.

Inductive Empty : Type :=
.

Definition Empty_rec
 {P : Type} (x : Empty) : P
:=
 match x with
 end
.

Definition Empty_rect
 {P : Empty -> Type} (x : Empty) : P x
:=
 match x with
 end
.

Definition neg (A : Type) : Type := A -> Empty.

Definition all {A : Type} (P : A -> Type) : Type := forall x, P x.

Inductive ex {A : Type} (P : A -> Type) : Type :=
| ex_pair : forall x, P x -> ex P
.

Arguments ex_pair {A P} x _.

Definition ex_rec
 {A : Type} {B : A -> Type} {P : Type} (c : forall x, B x -> P) (x : ex B) : P
:=
 match x with
 | ex_pair x H => c x H
 end
.

Definition ex_rect
 {A : Type} {B : A -> Type} {P : ex B -> Type}
 (c : forall (x : A) (H : B x), P (ex_pair x H))
 (x : ex B) : P x
:=
 match x with
 | ex_pair x H => c x H
 end
.

Definition ex_fst {A : Type} {P : A -> Type} (x : ex P) : A :=
 match x with
 | ex_pair x _ => x
 end
.

Definition ex_snd {A : Type} {P : A -> Type} (x : ex P) : P (ex_fst x) :=
 match x with
 | ex_pair _ H => H
 end
.

Inductive paths {A : Type} (a : A) : A -> Type :=
| idpath : paths a a
.

Arguments idpath {A a} , [A] a.

Definition paths_rec
 {A : Type} {a : A} {P : A -> Type} (ci : P a)
 {a' : A} (x : paths a a') : P a'
:=
 match x with
 | idpath => ci
 end
.

Definition paths_rect
 {A : Type} {a : A} {P : forall a', paths a a' -> Type} (ci : P a idpath)
 {a' : A} (x : paths a a') : P a' x
:=
 match x with
 | idpath => ci
 end
.

Definition paths_rec_nop
 {A : Type} {P : A -> A -> Type} (ci : forall a, P a a)
 {a a' : A} (x : paths a a') : P a a'
:=
 match x with
 | idpath => ci a
 end
.

Definition paths_rect_nop
 {A : Type} (P : forall a a', paths a a' -> Type) (ci : forall a, P a a idpath)
 {a a' : A} (x : paths a a') : P a a' x
:=
 match x with
 | idpath => ci a
 end
.

Definition concat
 {A : Type} {x y z : A} (p : paths x y) (q : paths y z) : paths x z
:=
 match q with
 | idpath =>
  match p with
  | idpath => idpath
  end
 end
.

Definition inverse
 {A : Type} {x y : A} (p : paths x y) : paths y x
:=
 match p with
 | idpath => idpath
 end
.

Definition ap
 {A B : Type} (f : A -> B) {x y : A} (p : paths x y) : paths (f x) (f y)
:=
 match p with
 | idpath => idpath
 end
.

Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".

Notation "x && y" := (and x y) (at level 40, left associativity).

Notation "x || y" := (or x y) (at level 40, left associativity).

Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x * y" := (mult x y) (at level 40, left associativity).

Notation "x /\ y" := (prod x y) (at level 80, right associativity).

Notation "x \/ y" := (sum x y) (at level 85, right associativity).

Notation "~ x" := (neg x) (at level 75, right associativity).

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
 (
  at level 200,
  x binder,
  right associativity,
  format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
.

Notation "x = y :> A" := (@paths A x y)
 (at level 70, y at next level, no associativity)
.

Notation "x = y" := (x = y :> _) (at level 70, no associativity).

Notation "x @( ty )@ y" := (concat (y := ty) x y)
 (at level 20, right associativity)
.

Notation "x @ y" := (x @( _ )@ y) (at level 20, no associativity).

Ltac pull x := refine (fun x => _).
Ltac push x := revert x.

Definition plus_O_n {n : nat} : O + n = n.
Proof.
 change (O + n) with n.
 exact idpath.
Defined.

Definition plus_n_O {n : nat} : n + O = n.
Proof.
 push n.
 refine (nat_rect _ _).
 -
  change (O + O) with O.
  exact idpath.
 -
  pull np.
  pull IHnp.
  change (S np + O) with (S (np + O)).
  refine (ap _ _).
  exact IHnp.
Defined.

Definition plus_Sm_n {m n : nat} : S m + n = S (m + n).
Proof.
 change (S m + n) with (S (m + n)).
 exact idpath.
Defined.

Definition plus_m_Sn {m n : nat} : m + S n = S (m + n).
Proof.
 push n.
 push m.
 refine (nat_rect _ _).
 -
  pull n.
  change (O + S n) with (S n).
  change (O + n) with n.
  exact idpath.
 -
  pull mp.
  pull IHmp.
  pull n.
  change (S mp + S n) with (S (mp + S n)).
  refine (ap _ _).
  exact (IHmp n).
Defined.

Definition plus_comm {m n : nat} : m + n = n + m.
Proof.
 push n.
 push m.
 refine (nat_rect _ _).
 -
  pull n.
  change (O + n) with n.
  refine (inverse _).
  exact plus_n_O.
 -
  pull mp.
  pull IHmp.
  pull n.
  change (S mp + n) with (S (mp + n)).
  refine (_ @(S (n + mp))@ _).
  +
   refine (ap _ _).
   exact (IHmp n).
  +
   refine (inverse _).
   exact plus_m_Sn.
Defined.

Definition plus_assoc {m n o : nat} : (m + n) + o = m + (n + o).
Proof.
 push o.
 push n.
 push m.
 refine (nat_rect _ _).
 -
  pull n.
  pull o.
  change (O + n) with n.
  change (O + (n + o)) with (n + o).
  exact idpath.
 -
  pull mp.
  pull IHmp.
  pull n.
  pull o.
  change (S mp + n) with (S (mp + n)).
  change (S (mp + n) + o) with (S (mp + n + o)).
  change (S mp + (n + o)) with (S (mp + (n + o))).
  refine (ap _ _).
  exact (IHmp n o).
Defined.

Definition plus_accom_l {m n o : nat} : m + (n + o) = n + (m + o).
Proof.
 refine (_ @((m + n) + o)@ _ @((n + m) + o)@ _).
 -
  refine (inverse _).
  exact plus_assoc.
 -
  refine (ap (fun x => x + _) _).
  exact plus_comm.
 -
  exact plus_assoc.
Defined.

Definition mult_O_n {n : nat} : O * n = O.
Proof.
 change (O * n) with O.
 exact idpath.
Defined.

Definition mult_n_O {n : nat} : n * O = O.
Proof.
 push n.
 refine (nat_rect _ _).
 -
  change (O * O) with O.
  exact idpath.
 -
  pull np.
  pull IHnp.
  change (S np * O) with (O + np * O).
  change (O + np * O) with (np * O).
  exact IHnp.
Defined.

Definition mult_Sm_n {m n : nat} : S m * n = n + m * n.
Proof.
 change (S m * n) with (n + m * n).
 exact idpath.
Defined.

Definition mult_m_Sn {m n : nat} : m * S n = m + m * n.
Proof.
 push n.
 push m.
 refine (nat_rect _ _).
 -
  pull n.
  change (O * S n) with O.
  change (O * n) with O.
  change (O + O) with O.
  exact idpath.
 -
  pull mp.
  pull IHmp.
  pull n.
  change (S mp * S n) with (S n + mp * S n).
  change (S n + mp * S n) with (S (n + mp * S n)).
  change (S mp + S mp * n) with (S (mp + S mp * n)).
  refine (ap _ _).
  change (S mp * n) with (n + mp * n).
  refine (_ @(n + (mp + mp * n))@ _).
  +
   refine (ap _ _).
   exact (IHmp n).
  +
   exact plus_accom_l.
Defined.

Definition mult_comm {m n : nat} : m * n = n * m.
Proof.
 push n.
 push m.
 refine (nat_rect _ _).
 -
  pull n.
  change (O * n) with O.
  refine (inverse _).
  exact mult_n_O.
 -
  pull mp.
  pull IHmp.
  pull n.
  change (S mp * n) with (n + mp * n).
  refine (_ @(n + n * mp)@ _).
  +
   refine (ap _ _).
   exact (IHmp n).
  +
   refine (inverse _).
   exact mult_m_Sn.
Defined.

Definition pointwise_paths
 {A : Type} {P : A -> Type} (f g : forall x, P x) : Type
:=
 forall x, f x = g x
.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity).

Definition pointwise_concat
 {A : Type} {P : A -> Type} {f g h : forall x, P x}
 (p : f == g) (q : g == h) : f == h
.
Proof.
 change (forall x, f x = h x).
 pull x.
 refine (_ @(g x)@ _).
 -
  change (forall x, f x = g x) in p.
  exact (p x).
 -
  change (forall x, g x = h x) in q.
  exact (q x).
Defined.

Section Rel.
 Variable A : Type.
 Variable R : A -> A -> Type.

 Definition Noetherian_induction : Type :=
  forall P, (forall x, (forall y, R y x -> P y) -> P x) -> forall x, P x
 .

 Definition is_empty_set (x : A) : Type :=
  forall y, ~ R y x
 .

 Definition has_a_predecessor (x : A) : Type :=
  exists y, R y x
 .

 Definition forall_has_a_predecessor : Type :=
  forall x, has_a_predecessor x
 .

 Definition is_predecessor_function (f : A -> A) : Type :=
  forall x, R (f x) x
 .

 Definition exists_is_predecessor_function : Type :=
  exists f, is_predecessor_function f
 .

 Definition predecessor_function_fhap
  (H: forall_has_a_predecessor) : A -> A
 .
 Proof.
  pull x.
  change (forall x, has_a_predecessor x) in H.
  change (forall x, exists y, R y x) in H.
  refine (ex_fst (P := fun y => R y x) _).
  exact (H x).
 Defined.

 Definition predecessor_function_eipf
  (H : exists_is_predecessor_function) : A -> A
 .
 Proof.
  change (exists f, is_predecessor_function f) in H.
  refine (ex_fst (P := is_predecessor_function) _).
  exact H.
 Defined.

 Definition eipf_fhap
  (H : forall_has_a_predecessor) : exists_is_predecessor_function
 .
 Proof.
  change (exists f, is_predecessor_function f).
  pose (pf := predecessor_function_fhap H).
  refine (ex_pair pf _).
  change (forall x, R (pf x) x).
  pull x.
  change (R (predecessor_function_fhap H x) x).
  change (R (ex_fst (P := fun y => R y x) (H x)) x).
  change (forall x, has_a_predecessor x) in H.
  change (forall x, exists y, R y x) in H.
  exact (ex_snd (P := fun y => R y x) (H x)).
 Defined.

 Definition fhap_eipf
  (H : exists_is_predecessor_function) : forall_has_a_predecessor
 .
 Proof.
  change (forall x, has_a_predecessor x).
  pull x.
  change (exists y, R y x).
  pose (pf := predecessor_function_eipf H).
  refine (ex_pair (pf x) _).
  change (R (predecessor_function_eipf H x) x).
  change (R (ex_fst (P := is_predecessor_function) H x) x).
  change (R (ex_fst (P := fun f => forall x, R (f x) x) H x) x).
  change (exists f, forall x, R (f x) x) in H.
  exact (ex_snd (P := fun f => forall x, R (f x) x) H x).
 Defined.


 Definition Contradict_ni_fhap
  (ni : Noetherian_induction) (fhap : forall_has_a_predecessor) (x : A) : Empty
 .
 Proof.
  change (
   forall P, (forall x, (forall y, R y x -> P y) -> P x) -> forall x, P x
  ) in ni.
  refine (ni (fun _ => Empty) _ _).
  -
   clear x.
   pull x.
   pull xH.
   change (forall x, has_a_predecessor x) in fhap.
   change (forall x, exists y, R y x) in fhap.
   case (fhap x).
   exact xH.
  -
   exact x.
 Defined.
End Rel.

Definition is_empty_set
 {A : Type} (R : A -> A -> Type) : Type
:=
 forall x, ~ forall y, ~ R y x
.

Definition Kuroda's_exists_empty_set
 {A : Type} (R : A -> A -> Type) : Type
:=
 ~ ~ exists x, forall y, ~ ~ ~ R y x
.

Definition Keee_eee
 {A : Type} (R : A -> A -> Type)
 : exists_empty_set R -> Kuroda's_exists_empty_set R
.
Proof.
 pull eee.
 change (~ ~ exists x, forall y, ~ ~ ~ R y x).
 change ((~ exists x, forall y, ~ ~ ~ R y x) -> Empty).
 pull H0.
 change ((exists x : A, forall y : A, ~ ~ ~ R y x) -> Empty) in H0.
 refine (H0 _).
 push eee.
 change (exists_empty_set R) with (exists x, forall y, ~ R y x).
 refine (ex_rec _).
 pull x.
 pull xH.
 refine (ex_pair x _).
 pull y.
 change ((~ ~ R y x) -> Empty).
 pull H1.
 change (~ R y x -> Empty) in H1.
 refine (H1 _).
 exact (xH y).
Defined.

Definition exists_predecessor
 {A : Type} (R : A -> A -> Type) : Type
:=
 forall x, exists y, R y x
.

Definition Kuroda's_exists_predecessor
 {A : Type} (R : A -> A -> Type) : Type
:=
 ~ ~ forall x, ~ ~ exists y, R y x
.

Definition Keae_nKeee
 {A : Type} (R : A -> A -> Type)
 : ~ Kuroda's_exists_empty_set R -> Kuroda's_exists_predecessor R
.
Proof.
 pull nKeee.
 change (~ ~ forall x, ~ ~ exists y, R y x).
 change (~ (forall x, ~ ~ exists y, R y x) -> Empty).
 pull pKep.
 change (Kuroda's_exists_empty_set R -> Empty) in nKeee.
 refine (nKeee _).
 change (~ ~ exists x, forall y, ~ ~ ~ R y x).
 change (~ (exists x, forall y, ~ ~ ~ R y x) -> Empty).
 pull pKeee.
 change ((forall x, ~ ~ (exists y, R y x)) -> Empty) in pKep.
 refine (pKep _).
 pull ppKep_x.
 change (~ (exists y : A, R y ppKep_x) -> Empty).
 pull ppKep_xH.
 change ((exists x, forall y, ~ ~ ~ R y x) -> Empty) in pKeee.
 refine (pKeee _).
 refine (ex_pair ppKep_x _).
 pull ppKeee_x.
 change (~ ~ R ppKeee_x ppKep_x -> Empty).
 pull ppKeee_xH.
 change ((exists y, R y ppKep_x) -> Empty) in ppKep_xH.
 refine (ppKep_xH _).
 refine (ex_pair ppKeee_x _).
 admit.
Admitted.

Definition nne3_Ni
 {A : Type} (R : A -> A -> Type)
 : Noetherian_induction R -> exists_empty_set R
.
Proof.
 admit.
Admitted.

Inductive fol (U : Type) : Type -> Type :=
| fol_unit : fol U Unit
| fol_empty : fol U Empty
| fol_prod : forall A B, fol U A -> fol U B -> fol U (A /\ B)
| fol_sum : forall A B, fol U A -> fol U B -> fol U (A \/ B)
| fol_forall : forall P, (forall x : U, fol U (P x)) -> fol U (forall x, P x)
| fol_exists : forall P, (exists x : U, fol U (P x)) -> fol U (exists x, P x)
| fol_neg : forall A, fol U A -> fol U (~ A)
| fol_atom : forall A, fol U A
.

(** Gödel–Gentzen translation *)
Inductive GG : Type -> Type -> Type :=
| GG_unit
 : GG Unit Unit
| GG_empty
 : GG Empty Empty
| GG_prod
 : forall A B C D, GG A C -> GG B D -> GG (A /\ B) (C /\ D)
| GG_sum
 : forall A B C D, GG A C -> GG B D -> GG (A \/ B) (~ (~ C \/ ~ D))
| GG_forall
 : forall A P G,
  (forall x : A, GG (P x) (G x)) -> GG (forall x, P x) (forall x, G x)
| GG_exists
 : forall A P G,
  (forall x : A, GG (P x) (G x)) -> GG (exists x, P x) (~ forall x, ~ G x)
| GG_neg
 : forall A B, GG A B -> GG (~ A) (~ B)
| GG_atom
 : forall A, GG A (~ ~ A)
.

Fixpoint GG_soundness
 (A B : Type) (H : GG A B)
 : ((forall X, ~ ~ X -> X) -> A) -> B
.
Proof.
 admit.
Admitted.

Fixpoint GG_completeness
 (A B : Type) (H : GG A B)
 : B -> (forall X, ~ ~ X -> X) -> A
.
Proof.
 admit.
Admitted.
