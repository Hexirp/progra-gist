(* -*- mode: coq; coq-prog-args: ("-nois") -*- *)

(* in Coq 8.8.0 *)

(** * Pre

事前に定義すべきもの。

第一に、表記法（演算子などの書き方）を事前に定義する。これらは実際に何を意味するか定義されてはいないが、
優先順位や結合性は定義されている。たとえば、どの小単位 (Module) に書かれているかによって
[2 + 3 + 4 * 0] が [(2 + 3) + (4 * 0)] となったり、 [((2 + 3) + 4) * 0] となったりすると読みづらい。
また、最初から [_ + _] を自然数同士の足し算と決めたりすると、整数同士の足し算と解釈したいときなどに困る。
書かれている場所によってどの解釈を選ぶかは視野 (scope) の仕組みによる。

第二に、視野 (scope) を定義する。例えば、 [(Empty + Unit)%type] という式があったとする。このとき、
百分率記号は、右側の式が解釈されるとき、その内の表記法が type という視野の中から探されることを示す。
どの表記法がどの視野に入るかは、表記法の意味を定義するときに定義できる。同じ表記法でも、視野によって意味が
異なることがある。式を読み取る何某の「視野」をイメージしてほしい。百分率記号で直接的に指定しなくとも型に
よって視野が選ばれることもある。

第三に、戦略 (tactic) を使用するための設定をする。戦略 (tactic) は一気に定義を書き上げることが出来ない
場合に有用な道具である。この部分の記述は Stack Overflow で Tej Chajed 氏に教えていただいた。感謝する。
さらに、 Coq の標準文庫 (library) の内部にある Coq.Init.Notations の記述も参考にした。

第四に、設定旗 (flag) を操作する。これら大部分は HoTT の内部にある HoTT.Basics.Overture の記述に
依ったが、暗黙引数に関する設定は独自である。 *)

Module Pre.

 (** 述語論理の記号。 *)

 Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
 Reserved Notation "x <-> y" (at level 95, no associativity).
 Reserved Notation "x /\ y" (at level 80, right associativity).
 Reserved Notation "x \/ y" (at level 85, right associativity).
 Reserved Notation "~ x" (at level 75, right associativity).

 (** 等号及び不等号、大小関係。 *)

 Reserved Notation "x = y :> T" (at level 70, y at next level, no associativity).
 Reserved Notation "x = y" (at level 70, no associativity).

 Reserved Notation "x <> y :> T"(at level 70, y at next level, no associativity).
 Reserved Notation "x <> y" (at level 70, no associativity).

 Reserved Notation "x <= y" (at level 70, no associativity).
 Reserved Notation "x < y" (at level 70, no associativity).
 Reserved Notation "x >= y" (at level 70, no associativity).
 Reserved Notation "x > y" (at level 70, no associativity).

 (** 算術演算子。 *)

 Reserved Notation "x + y" (at level 50, left associativity).
 Reserved Notation "x - y" (at level 50, left associativity).
 Reserved Notation "x * y" (at level 40, left associativity).
 Reserved Notation "x / y" (at level 40, left associativity).
 Reserved Notation "x ^ y" (at level 30, right associativity).

 Reserved Notation "- x" (at level 35, right associativity).
 Reserved Notation "/ x" (at level 35, right associativity).

 (** 視野 (scope) 。 *)

 Delimit Scope type_scope with type.
 Delimit Scope function_scope with function.
 Delimit Scope core_scope with core.

 Bind Scope type_scope with Sortclass.
 Bind Scope function_scope with Funclass.

 Open Scope core_scope.
 Open Scope function_scope.
 Open Scope type_scope.

 (** 戦略 (tactic) の設定。 *)

 Declare ML Module "ltac_plugin".

 Export Set Default Proof Mode "Classic".

 (** 設定旗 (flag) の操作。 *)

 Export Unset Bracketing Last Introduction Pattern.

 Export Set Typeclasses Strict Resolution.

 Export Unset Elimination Schemes.

 Export Set Keyed Unification.

 Export Unset Refine Instance Mode.

 Export Unset Strict Universe Declaration.

 Export Unset Universe Minimization ToSet.

 Export Set Implicit Arguments.

 Export Set Strongly Strict Implicit.

End Pre.

(** * Predicate

命題論理、述語論理についての定義。論理式はカリー・ハワード対応に従って型へ翻訳される。この小単位はそれらを
定義するものである。ただ、これらは命題 (Prop) ではなく 型 (Type) であることに注意すること。 *)

Module Predicate.

 Export Pre.

 (** ** 関数 *)

 Definition arrow (A B : Type) : Type := forall (_ : A), B.

 Notation "A -> B" := (forall (_ : A), B) : type_scope.

 (** 汎用関数 *)

 Definition id : forall A, A -> A := fun _ x => x.

 Definition const : forall A B, A -> B -> A := fun _ _ x _ => x.

 Definition compose
     : forall A B C, (A -> B) -> (C -> A) -> C -> B
     := fun _ _ _ f g x => f (g x).

 Definition flip : forall A B C, (A -> B -> C) -> B -> A -> C := fun _ _ _ f x y => f y x.

 Definition apply : forall A B, (A -> B) -> A -> B := fun _ _ f x => f x.

 (** ** Empty *)

 (** 偽、矛盾、空の型、空の空間。 *)

 Inductive Empty : Type :=
 .

 Scheme Empty_ind := Induction for Empty Sort Type.
 Scheme Empty_rec := Minimality for Empty Sort Type.
 Definition Empty_rect := @Empty_ind.

 Definition not (A : Type) : Type := A -> Empty.

 Notation "~ x" := (not x) : type_scope.

 (** ** Unit *)

 (** 真、点の空間、ユニット。 *)

 Inductive Unit : Type :=
 | tt : Unit
 .

 Scheme Unit_ind := Induction for Unit Sort Type.
 Scheme Unit_rec := Minimality for Unit Sort Type.
 Definition Unit_rect := Unit_ind.

 (** ** and *)

 (** 論理積、二つ組、対、ダブル、2-タプル、ペア。 *)

 Inductive and (A B : Type) : Type :=
 | pair : A -> B -> A /\ B
 where
   "A /\ B" := (and A B) : type_scope
 .

 Scheme and_ind := Induction for and Sort Type.
 Scheme and_rec := Minimality for and Sort Type.
 Definition and_rect := and_ind.

 Definition first : forall A B, A /\ B -> A :=
  fun _ _ x => match x with pair xL _ => xL end
 .

 Definition second : forall A B, A /\ B -> B :=
  fun _ _ x => match x with pair _ xR => xR end
 .

 (** ** or *)

 (** 論理和。 *)

 Inductive or (A B : Type) : Type :=
 | left : A -> A \/ B
 | right : B -> A \/ B
 where
   "A \/ B" := (or A B) : type_scope
 .

 Scheme or_ind := Induction for or Sort Type.
 Scheme or_rec := Minimality for or Sort Type.
 Definition or_rect := or_ind.

 (** 写像。 *)

 Theorem and_map_l : forall A B C : Type, (A -> B) -> A /\ C -> B /\ C.
 Proof.
  intros A B C f [xl xr]; refine (pair (f xl) xr).
 Defined.

 Theorem and_map_r : forall A B C : Type, (A -> B) -> C /\ A -> C /\ B.
 Proof.
  intros A B C f [xl xr]; refine (pair xl (f xr)).
 Defined.

 Theorem or_map_l : forall A B C : Type, (A -> B) -> A \/ C -> B \/ C.
 Proof.
  intros A B C f [xl | xr]; [> refine (left (f xl)) | refine (right xr) ].
 Defined.

 Theorem or_map_r : forall A B C : Type, (A -> B) -> C \/ A -> C \/ B.
 Proof.
  intros A B C f [xl | xr]; [> refine (left xl) | refine (right (f xr)) ].
 Defined.

 Theorem imp_map_l : forall A B C : Type, (A -> B) -> (B -> C) -> (A -> C).
 Proof.
  intros A B C f g; refine (compose g f).
 Defined.

 Theorem imp_map_r : forall A B C : Type, (A -> B) -> (C -> A) -> (C -> B).
 Proof.
  intros A B C f g; refine (compose f g).
 Defined.

 Theorem not_map : forall A B : Type, (A -> B) -> ~ B -> ~ A.
 Proof.
  intros A B f x; refine (compose x f).
 Defined.

 (** ** 命題論理の定理 *)

 Definition exfalso : forall A : Type, Empty -> A := Empty_rec.

 Definition unit_const : forall A : Type, A -> Unit := fun A => const tt.

 Theorem and_fanout : forall A B C, (A -> B) -> (A -> C) -> A -> B /\ C.
 Proof.
  intros A B C f g x; refine (pair (f x) (g x)).
 Defined.

 Theorem or_fanin : forall A B C, (A -> B) -> (C -> B) -> A \/ C -> B.
 Proof.
  intros A B C f g [xl | xr]; [> refine (f xl) | refine (g xr) ].
 Defined.

 Theorem double_not : forall A : Type, A -> ~ ~ A.
 Proof.
  intros A a na.
  apply na.
  apply a.
 Defined.

 (** ** iff *)

 (** 同値。 *)

 Definition iff (A B : Type) : Type := (A -> B) /\ (B -> A).

 Notation "A <-> B" := (iff A B) : type_scope.

 (** iffの基本性質 *)

 Theorem iff_refl : forall A, A <-> A.
 Proof.
  intros A.
  refine (pair (@id _) (@id _)).
 Defined.

 Theorem iff_sym : forall A B, (A <-> B) -> (B <-> A).
 Proof.
  intros A B x.
  refine (pair (second x) (first x)).
 Defined.

 Theorem iff_trans : forall A B C, (A <-> B) -> (C <-> A) -> (C <-> B).
 Proof.
  intros A B C x y.
  apply pair.
  -
   refine (compose (first x) (first y)).
  -
   refine (compose (second y) (second x)).
 Defined.

 (** 双方向の写像 *)

 Theorem and_iff_map_l : forall A B C : Type, (A <-> B) -> (A /\ C <-> B /\ C).
 Proof.
  intros A B C [xl xr]; refine (pair (and_map_l xl) (and_map_l xr)).
 Defined.

 Theorem and_iff_map_r : forall A B C : Type, (A <-> B) -> (C /\ A <-> C /\ B).
 Proof.
  intros A B C [xl xr]; refine (pair (and_map_r xl) (and_map_r xr)).
 Defined.

 Theorem or_iff_map_l : forall A B C : Type, (A <-> B) -> (A \/ C <-> B \/ C).
 Proof.
  intros A B C [xl xr]; refine (pair (or_map_l xl) (or_map_l xr)).
 Defined.

 Theorem or_iff_map_r : forall A B C : Type, (A <-> B) -> (C \/ A <-> C \/ B).
 Proof.
  intros A B C [xl xr]; refine (pair (or_map_r xl) (or_map_r xr)).
 Defined.

 Theorem imp_iff_map_l : forall A B C : Type, (A <-> B) -> ((A -> C) <-> (B -> C)).
 Proof.
  intros A B C [xl xr]; refine (pair (imp_map_l xr) (imp_map_l xl)).
 Defined.

 Theorem imp_iff_map_r : forall A B C : Type, (A <-> B) -> ((C -> A) <-> (C -> B)).
 Proof.
  intros A B C [xl xr]; refine (pair (imp_map_r xl) (imp_map_r xr)).
 Defined.

 Theorem not_iff_map : forall A B : Type, (A <-> B) -> (~ A <-> ~B).
 Proof.
  intros A B [xl xr]; refine (pair (not_map xr) (not_map xl)).
 Defined.

 (** ** 重要な同値関係 *)

 Theorem neg_false : forall A : Type, ~ A <-> (A <-> Empty).
 Proof.
  intros A.
  apply pair.
  -
   intros x.
   refine (pair x (@exfalso _)).
  -
   apply first.
 Defined.

 Theorem and_comm : forall A B : Type, A /\ B <-> B /\ A.
 Proof.
  assert (comm : forall A B, A /\ B -> B /\ A).
  -
   intros A B [xl xr]; refine (pair xr xl).
  -
   intros A B.
   apply pair.
   +
    apply comm.
   +
    apply comm.
 Defined.

 Theorem and_assoc : forall A B C : Type, (A /\ B) /\ C <-> A /\ B /\ C.
 Proof.
  intros A B C.
  apply pair.
  -
   intros [[xll xlr] xr]; refine (pair xll (pair xlr xr)).
  -
   intros [xl [xrl xrr]]; refine (pair (pair xl xrl) xrr).
 Defined.

 Theorem and_unit_l : forall A : Type, A /\ Unit <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply first.
  -
   apply and_fanout.
   +
    apply id.
   +
    apply unit_const.
 Defined.

 Theorem and_unit_r : forall A : Type, Unit /\ A <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply second.
  -
   apply and_fanout.
   +
    apply unit_const.
   +
    apply id.
 Defined.

 Theorem or_comm : forall A B : Type, (A \/ B) <-> (B \/ A).
 Proof.
  assert (comm : forall A B, A \/ B -> B \/ A).
  -
   intros A B [xl | xr]; [> refine (right xl) | refine (left xr) ].
  -
   intros A B.
   apply pair.
   +
    apply comm.
   +
    apply comm.
 Defined.

 Theorem or_assoc : forall A B C : Type, (A \/ B) \/ C <-> A \/ B \/ C.
 Proof.
  intros A B C.
  apply pair.
  -
   intros [[xll | xlr] | xr]; [>
    refine (left xll) |
    refine (right (left xlr)) |
    refine (right (right xr)) ].
  -
   intros [xl | [xrl | xrr]]; [>
    refine (left (left xl)) |
    refine (left (right xrl)) |
    refine (right xrr) ].
 Defined.

 Theorem or_empty_l : forall A : Type, A \/ Empty <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply or_fanin.
   +
    apply id.
   +
    apply exfalso.
  -
   apply left.
 Defined.

 Theorem or_empty_r : forall A : Type, Empty \/ A <-> A.
 Proof.
  intros A.
  apply pair.
  -
   apply or_fanin.
   +
    apply exfalso.
   +
    apply id.
  -
   apply right.
 Defined.

 Theorem iff_double_not : forall A : Type, ~ ~ ~ A <-> ~ A.
 Proof.
  intros A.
  apply pair.
  -
   apply not_map.
   apply double_not.
  -
   apply double_not.
 Defined.

 Theorem de_morgan : forall A B, ~ (A \/ B) <-> ~ A /\ ~ B.
 Proof.
  intros A B.
  apply pair.
  -
   apply and_fanout.
   +
    apply not_map.
    apply left.
   +
    apply not_map.
    apply right.
  -
   intros [xl xr].
   refine (or_rec _ _).
   +
    apply xl.
   +
    apply xr.
 Defined.

 (** ** 量化子 *)

 Inductive ex (A : Type) (P : A -> Type) : Type :=
 | ex_pair : forall x, P x -> ex P
 .

 Notation "'exists' x .. y , p"
   :=
     (ex (fun x => .. (ex (fun y => p)) ..))
   (
     at level 200,
     x binder,
     right associativity,
     format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
   :
     type_scope.

 Scheme ex_ind := Induction for ex Sort Type.
 Scheme ex_rec := Minimality for ex Sort Type.
 Definition ex_rect := ex_ind.

 Definition ex_proj1 : forall (A : Type) (P : A -> Type), ex P -> A.
 Proof.
  intros A P x.
  case x.
  intros x1 x2.
  apply x1.
 Defined.

 Definition ex_proj2 : forall (A : Type) (P : A -> Type) (x : ex P), P (ex_proj1 x).
 Proof.
  intros A P x.
  case x.
  intros x1 x2.
  apply x2.
 Defined.

 Definition all (A : Type) (P : A -> Type) : Type := forall x, P x.

 (** 量化子に関する重要な同値関係 *)

 Theorem quant_de_morgan
     : forall (A : Type) (P : A -> Type), ~ (exists x, P x) <-> forall x, ~ P x.
 Proof.
  intros A P.
  apply pair.
  -
   intros H x xH.
   apply H.
   apply (ex_pair xH).
  -
   intros H [x xH].
   apply (H x).
   apply xH.
 Defined.

End Predicate.

(** * Equality *)

(** 等号について。 *)

Module Equality.

 Export Predicate.

 (** ** eq *)

 Inductive eq (A : Type) (x : A) : A -> Type :=
 | eq_refl : x = x :> A
 where
   "x = y :> A" := (@eq A x y) : type_scope
 .

 Scheme eq_ind := Induction for eq Sort Type.
 Scheme eq_rec := Minimality for eq Sort Type.
 Definition eq_rect := eq_ind.

 Notation "x = y" := (x = y :> _) : type_scope.
 Notation "x <> y :> T" := (~ x = y :> T) : type_scope.
 Notation "x <> y" := (x <> y :> _) : type_scope.

 (** eqの基本性質 *)

 Definition eq_sym : forall (A : Type) (x y : A), x = y -> y = x.
 Proof.
  intros A x y p.
  case p.
  apply eq_refl.
 Defined.

 Definition eq_trans : forall (A : Type) (x y z : A), x = y -> z = x -> y = z.
 Proof.
  intros A x y z p q.
  case p.
  case q.
  apply eq_refl.
 Defined.

 (** eqの汎用関数 *)

 Definition eq_ind'
     : forall (A : Type) (P : forall a b : A, a = b -> Type),
         (forall a : A, P a a eq_refl) -> forall (a b : A) (p : a = b), P a b p.
 Proof.
  intros A P H a b p.
  case p.
  apply H.
 Defined.

 Definition eq_rec'
     : forall (A : Type) (P : A -> A -> Type),
         (forall a : A, P a a) -> forall a b : A, a = b -> P a b.
 Proof.
  intros A P H a b p.
  case p.
  apply H.
 Defined.

 Definition eq_rect' := eq_ind'.

 Definition eq_rec_r
     : forall (A : Type) (x : A) (P : A -> Type), P x -> forall (y : A), y = x -> P y.
 Proof.
  intros A x P H y p.
  revert H.
  case p.
  apply id.
 Defined.

 Definition f_equal : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
 Proof.
  intros A B f x y p.
  case p.
  apply eq_refl.
 Defined.

 Definition rew : forall (A : Type) (P : A -> Type) (x y : A), x = y -> P x -> P y.
 Proof.
  intros A P x y p.
  case p.
  apply id.
 Defined.

End Equality.

Module Path.
 Export Equality.

 Definition paths := eq.

 Definition idpath := @eq_refl.

 Definition inverse := eq_sym.

 Definition concat := fun (A : Type) (x y z : A) => flip (@eq_trans A y z x).

 Definition transport := rew.

 Definition ap := f_equal.

 (** apKN

<<
ap00 :=
  fun (f   : A -> B)                       (x   : A)                => (_ : B)
ap01 :=
  fun (f   : A -> B)                       (x y : A) (p : eq A x y) => (_ : eq B (f x) (f y))
ap10 :=
  fun (f g : A -> B) (p : eq (A -> B) f g) (x   : A)                => (_ : eq B (f x) (g x))
ap11 :=
  fun (f g : A -> B) (p : eq (A -> B) f g) (x y : A) (q : eq A x y) => (_ : eq B (f x) (g y))
>>

 *)

 Definition ap00 := apply.

 Definition ap01 := ap.

 Definition ap10 : forall (A B : Type) (f g : A -> B), f = g -> forall (x : A), f x = g x.
 Proof.
  intros A B f g p x.
  case p.
  apply idpath.
 Defined.

 Definition ap11
     : forall (A B : Type) (f g : A -> B), f = g -> forall (x y : A), x = y -> f x = g y.
 Proof.
  intros A B f g p x y q.
  case p.
  case q.
  apply idpath.
 Defined.

 Definition pw_paths (A : Type) (P : A -> Type) (f g : forall x, P x) := forall x, f x = g x.

 Definition pw_idpath : forall (A : Type) (P : A -> Type) (f : forall x, P x), pw_paths f f.
 Proof.
  intros A P f x.
  apply idpath.
 Defined.

 Definition pw_whiskerL
     : forall (A B C : Type) (f : A -> B) (g h : B -> C),
         pw_paths g h -> pw_paths (compose g f) (compose h f).
 Proof.
  intros A B C f g h p x.
  apply p.
 Defined.

 Definition pw_whiskerR
     : forall (A B C : Type) (f g : A -> B) (h : B -> C),
         pw_paths f g -> pw_paths (compose h f) (compose h g).
 Proof.
  intros A B C f g h p x.
  apply (@ap _ _ h).
  apply p.
 Defined.

 Definition pw_pw_paths
     (A : Type) (P : A -> Type) (f g : forall x, P x) (pw_p pw_q : pw_paths f g)
   := forall x, pw_p x = pw_q x.

 Definition sect (A B : Type) (s : A -> B) (r : B -> A) := pw_paths (compose r s) (@id _).

 Definition equiv (A B : Type)
     := exists (f : A -> B) (g : B -> A) (es : sect g f) (er : sect f g),
         pw_pw_paths (@pw_whiskerL _ _ _ f _ _ es) (@pw_whiskerR _ _ _ _ _ f er).

(* Module Peano.
 Export Predicate.

 Inductive nat : Type :=
 | O : nat
 | S : nat -> nat
 .

 Scheme nat_ind := Induction for nat Sort Type.
 Scheme nat_rec := Minimality for nat Sort Type.
 Definition nat_rect := nat_ind.

 Definition not_eq_O_S : forall n, O <> S n.
 Proof.
  intros n p.
  refine (
   match p in _ = x' return (match x' with O => Unit | S xp => Empty end) with
   | eq_refl _ _ => _
   end
  ).
  apply tt.
 Defined.

 Definition pred : nat -> nat :=
  fun x =>
   match x with
   | O => O
   | S xp => xp
   end
 .

 Inductive le (m : nat) : nat -> Type :=
 | le_n : le m m
 | le_S : forall n, le m n -> le m (S n)
 .

 Definition le_rect_simple : forall (m : nat) (P : nat -> Type),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P cN cS.
  apply le_rect.
  -
   apply cN.
  -
   apply cS.
 Defined.

 Definition le_ind_simple : forall (m : nat) (P : nat -> Prop),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P cN cS.
  apply le_rect.
  -
   apply cN.
  -
   apply cS.
 Defined.

 Definition le_rec_simple : forall (m : nat) (P : nat -> Set),
   P m -> (forall n, le m n -> P n -> P (S n)) -> forall n, le m n -> P n.
 Proof.
  intros m P.
  apply le_rect_simple.
 Defined.

 Definition le_0_n : forall n : nat, le O n.
 Proof.
  intros n.
  induction n as [ | n IHn ].
  -
   apply le_n.
  -
   apply le_S.
   apply IHn.
 Defined.

 Definition le_n_S : forall m n : nat, le m n -> le (S m) (S n).
 Proof.
  intros m.
  apply le_rect_simple.
  -
   apply le_n.
  -
   intros n nH H.
   apply le_S.
   apply H.
 Defined.

 Definition le_pred : forall m n : nat, le m n -> le (pred m) (pred n).
 Proof.
  intros m.
  apply le_rect_simple.
  -
   apply le_n.
  -
   intros [ | np ] nH H.
   +
    apply H.
   +
    cut (forall k, S (pred (S k)) = pred (S (S k))).
    *
     intros Lem.
     case (Lem np).
     apply le_S.
     apply H.
    *
     intros k.
     apply eq_refl.
 Defined.

 Definition le_S_n : forall m n : nat, le (S m) (S n) -> le m n.
 Proof.
  intros m n H.
  apply (le_pred (S m) (S n)).
  apply H.
 Defined.

 Definition le_trans : forall m n o, le m n -> le n o -> le m o.
 Proof.
  intros m n o H.
  revert o.
  apply le_rect_simple.
  -
   apply H.
  -
   intros o oH IH.
   apply le_S.
   apply IH.
 Defined.

 Definition lt m n := le (S m) n.

 Definition not_lt_n_0 : forall n, ~ lt n O.
 Proof.
  intros n nH.
  cut (O = O).
  -
   refine (
    match nH in le _ o' return O <> o' with
    | le_n _ => _
    | le_S _ o pH => _
    end
   ).
   +
    apply not_eq_O_S.
   +
    apply not_eq_O_S.
  -
   apply eq_refl.
 Defined.
End Peano.

Export Peano. *)

Module Relation.
 Export Predicate.

 Definition relation (A : Type) := A -> A -> Type.

 Definition mere (A : Type) (R : relation A) := forall x y : A, forall p q : R x y, p = q.

 Section Classes.
  Variable A : Type.
  Variable R : relation A.

  Class Reflexive : Type :=
    reflexivity : forall x, R x x.

  Class Irreflexive :=
    irreflexivity : forall x, ~ R x x.

  Class Symmetric :=
    symmetry : forall x y, R x y -> R y x.

  Class Asymmetric :=
    asymmetry : forall x y, R x y -> ~ R y x.

  Class Antisymmetric :=
    antisymmetry : forall x y, R x y -> R y x -> x = y.

  Class Transitive :=
    transitivity : forall x y z, R x y -> R y z -> R x z.

  Class Well_Founded :=
    well_foundness : forall P, (forall x, (forall y, R y x -> P y) -> P x) -> (forall x, P x).

  Class Trichotomous :=
    trichotomy : forall x y, x = y \/ R x y \/ R y x.

  Class Extensional :=
    extensionality : forall x y, (forall a, R a x <-> R a y) -> x = y.

  Theorem th_0 `{WF : Well_Founded} : Irreflexive.
  Proof.
   unfold Irreflexive.
   apply well_foundness.
   intros x IH H.
   apply IH with x.
   -
    apply H.
   -
    apply H.
  Defined.

  Theorem th_1 `{WF : Well_Founded} : Asymmetric.
  Proof.
   unfold Asymmetric.
   apply (@well_foundness _ (fun x => forall y, R x y -> ~ R y x)).
   intros x IH y Hl Hr.
   apply IH with y x.
   -
    apply Hr.
   -
    apply Hr.
   -
    apply Hl.
  Defined.

  Theorem th_2 `{IR : Irreflexive} `{T : Trichotomous} : Extensional.
  Proof.
   unfold Extensional.
   intros x y H.
   destruct (@trichotomy _ x y) as [both | [left | right]].
   -
    apply both.
   -
    apply exfalso.
    apply irreflexivity with x.
    apply (second (H _)).
    apply left.
   -
    apply exfalso.
    apply irreflexivity with y.
    apply (first (H _)).
    apply right.
  Defined.

  Theorem th_3 `{WF : Well_Founded} `{T : Trichotomous} : Transitive.
  Proof.
   unfold Transitive.
   intros x y z Hl Hr.
   destruct (@trichotomy _ x z) as [both | [left | right]].
   -
    apply exfalso.
    assert (AS : Asymmetric).
    +
     apply th_1.
    +
     apply asymmetry with y z.
     *
      apply Hr.
     *
      case both.
      apply Hl.
  -
   apply left.
  -
   assert (tri_loop : forall x y z, R x y -> R y z -> R z x -> Empty).
   +
    clear x y z Hl Hr right.
    apply (@well_foundness _ (fun x => forall y z, R x y -> R y z -> R z x -> Empty)).
    intros x IH y z Hx Hy Hz.
    apply IH with z x y.
    *
     apply Hz.
    *
     apply Hz.
    *
     apply Hx.
    *
     apply Hy.
   +
    apply exfalso.
    apply tri_loop with x y z.
    *
     apply Hl.
    *
     apply Hr.
    *
     apply right.
  Defined.
 End Classes.

Module Type Ord.
 Parameter ord : Type.
 Parameter lt : ord -> ord -> Type.
End Ord.

Module Ord_Defs (Export Model : Ord).
 Definition le : ord -> ord -> Type := fun a b => lt a b \/ a = b.

 Definition le_lt : forall a b, lt a b -> le a b.
 Proof.
  intros a b H.
  apply left.
  apply H.
 Defined.

 Definition le_eq : forall a b, a = b -> le a b.
 Proof.
  intros a b H.
  apply right.
  apply H.
 Defined.

 Definition le_refl : forall a, le a a.
 Proof.
  intros a.
  apply le_eq.
  apply eq_refl.
 Defined.
End Ord_Defs.

Module Type Induction (Export Model : Ord).
 Axiom ind
   : forall p : ord -> Type, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
End Induction.

Module Induction_Defs (Model : Ord) (Export IndModel : Induction Model).
 Module Model_Ord_Defs := Ord_Defs Model.
 Export Model_Ord_Defs.

 Definition not_lt_refl : forall a, ~ lt a a.
 Proof.
  apply (ind (fun a => ~ lt a a)).
  intros a IHa H.
  apply IHa with a.
  -
   apply H.
  -
   apply H.
 Defined.

 Definition not_lt_sym : forall a b, lt a b -> ~ lt b a.
 Proof.
  apply (ind (fun a => forall b, lt a b -> ~ lt b a)).
  intros a IHa b Ha Hb.
  apply IHa with b a.
  -
   apply Hb.
  -
   apply Hb.
  -
   apply Ha.
 Defined.

 Definition not_lt_sym_and : forall a b, ~ (lt a b /\ lt b a).
 Proof.
  intros a b.
  apply not_and_then.
  apply not_lt_sym.
 Defined.

 Definition not_lt_inf_dec_chain : forall f, ~ (forall n, lt (f (S n)) (f n)).
 Proof.
  intros f inf_dec_chain.
  cut (forall a x, f x <> a).
  -
   intros H.
   apply H with (f O) O.
   apply eq_refl.
  -
   apply (ind (fun a => forall x, f x <> a)).
   intros a IHa x H.
   apply IHa with (f (S x)) (S x).
   +
    case H.
    apply inf_dec_chain.
   +
    apply eq_refl.
 Defined.

 Definition not_le_lt : forall a b, lt a b -> ~ le b a.
 Proof.
  intros a b H [L | R].
  -
   apply not_lt_sym with a b.
   +
    apply H.
   +
    apply L.
  -
   revert H.
   case R.
   apply not_lt_refl.
 Defined.

 Definition not_and_lt_le : forall a b, ~ (lt a b /\ le b a).
 Proof.
  intros a b.
  apply not_and_then.
  apply not_le_lt.
 Defined.

 Definition not_lt_le : forall a b, le a b -> ~ lt b a.
 Proof.
  intros a b.
  apply not_then_then.
  apply not_le_lt.
 Defined.
End Induction_Defs.

Module Type Extensionality (Export Model : Ord).
 Axiom extension : forall a b, (forall x, lt x a <-> lt x b) -> a = b.
End Extensionality.

Module Extensionality_Defs (Model : Ord) (Export ExModel : Extensionality Model).
End Extensionality_Defs.

Module Type Transitivity (Export Model : Ord).
 Axiom transition : forall a b c, lt a b -> lt b c -> lt a c.
End Transitivity.

Module Transitivity_Defs (Model : Ord) (Export TransModel : Transitivity Model).
End Transitivity_Defs.

Module IndExTrans_Defs
  (Model : Ord)
  (Export IndModel : Induction Model)
  (Export ExModel : Extensionality Model)
  (Export TransModel : Transitivity Model).

 Module IndDefs := Induction_Defs Model IndModel.
 Export IndDefs.

 Module ExDefs := Extensionality_Defs Model ExModel.
 Export ExDefs.

 Module TransDefs := Transitivity_Defs Model TransModel.
 Export TransDefs.

 (*
  double-negation translated [forall x y, x = y \/ lt x y \/ lt y x] (Gödel–Gentzen translation)
 *)
 Definition trichotomy : forall x y, ~ (~ ~ ~ x = y /\ ~ ~ (~ ~ ~ lt x y /\ ~ ~ ~ lt y x)).
 Proof.
  intros x y H.
  case H.
  intros HL HR.
  apply HL.
  intros HL'.
  apply HR.
  intros HR'.
  case HR'.
  intros HR'L HR'R.
  apply HR'L.

Module Nat_Ord <: Ord.
 Definition ord : Type := nat.
 Definition lt : ord -> ord -> Type := lt.
End Nat_Ord.

Module Nat_Induction <: Induction Nat_Ord.
 Export Nat_Ord.

 Definition ind
   : forall p : ord -> Type, (forall a, (forall x, lt x a -> p x) -> p a) -> forall a, p a.
 Proof.
  intros p f.
  cut (forall n k, lt k n -> p k).
  -
   intros Lem a.
   apply f.
   apply Lem.
  -
   apply (nat_rect (fun n => forall k, lt k n -> p k)).
   +
    intros k kH.
    apply Empty_rect.
    apply not_lt_n_0 with k.
    apply kH.
   +
    intros n IHn k kH.
    apply f.
    intros x xH.
    apply IHn.
    apply le_trans with k.
    *
     apply xH.
    *
     apply le_S_n.
     apply kH.
 Defined.
End Nat_Induction.
