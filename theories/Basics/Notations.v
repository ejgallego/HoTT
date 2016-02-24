(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** These are the notations whose level and associativity are imposed by Coq *)

(** Notations for propositional connectives *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "/ x" (at level 35, right associativity).
Reserved Notation "x ^ y" (at level 30, right associativity).

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )" (at level 0).

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level than "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).

Delimit Scope type_scope with type.
Delimit Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.

(** ML Tactic Notations *)

Declare ML Module "coretactics".
Declare ML Module "extratactics".
Declare ML Module "eauto".
Declare ML Module "g_class".
(* Declare ML Module "g_eqdecide". *)
(* Declare ML Module "g_rewrite". *)
Declare ML Module "tauto".

Set Implicit Arguments.

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

(** [True] is the unit type. *)
Inductive True : Type :=
  I : True.

(** [False] is the empty type. *)
Inductive False : Type :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Type) : Type := A -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

Hint Resolve I : core.

Set Implicit Arguments.

Declare ML Module "nat_syntax_plugin".

Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Local Unset Elimination Schemes.

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Scheme option_rect := Induction for option Sort Type.

Arguments None [A].

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Scheme sum_rect := Induction for sum Sort Type.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Notation "A \/ B" := (A + B)%type (only parsing) : type_scope.
Notation or := sum (only parsing).

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme prod_rect := Induction for prod Sort Type.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (prod A B) (only parsing) : type_scope.
Notation and := prod (only parsing).
Notation conj := pair (only parsing).

Hint Resolve pair inl inr : core.

Definition prod_curry (A B C : Type) (f : A -> B -> C)
  (p : prod A B) : C := f (fst p) (snd p).

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(* Natural numbers. *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Scheme nat_rect := Induction for nat Sort Type.

(* It would be nice not to need this, but the tactic [induction] requires it when the target is in [Set], and the above definition of [nat] puts it in [Set]. *)
Scheme nat_rec := Induction for nat Sort Set.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Arguments S _.

Open Scope nat_scope. (* Originally in Peano.v *)

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity (A : Type) (a : A) : A -> Type :=
  identity_refl : identity a a.

Scheme identity_rect := Induction for identity Sort Type.

Hint Resolve identity_refl: core.

Arguments identity {A} _ _.
Arguments identity_refl {A a} , [A] a.

Arguments identity_rect [A] a P f y i.


(** Identity type *)

(*
Definition ID := forall A : Type, A -> A.
Definition id : ID := fun A x => x.
*)

Delimit Scope identity_scope with identity.

Notation "x = y :> A" := (@identity A x y)%identity : identity_scope.

Notation "x = y" := (x = y :>_)%identity : identity_scope.
Notation "x <> y  :> T" := (~ x = y :>T)%identity : identity_scope.
Notation "x <> y" := (x <> y :>_)%identity : identity_scope.

Local Open Scope identity_scope.

(** Another way of interpreting booleans as propositions *)

(* Definition is_true b := b = true. *)

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Scheme list_rect := Induction for list Sort Type.

Arguments nil [A].
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.
(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.

Ltac easy :=
  let rec use_hyp H :=
    match type of H with
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let rec do_atom :=
    solve [reflexivity | symmetry; trivial] ||
    contradiction ||
    (split; do_atom)
  with do_ccl := trivial; repeat do_intro; do_atom in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".

Tactic Notation "now" tactic(t) := t; easy.
(** Because we do not use the Coq standard library at all, we have
    to start from scratch. *)

Add Search Blacklist "_admitted" "_subproof" "Private_".

Local Open Scope identity_scope.
Local Unset Elimination Schemes.

(** [(sig A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sig2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.

Scheme sig_rect := Induction for sig Sort Type.

(** We make the parameters maximally inserted so that we can pass around [pr1] as a function and have it actually mean "first projection" in, e.g., [ap]. *)

Arguments exist {A}%type P%type _ _.
Arguments proj1_sig {A P} _ / .
Arguments proj2_sig {A P} _ / .

Inductive sig2 (A:Type) (P Q:A -> Type) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

Scheme sig2_rect := Induction for sig2 Sort Type.

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.

(** *** Notations *)

(** In standard Coq, [sig] and [sig2] are defined as "subset types" which sum over predicates [P:A->Prop], while [sigT] and [sigT2] are the [Type] variants.  Because we don't use [Prop], we combine the two versions, and make [sigT] a notation for [sig].  Note that some parts of Coq (like [Program Definition]) expect [sig] to be present. *)

Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).
Notation sigT_rect := sig_rect (only parsing).
Notation sigT_rec := sig_rect (only parsing).
Notation sigT_ind := sig_rect (only parsing).
Notation sigT2 := sig2 (only parsing).
Notation existT2 := exist2 (only parsing).
Notation sigT2_rect := sig2_rect (only parsing).
Notation sigT2_rec := sig2_rect (only parsing).
Notation sigT2_ind := sig2_rect (only parsing).

Notation  ex_intro := existT (only parsing).

Notation "{ x | P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sigT (A := A) (fun x => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sigT2 (A := A) (fun x => P) (fun x => Q)) :
  type_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (sigT2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (sigT2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(* Definition exist := existT.  (* (only parsing). *) *)
(* Definition sig := sigT.  (* (only parsing). *) *)
(* Notation sig2 := (@sigT2 _) (only parsing). *)
(* Notation exist2 := (@existT2 _) (only parsing). *)

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A  & P  & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
(* Notation "{ x & P }" := (sigT (fun x:_ => P)) : type_scope. *)
(* Notation "{ x & P  & Q }" := (sigT2 (fun x:_ => P) (fun x:A => Q)) : *)
(*   type_scope. *)

Add Printing Let sig.
Add Printing Let sig2.


(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(proj1 x)] is the first projection and [(proj2 x)] is the
    second projection, the type of which depends on the [proj1]. *)

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).


(** Various forms of the axiom of choice for specifications *)

Section Choice_lemmas.

  Variables S S' : Type.
  Variable R : S -> S' -> Type.
  Variable R' : S -> S' -> Type.
  Variables R1 R2 : S -> Type.

  Lemma Choice :
   (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.
  Proof.
    intro H.
    exists (fun z => projT1 (H z)).
    intro z; destruct (H z); assumption.
  Defined.

(*
  Lemma bool_choice :
   (forall x:S, (R1 x) + (R2 x)) ->
     {f:S -> bool & forall x:S, (f x = true) * (R1 x) + (f x = false) * R2 x}.
  Proof.
    intro H.
    exists (fun z:S => if H z then true else false).
    intro z; destruct (H z); auto.
  Defined.
*)

End Choice_lemmas.

Section Dependent_choice_lemmas.

  Variables X : Type.
  Variable R : X -> X -> Type.

  Lemma dependent_choice :
    (forall x:X, {y : _ & R x y}) ->
    forall x0, {f : nat -> X & (f O = x0) * (forall n, R (f n) (f (S n)))}.
  Proof.
    intros H x0.
    set (f:=fix f n := match n with O => x0 | S n' => projT1 (H (f n')) end).
    exists f.
    split. reflexivity.
    induction n; simpl; apply projT2.
  Defined.

End Dependent_choice_lemmas.


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)

Definition Exc := option.
Definition value := Some.
Definition error := @None.

Arguments error [A].

Definition except := False_rec. (* for compatibility with previous versions *)

Arguments except [P] _.

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Defined.

Hint Resolve existT existT2: core.


(* Compatibility with ssreflect *)

(* Notation sigS := sigT (compat "8.2"). *)
Notation existS := existT (compat "8.2").
(* Notation sigS_rect := sigT_rect (compat "8.2"). *)
(* Notation sigS_rec := sigT_rec (compat "8.2"). *)
(* Notation sigS_ind := sigT_ind (compat "8.2"). *)
Notation projS1 := projT1 (compat "8.2").
Notation projS2 := projT2 (compat "8.2").

(* Notation sigS2 := sigT2 (compat "8.2"). *)
(* Notation existS2 := existT2 (compat "8.2"). *)
(* Notation sigS2_rect := sigT2_rect (compat "8.2"). *)
(* Notation sigS2_rec := sigT2_rec (compat "8.2"). *)
(* Notation sigS2_ind := sigT2_ind (compat "8.2"). *)

Set Implicit Arguments.

(** Negation of a type in [Type] *)

Definition notT (A:Type) := A -> False.

(** Properties of [identity] *)

Section identity_is_a_congruence.

 Variables A B : Type.
 Variable f : A -> B.

 Variables x y z : A.

 Lemma identity_sym : identity x y -> identity y x.
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma identity_trans : identity x y -> identity y z -> identity x z.
 Proof.
  destruct 2; trivial.
 Defined.

 Lemma identity_congr : identity x y -> identity (f x) (f y).
 Proof.
  destruct 1; trivial.
 Defined.

 Lemma not_identity_sym : notT (identity x y) -> notT (identity y x).
 Proof.
  red; intros H H'; apply H; destruct H'; trivial.
 Qed.

 Definition f_equal (e : x = y) : f x = f y := 
   match e with identity_refl => identity_refl end.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

End identity_is_a_congruence.

Definition identity_ind_r :
  forall (A:Type) (a:A) (P:A -> Prop), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rec_r :
  forall (A:Type) (a:A) (P:A -> Set), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rect_r :
  forall (A:Type) (a:A) (P:A -> Type), P a -> forall y:A, identity y a -> P y.
 intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Hint Immediate identity_sym not_identity_sym: core v62.

(* Notation refl_id := identity_refl (compat "8.3"). *)
(* Notation sym_id := identity_sym (compat "8.3"). *)
(* Notation trans_id := identity_trans (compat "8.3"). *)
(* Notation sym_not_id := not_identity_sym (compat "8.3"). *)

Reserved Notation "f ^*" (at level 20).
