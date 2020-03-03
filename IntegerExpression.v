(* Integer Expression *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

From PLT Require Import Maps.
Import ListNotations.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Definition state := total_map nat.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Fixpoint adenot (a : aexp) : (state -> nat) :=
  match a with
  | ANum n =>
    fun _ => n
  | AId x =>
    fun st => st x
  | APlus a1 a2 =>
    fun st => (adenot a1) st + (adenot a2) st
  | AMinus a1 a2 =>
    fun st => (adenot a1) st - (adenot a2) st
  | AMult a1 a2 =>
    fun st => (adenot a1) st * (adenot a2) st
  end.

Fixpoint bdenot (b : bexp) : (state -> bool) :=
  match b with
  | BTrue =>
    fun _ => true
  | BFalse =>
    fun _ => false
  | BEq a1 a2 =>
    fun st => (adenot a1) st =? (adenot a2) st
  | BLe a1 a2 =>
    fun st => (adenot a1) st <=? (adenot a2) st
  | BNot b1 =>
    fun st => negb ((bdenot b1) st)
  | BAnd b1 b2 => 
    fun st => andb ((bdenot b1) st) ((bdenot b2) st)
  end.

Inductive aexp_appears_free_in : string -> aexp -> Prop :=
  | AIdaafi (x:string) : aexp_appears_free_in x (AId x)
  | APlusaafi1 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a1) :
      aexp_appears_free_in x (APlus a1 a2)
  | APlusaafi2 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a2) :
      aexp_appears_free_in x (APlus a1 a2)
  | AMinusaafi1 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a1) :
      aexp_appears_free_in x (AMinus a1 a2)
  | AMinusaafi2 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a2) :
      aexp_appears_free_in x (AMinus a1 a2)
  | AMultaafi1 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a1) :
      aexp_appears_free_in x (AMult a1 a2)
  | AMultaafi2 (x:string) (a1:aexp) (a2:aexp) (H:aexp_appears_free_in x a2) :
      aexp_appears_free_in x (AMult a1 a2).

Hint Constructors aexp_appears_free_in.

Inductive bexp_appears_free_in : string -> bexp -> Prop :=
  | BEqbafi1 (x:string) (a1 a2:aexp) (H:aexp_appears_free_in x a1) :
      bexp_appears_free_in x (BEq a1 a2)
  | BEqbafi2 (x:string) (a1 a2:aexp) (H:aexp_appears_free_in x a2) :
      bexp_appears_free_in x (BEq a1 a2)
  | BLebafi1 (x:string) (a1 a2:aexp) (H:aexp_appears_free_in x a1) :
      bexp_appears_free_in x (BLe a1 a2)
  | BLebafi2 (x:string) (a1 a2:aexp) (H:aexp_appears_free_in x a2) :
      bexp_appears_free_in x (BLe a1 a2)
  | BNotbafi (x:string) (b1:bexp) (H:bexp_appears_free_in x b1) :
      bexp_appears_free_in x (BNot b1)
  | BAndbafi1 (x:string) (b1 b2:bexp) (H:bexp_appears_free_in x b1) :
      bexp_appears_free_in x (BAnd b1 b2)
  | BAndbafi2 (x:string) (b1 b2:bexp) (H:bexp_appears_free_in x b2) :
      bexp_appears_free_in x (BAnd b1 b2).

Hint Constructors bexp_appears_free_in.

Theorem aexp_eval_denot:
  forall a st,
  adenot a st = aeval st a.
Proof with auto.
  intros. induction a...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  Qed.

Theorem bexp_eval_denot:
  forall b st,
  bdenot b st = beval st b.
Proof with auto.
  intros. induction b...
  - simpl. rewrite aexp_eval_denot. rewrite aexp_eval_denot...
  - simpl. rewrite aexp_eval_denot. rewrite aexp_eval_denot...
  - simpl. rewrite IHb...
  - simpl. rewrite IHb1... rewrite IHb2...
  Qed.

Theorem aexp_denot_coincidence : 
  forall a st st',
  (forall x, (aexp_appears_free_in x a -> st x = st' x)) ->
  adenot a st = adenot a st'.
Proof with auto.
  intros. induction a; auto.
  - simpl...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  Qed.

Theorem aexp_eval_coincidence :
  forall a st st',
  (forall x, (aexp_appears_free_in x a -> st x = st' x)) ->
  aeval st a = aeval st' a.
Proof with auto.
  intros. induction a; auto.
  - simpl...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  - simpl. rewrite IHa1...
  Qed.

Theorem bexp_denot_coincidence : 
  forall b st st',
  (forall x, (bexp_appears_free_in x b -> st x = st' x)) ->
  bdenot b st = bdenot b st'.
Proof with auto.
  intros. induction b; auto.
  - simpl.
    replace (adenot a1 st) with (adenot a1 st').
    replace (adenot a2 st) with (adenot a2 st').
    reflexivity.
    apply aexp_denot_coincidence. intros.
    symmetry...
    apply aexp_denot_coincidence. intros.
    symmetry...
  - simpl.
    replace (adenot a1 st) with (adenot a1 st').
    replace (adenot a2 st) with (adenot a2 st').
    reflexivity.
    apply aexp_denot_coincidence. intros.
    symmetry...
    apply aexp_denot_coincidence. intros.
    symmetry...
  - simpl. rewrite IHb...
  - simpl. rewrite IHb1... rewrite IHb2...
  Qed.

Theorem bexp_eval_coincidence :
  forall b st st',
  (forall x, (bexp_appears_free_in x b -> st x = st' x)) ->
  beval st b = beval st' b.
Proof.
  intros. rewrite <- bexp_eval_denot. rewrite <- bexp_eval_denot.
  apply bexp_denot_coincidence. apply H.
  Qed.

(* TODO : add substitution and substitution lemma. *)