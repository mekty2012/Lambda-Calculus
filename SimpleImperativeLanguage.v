(* Simple Imperative Language *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

From PLT Require Import Maps.
From PLT Require Import IntegerExpression.
Import ListNotations.

Inductive SILang: Type :=
  | SISkip : SILang
  | SIAssn (x:string) (a:aexp) : SILang
  | SISeq (first:SILang) (second:SILang) : SILang
  | SIIf (cond:bexp) (thenE:SILang) (elseE:SILang) : SILang
  | SIWhile (cond:bexp) (body:SILang) : SILang.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive sieval : SILang -> state -> state -> Prop :=
  | SIE_Skip : forall st,
      st =[ SISkip ]=> st
  | SIE_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ SIAssn x a1 ]=> (x !-> n ; st)
  | SIE_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ SISeq c1 c2 ]=> st''
  | SIE_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ SIIf b c1 c2 ]=> st'
  | SIE_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ SIIf b c1 c2 ]=> st'
  | SIE_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ SIWhile b c ]=> st
  | SIE_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ SIWhile b c ]=> st'' ->
      st  =[ SIWhile b c ]=> st''

  where "st =[ c ]=> st'" := (sieval c st st').

Theorem sieval_deterministic :
  forall st st' st'' c,
  st =[ c ]=> st' ->
  st =[ c ]=> st'' ->
  st' = st''.
Proof.
  intros. generalize dependent st'. induction H0; intros.
  - inversion H; subst. reflexivity.
  - inversion H0; subst. reflexivity.
  - inversion H; subst.
    assert (st'1 = st').
    { apply IHsieval1. apply H2. }
    apply IHsieval2. subst. apply H5.
  - inversion H1; subst.
    + apply IHsieval. apply H8.
    + rewrite H in H7. discriminate.
  - inversion H1; subst.
    + rewrite H in H7. discriminate.
    + apply IHsieval. apply H8.
  - inversion H0; subst.
    + reflexivity.
    + rewrite H in H3. discriminate.
  - inversion H0; subst.
    + rewrite H in H5. discriminate.
    + assert (st'1 = st').
      { apply IHsieval1. apply H4. }
      apply IHsieval2. subst. apply H7.
  Qed.