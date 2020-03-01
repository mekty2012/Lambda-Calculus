(* Arrays *)

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

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AArray (x : string) (a : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(*
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
*)

Inductive ArLang: Type :=
  | SSkip : ArLang
  | SAssn (x:string) (a:aexp) : ArLang
  | SSeq (first:ArLang) (second:ArLang) : ArLang
  | SIf (cond:bexp) (thenE:ArLang) (elseE:ArLang) : ArLang
  | SWhile (cond:bexp) (body:ArLang) : ArLang
  | SArrAssn (x : string) (a1 a2:aexp) : ArLang
  | SNewArray (x : string) (afrom ato ainit:aexp) (body:ArLang) : ArLang.

Definition state := total_map nat.
Definition arstate := total_map (list nat).
