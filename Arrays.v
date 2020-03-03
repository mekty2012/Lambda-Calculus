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

Definition state := total_map nat.
Definition arstate := total_map (nat -> nat).

Fixpoint aeval (st : state) (arst : arstate) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st arst a1) + (aeval st arst a2)
  | AMinus a1 a2  => (aeval st arst a1) - (aeval st arst a2)
  | AMult a1 a2 => (aeval st arst a1) * (aeval st arst a2)
  | AArray x a1 => (arst x) (aeval st arst a1)
  end.

Fixpoint beval (st : state) (arst : arstate) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st arst a1) =? (aeval st arst a2)
  | BLe a1 a2   => (aeval st arst a1) <=? (aeval st arst a2)
  | BNot b1     => negb (beval st arst b1)
  | BAnd b1 b2  => andb (beval st arst b1) (beval st arst b2)
  end.

Inductive ArLang: Type :=
  | ArSkip : ArLang
  | ArAssn (x:string) (a:aexp) : ArLang
  | ArSeq (first:ArLang) (second:ArLang) : ArLang
  | ArIf (cond:bexp) (thenE:ArLang) (elseE:ArLang) : ArLang
  | ArWhile (cond:bexp) (body:ArLang) : ArLang
  | ArArrAssn (x : string) (a1 a2:aexp) : ArLang
  | ArNewArray (x : string) (afrom ato ainit:aexp) (body:ArLang) : ArLang.

Definition new_array (n1 n2 n3: nat) : (nat -> nat) :=
  fun (t:nat) => 
  if (andb (t <=? n2) (n1 <=? n1)) then n3
  else 0.

Definition n_update (n1 n2:nat) (m:(nat -> nat)) : (nat -> nat) :=
  fun t => if (t =? n1) then n2 else (m t).

Inductive areval : ArLang -> state -> arstate -> state -> arstate -> Prop :=
  | ArE_Skip :    forall st arst,
      areval ArSkip st arst st arst
  | ArE_Ass : forall st a1 n x arst,
      aeval st arst a1 = n ->
      areval (ArAssn x a1) st arst (x !-> n ; st) arst
  | ArE_Seq : forall c1 c2 st st' st'' arst arst' arst'',
      areval c1 st arst st' arst' ->
      areval c2 st' arst' st'' arst'' ->
      areval (ArSeq c1 c2) st arst st'' arst''
  | ArE_IfTrue : forall st st' b c1 c2 arst arst',
      beval st arst b = true ->
      areval c1 st arst st' arst' ->
      areval (ArIf b c1 c2) st arst st' arst'
  | ArE_IfFalse : forall st st' b c1 c2 arst arst',
      beval st arst b = false ->
      areval c2 st arst st' arst' ->
      areval (ArIf b c1 c2) st arst st' arst'
  | ArE_WhileFalse : forall b st c arst,
      beval st arst b = false ->
      areval (ArWhile b c) st arst st arst
  | ArE_WhileTrue : forall st st' st'' b c arst arst' arst'',
      beval st arst b = true ->
      areval c st arst st' arst' ->
      areval (ArWhile b c) st' arst' st'' arst'' ->
      areval (ArWhile b c) st arst st'' arst''
  | ArE_ArrAssn : forall st arst x a1 a2 n1 n2,
      aeval st arst a1 = n1 ->
      aeval st arst a2 = n2 ->
      areval (ArArrAssn x a1 a2) st arst st (x !-> (n_update n1 n2 (arst x)); arst)
  | ArE_NewArray : forall st st' arst arst' x a1 a2 a3 c1 n1 n2 n3,
      aeval st arst a1 = n1 ->
      aeval st arst a2 = n2 ->
      aeval st arst a3 = n3 ->
      areval c1 st (x !-> (new_array n1 n2 n3); arst) st' arst' ->
      areval (ArNewArray x a1 a2 a3 c1) st arst st' arst'.

Notation "st '/' arst '=[' c ']=>' st2 '/' arst2" := (areval c st arst st2 arst2)
  (at level 40).

