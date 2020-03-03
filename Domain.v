(**
    This file is implementation of 
    Some Domain Theory and Denotational Semantics in Coq, Nick Benton et al.
    My purpose is to develop this approach to create denotational semantics here.
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

Import ListNotations.

Record ord:= mk_ord 
  { tord :> Type;
    Ole : tord -> tord -> Prop;
    Ole_refl : forall x : tord, Ole x x;
    Ole_trans : forall x y z : tord, Ole x y -> Ole y z -> Ole x z}.

Definition Oeq (O : ord) (x y : O) := (Ole O x y) /\ (Ole O y x).

Definition monotonic (O1 O2 : ord) (f : O1 -> O2) :=
  forall x y, (Ole O1 x y) -> (Ole O2 (f x) (f y)).

Record fmono (O1 O2 : ord) := mk_fmono
  { fmonot :> O1 -> O2;
    fmonotonic: monotonic O1 O2 fmonot}.

Lemma le_trans : 
  forall x y z, le x y -> le y z -> le x z.
Proof.
  intros. induction H.
  - apply H0.
  - apply IHle. apply le_S_n. apply le_S. apply H0.
  Qed.

Definition natO : ord := mk_ord nat le le_n le_trans.

Definition fle (O1 O2 : ord) (f1 f2 : fmono O1 O2) :=
  forall t, Ole O2 (f1 t) (f2 t).

Lemma fle_refl (O1 O2 : ord) :
  forall f, fle O1 O2 f f.
Proof.
  intros. unfold fle. intros. apply (Ole_refl O2). Qed.

Lemma fle_trans (O1 O2 : ord) :
  forall f1 f2 f3, fle O1 O2 f1 f2 -> fle O1 O2 f2 f3 -> fle O1 O2 f1 f3.
Proof.
  unfold fle. intros. eapply (Ole_trans O2).
  apply H. apply H0. Qed.

Definition mono_fun_ord (O1 O2 : ord) : ord :=
  mk_ord
  (fmono O1 O2)
  (fle O1 O2)
  (fle_refl O1 O2)
  (fle_trans O1 O2).

Record cpo := mk_cpo {
  tcpo :> ord;
  lubp: (fmono natO tcpo) -> tcpo;
  le_lub : forall (c : fmono natO tcpo) (n : nat), 
    (Ole tcpo) (c n) (lubp c);
  lub_le : forall (c : fmono natO tcpo) (x : tcpo),
    (forall n, (Ole tcpo) (c n) x) -> (Ole tcpo) (lubp c) x
  }.

Lemma monotonic_compose (D1 D2 : ord) (f : fmono D1 D2) (c : fmono natO D1) :
  monotonic natO D2 (fun (n:natO) => f (c n)).
Proof.
  unfold monotonic. intros.
  apply (fmonotonic D1 D2 f).
  apply (fmonotonic natO D1 c).
  apply H.
  Qed.

Definition fmono_compose (D1 D2:ord) (f:fmono D1 D2) (c : fmono natO D1) : fmono natO D2 :=
  mk_fmono natO D2
  (fun (n:natO) => f (c n))
  (monotonic_compose D1 D2 f c)
  .

Definition continuous (D1 D2:cpo) (f:fmono D1 D2) :=
  forall (c : fmono natO D1), (Ole D2) (f (lubp D1 c)) (lubp D2 (fmono_compose D1 D2 f c)).

Record fconti (D1 D2 : cpo) := mk_fconti
  { fcontit : fmono D1 D2;
    fcontinuous : continuous D1 D2 fcontit}.

Definition cle (D1 D2 : cpo) (f1 f2 : fconti D1 D2) : Prop :=
  forall t, Ole D2 ((fmonot D1 D2 (fcontit D1 D2 f1)) t) ((fmonot D1 D2 (fcontit D1 D2 f2)) t).

Lemma cle_refl (D1 D2 : cpo) (f : fconti D1 D2) :
  cle D1 D2 f f.
Proof.
  unfold cle. intros. apply (Ole_refl D2). Qed.

Lemma cle_trans (D1 D2 : cpo) (f1 f2 f3 : fconti D1 D2) :
  cle D1 D2 f1 f2 -> cle D1 D2 f2 f3 -> cle D1 D2 f1 f3.
Proof.
  unfold cle. intros. eapply (Ole_trans D2). apply H. apply H0. Qed.

Definition conti_fun_ord (D1 D2 : cpo) : ord :=
  mk_ord
  (fconti D1 D2)
  (cle D1 D2)
  (cle_refl D1 D2)
  (cle_trans D1 D2).

Definition conti_swap (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  fun t => (fun n => (fmonot D1 D2 (fcontit D1 D2 ((fmonot natO (conti_fun_ord D1 D2) c) n))) t).
Check conti_swap.

Lemma conti_swap_mono :
  forall (D1 D2 : cpo) c t,
  monotonic natO D2 (conti_swap D1 D2 c t).
Proof.
  intros. unfold monotonic. intros.
  unfold conti_swap.
  destruct c. unfold monotonic in fmonotonic0.
  apply fmonotonic0 in H.
  unfold fcontit. simpl.
  destruct (fmonot0 x).
  destruct (fmonot0 y).
  simpl in H.
  unfold cle in H. unfold fcontit in H. apply H. Qed.

Definition conti_fmono (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  fun t => mk_fmono natO D2 (conti_swap D1 D2 c t) (conti_swap_mono D1 D2 c t).

Check conti_fmono.

Definition lubpf (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  fun t => (lubp D2) (mk_fmono natO D2 (conti_swap D1 D2 c t) (conti_swap_mono D1 D2 c t)).

Check lubpf.

Lemma lubpf_mono :
  forall (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)),
  (monotonic D1 D2) (lubpf D1 D2 c).
Proof.
  intros. remember c as c0. destruct c.
  unfold monotonic. intros.
  assert (forall n, Ole D2 ((fcontit D1 D2 (fmonot0 n)) x) ((fcontit D1 D2 (fmonot0 n)) y)).
  { intros. destruct (fmonot0 n).
    simpl. destruct fcontit0. simpl. apply fmonotonic1. apply H. }
  assert (forall n, Ole D2 (fcontit D1 D2 (fmonot0 n) y) ((lubpf D1 D2 c0) y)).
  { intro n. simpl.
    unfold lubpf. eapply (Ole_trans D2).
    2 : { apply (le_lub D2) with (n:=n). }
    simpl. subst. unfold conti_swap. simpl. apply (Ole_refl D2). }
  assert (forall n, Ole D2 (fcontit D1 D2 (fmonot0 n) x) ((lubpf D1 D2 c0) y)).
  { intros. eapply (Ole_trans D2).
    - apply H0.
    - apply H1. }
  assert (forall n, fcontit D1 D2 (fmonot0 n) x = 
                    {| fmonot := conti_swap D1 D2 c0 x; fmonotonic := conti_swap_mono D1 D2 c0 x|} n).
  { intros. subst. simpl. unfold conti_swap. simpl. reflexivity. }
  assert (forall n, Ole D2
    ({| fmonot := conti_swap D1 D2 c0 x; fmonotonic := conti_swap_mono D1 D2 c0 x|} n)
    (lubpf D1 D2 c0 y)).
  { intros. rewrite <- H3. apply H2. }
  assert (Ole D2 (lubp D2 {| fmonot := conti_swap D1 D2 c0 x; fmonotonic := conti_swap_mono D1 D2 c0 x|})
                 (lubpf D1 D2 c0 y)).
  { apply (lub_le D2). apply H4. }
  unfold lubpf. unfold lubpf in H5. apply H5.
  Qed.

Definition lubpf_fmono (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  mk_fmono D1 D2
  (lubpf D1 D2 c)
  (lubpf_mono D1 D2 c).

Lemma lubpf_fmono_conti :
  forall (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)),
  continuous D1 D2 (lubpf_fmono D1 D2 c).
Proof.
  intros. unfold continuous. intros.
  destruct c.
  Admitted.

Definition lubpf_fconti (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  mk_fconti D1 D2
  (lubpf_fmono D1 D2 c)
  (lubpf_fmono_conti D1 D2 c).

Lemma lubpf_le_lub :
  forall (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) (n : nat),
  (Ole (conti_fun_ord D1 D2)) (c n) (lubpf_fconti D1 D2 c).
Proof.
  Admitted.

Lemma lubpf_lub_le : 
  forall (D1 D2 : cpo) (c: fmono natO (conti_fun_ord D1 D2)) (x : conti_fun_ord D1 D2),
  (forall n, (Ole (conti_fun_ord D1 D2)) (c n) x) -> 
  (Ole (conti_fun_ord D1 D2)) (lubpf_fconti D1 D2 c) x.
Proof.
  Admitted.

Definition fconti_cpo (D1 D2 : cpo) := mk_cpo 
  (conti_fun_ord D1 D2)
  (lubpf_fconti D1 D2)
  (lubpf_le_lub D1 D2)
  (lubpf_lub_le D1 D2).

Lemma eq_refl : 
  forall (X : Type) (t1 : X),
  t1 = t1.
Proof.
  reflexivity. Qed.

Lemma eq_trans :
  forall (X : Type) (t1 t2 t3 : X),
  t1 = t2 -> t2 = t3 -> t1 = t3.
Proof.
  intros. subst. reflexivity. Qed.

Definition discrete_ord (X : Type) :=
  mk_ord
  X
  (fun t1 => fun t2 => (t1 = t2))
  (eq_refl X)
  (eq_trans X).

Lemma discrete_le_lub (X : Type) :
  forall (c : fmono natO (discrete_ord X)) (n : nat),
    (Ole (discrete_ord X)) (c n) (c 0).
Proof.
  intros. destruct c. simpl.
  unfold monotonic in fmonotonic0.
  assert (Ole natO 0 n). simpl. omega.
  apply fmonotonic0 in H. inversion H. reflexivity.
  Qed.

Lemma discrete_lub_le (X : Type) :
  forall (c : fmono natO (discrete_ord X)) (x : discrete_ord X),
    (forall n, (Ole (discrete_ord X)) (c n) x) -> (Ole (discrete_ord X) (c 0) x).
Proof.
  intros. apply H. Qed.

Definition discrete_cpo (X : Type) :=
  mk_cpo
  (discrete_ord X)
  (fun c => c 0)
  (discrete_le_lub X)
  (discrete_lub_le X).

(*
  TODO : Show finite product of cpo is also cpo.
 *)

Class Pointed(D : cpo) := {bot:D; Pleast : forall d : D, Ole D bot d}.


