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

(** Basic Domain Theory *)

(*
   The normal definition of poset contains antisymmetry, meaning
   x <= y -> y <= x -> x = y
   however we do not include it here.
   First, we can induce poset with antisymmetry by creating
   congruence class with relation a ~ b := a <= b /\ b <= a.
   Second, adding antisymmetry will break our approach on 
   creating pointed cpo from cpo. The detail on this will explained later.
 *)
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


Lemma lubp_preserves_order : 
  forall (D : cpo) (f1 f2 : fmono natO D),
  (forall n, Ole D (f1 n) (f2 n)) -> Ole D (lubp D f1) (lubp D f2).
Proof.
  intros.
  assert (forall n, Ole D (f1 n) (lubp D f2)).
  { intros. eapply (Ole_trans D).
    - apply H.
    - apply (le_lub D). }
  apply (lub_le D). apply H0.
  Qed.

Lemma lubpf_fmono_conti :
  forall (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)),
  continuous D1 D2 (lubpf_fmono D1 D2 c).
Proof.
  
  Admitted.

Definition lubpf_fconti (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) :=
  mk_fconti D1 D2
  (lubpf_fmono D1 D2 c)
  (lubpf_fmono_conti D1 D2 c).

Lemma lubpf_le_lub :
  forall (D1 D2 : cpo) (c : fmono natO (conti_fun_ord D1 D2)) (n : nat),
  (Ole (conti_fun_ord D1 D2)) (c n) (lubpf_fconti D1 D2 c).
Proof.
  intros. simpl. unfold cle. intros. simpl.
  unfold lubpf.
  pose proof (le_lub D2 
    {| fmonot := conti_swap D1 D2 c t; fmonotonic := conti_swap_mono D1 D2 c t |}
    n).
  simpl in H.
  replace (fcontit D1 D2 (c n) t) with (conti_swap D1 D2 c t n).
  apply H.
  unfold conti_swap. reflexivity.
  Qed.

Lemma lubpf_lub_le : 
  forall (D1 D2 : cpo) (c: fmono natO (conti_fun_ord D1 D2)) (x : conti_fun_ord D1 D2),
  (forall n, (Ole (conti_fun_ord D1 D2)) (c n) x) -> 
  (Ole (conti_fun_ord D1 D2)) (lubpf_fconti D1 D2 c) x.
Proof.
  intros. simpl. unfold cle. intros. simpl.
  unfold lubpf. Search lubp.
  pose proof (lub_le D2 
    {| fmonot := conti_swap D1 D2 c t; fmonotonic := conti_swap_mono D1 D2 c t |}
    (fcontit D1 D2 x t)
    ).
  apply H0. intros. simpl.
  unfold conti_swap. apply H. Qed.

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

Definition product_le (D1 D2 : cpo) (x y : prod D1 D2) :=
  match x with
  | pair x1 x2 =>
    match y with
    | pair y1 y2 => (Ole D1 x1 y1) /\ (Ole D2 x2 y2)
    end
  end.

Lemma product_le_refl (D1 D2 : cpo):
  forall x, product_le D1 D2 x x.
Proof.
  intros. unfold product_le. destruct x. split.
  apply (Ole_refl D1). apply (Ole_refl D2).
  Qed.

Lemma product_le_trans (D1 D2 : cpo) :
  forall x y z, product_le D1 D2 x y -> product_le D1 D2 y z -> product_le D1 D2 x z.
Proof.
  unfold product_le. intros. destruct x, y, z.
  destruct H, H0.
  split.
  - eapply (Ole_trans D1). apply H. apply H0.
  - eapply (Ole_trans D2). apply H1. apply H2.
  Qed.

Definition product_ord (D1 D2 : cpo) :=
  mk_ord
  (prod D1 D2)
  (product_le D1 D2)
  (product_le_refl D1 D2)
  (product_le_trans D1 D2).

Lemma fst_product_mono : 
  forall (D1 D2 : cpo) (c : fmono natO (product_ord D1 D2)),
  monotonic natO D1 (fun n => fst (c n)).
Proof.
  intros. destruct c. unfold monotonic. intros.
  unfold monotonic in fmonotonic0. apply fmonotonic0 in H.
  simpl in H. simpl. destruct (fmonot0 x), (fmonot0 y).
  simpl. unfold product_le in H. destruct H as [H _]. apply H.
  Qed.

Lemma snd_product_mono : 
  forall (D1 D2 : cpo) (c : fmono natO (product_ord D1 D2)),
  monotonic natO D2 (fun n => snd (c n)).
Proof.
  intros. destruct c. unfold monotonic. intros.
  unfold monotonic in fmonotonic0. apply fmonotonic0 in H.
  simpl in H. simpl. destruct (fmonot0 x), (fmonot0 y).
  simpl. unfold product_le in H. destruct H as [_ H]. apply H.
  Qed.

Definition product_lubp (D1 D2 : cpo) (c : fmono natO (product_ord D1 D2)) :=
  pair (lubp D1 (mk_fmono natO D1 (fun (n:natO) => fst (c n)) (fst_product_mono D1 D2 c))) 
       (lubp D2 (mk_fmono natO D2 (fun (n:natO) => snd (c n)) (snd_product_mono D1 D2 c))).

Lemma product_le_lub :
  forall (D1 D2 : cpo) (c : fmono natO (product_ord D1 D2)) (n : nat),
  (Ole (product_ord D1 D2)) (c n) (product_lubp D1 D2 c).
Proof.
  intros.
  pose proof (le_lub D1 (mk_fmono natO D1 (fun (n:natO) => fst (c n)) 
                                          (fst_product_mono D1 D2 c)) n).
  pose proof (le_lub D2 (mk_fmono natO D2 (fun (n:natO) => snd (c n)) 
                                          (snd_product_mono D1 D2 c)) n).
  simpl in H. simpl in H0.
  simpl. unfold product_le.
  destruct (c n). simpl in *. split; assumption.
  Qed.

Lemma product_lub_le : 
  forall (D1 D2 : cpo) (c: fmono natO (product_ord D1 D2)) (x : product_ord D1 D2),
  (forall n, (Ole (product_ord D1 D2)) (c n) x) -> 
  (Ole (product_ord D1 D2)) (product_lubp D1 D2 c) x.
Proof.
  intros. simpl. destruct x. split.
  - apply (lub_le D1). simpl in H. intros.
    pose proof (H n). simpl.
    destruct (c n). simpl. unfold product_le in H0. destruct H0.
    apply H0.
  - apply (lub_le D2). simpl in H. intros.
    pose proof (H n). simpl.
    destruct (c n). simpl. unfold product_le in H0. destruct H0.
    apply H1.
  Qed.

Definition product_cpo (D1 D2 : cpo) : cpo :=
  mk_cpo
  (product_ord D1 D2)
  (product_lubp D1 D2)
  (product_le_lub D1 D2)
  (product_lub_le D1 D2).

Class Pointed(D : cpo) := {bot:D; Pleast : forall d : D, Ole D bot d}.

Instance prod_pointed (A B : cpo) (pa : Pointed A) (pb : Pointed B) : Pointed (product_cpo A B).
Proof.
  destruct pa. destruct pb.
  exists (pair bot0 bot1). intros. simpl.
  destruct d. split; auto.
  Defined.

Instance fun_pointed (A B : cpo) (pb : Pointed B) : Pointed (fconti_cpo A B).
Proof.
  destruct pb.
  assert (monotonic A B (fun t => bot0)).
  { unfold monotonic. intros. apply (Ole_refl B). }
  remember (mk_fmono A B (fun t => bot0) H) as fmonobot.
  assert (continuous A B fmonobot).
  { unfold continuous. intros. subst. simpl. apply Pleast0. }
  remember (mk_fconti A B fmonobot H0).
  exists f. intros. simpl. unfold cle.
  intros. rewrite Heqf. simpl. rewrite Heqfmonobot. simpl. apply Pleast0.
  Defined.

Fixpoint repeat (C : cpo) (D : Pointed C) (f : fconti C C) (n : nat) : C :=
  match n with
  | 0 => (bot)
  | S n' => (fcontit C C f) (repeat C D f n')
  end.

Lemma repeat_mono :
  forall (C : cpo) (D : Pointed C) (f : fconti C C),
  monotonic natO C (repeat C D f).
Proof.
  intros. unfold monotonic. intros. simpl in H. generalize dependent x. induction y.
  - intros. assert (x = 0) by omega. subst. apply (Ole_refl C).
  - intros. destruct x.
    + simpl. apply Pleast.
    + simpl. destruct f. simpl. destruct fcontit0. simpl.
      apply fmonotonic0. apply IHy. omega.
  Qed.

Definition repeat_fmono (C : cpo) (D : Pointed C) (f : fconti C C) : fmono natO C :=
  mk_fmono natO C
  (repeat C D f)
  (repeat_mono C D f).

Definition fixp (C : cpo) (D : Pointed C) (f : fconti C C) : C :=
  lubp C (repeat_fmono C D f).

(* TODO : fixp itself is continuous. *)

Definition admmisible (D : cpo) (pd : Pointed D) (P : D -> Prop) :=
  forall (c : fmono natO D),
  (forall n, P (c n)) -> P (lubp D c).

Definition fixp_ind (D : cpo) (pd : Pointed D) :
  forall (F : fconti D D) (P : D -> Prop),
  admmisible D pd P -> 
  P bot -> 
  (forall x, P x -> P ((fcontit D D F) x)) ->
  P (fixp D pd F).
Proof.
  intros. unfold fixp. unfold admmisible in H.
  apply H. induction n.
  - simpl. apply H0.
  - simpl. apply H1. apply IHn.
  Qed.

(** Pointed Domain *)

(*
   Here, instead of simple implementation
   Inductive botted (D : cpo) :=
   | bot : botted D
   | val : D -> botted D.
   we use stream based implementation. 
   Reason here is to make our lubp function be constructive (and computable).
   If we use simple implementation, to check whether the input is all bot, 
   we need to check every input, yielding uncomputability.
   To overcome this problem, we use lazy evaluation property of coinductive types
   and cofixpoint.
   Here, if we add antisymmetry, we have
   Val n <= Eps (Val n) and Eps (Val n) <= Val n, contradicting antisymmetry.
 *)

CoInductive Stream (D : cpo) := 
  Eps : Stream D -> Stream D |
  Val : D -> Stream D.

Fixpoint pred_nth {D : cpo} (x : Stream D) (n : nat) : Stream D :=
  match x, n with
  | Eps _ x', S n' => pred_nth x' n'
  | Val _ d, _ => x
  | Eps _ x', 0 => x
  end.

CoInductive DLle {D : cpo} : Stream D -> Stream D -> Prop :=
  | DLleEps : forall x y, DLle x y -> DLle (Eps D x) (Eps D y)
  | DLleEpsVal : forall x d, DLle x (Val D d) -> DLle (Eps D x) (Val D d)
  | DLleVal : forall d d' n y, 
      pred_nth y n = Val D d' -> Ole D d d' -> DLle (Val D d) y.

(* This lemma creates induction appliable to DLle. *)
Lemma DLle_rec {D : cpo} : forall R : Stream D -> Stream D -> Prop,
  (forall x y, R (Eps D x) (Eps D y) -> R x y) ->
  (forall x d, R (Eps D x) (Val D d) -> R x (Val D d)) ->
  (forall d y, R (Val D d) y -> exists n d', pred_nth y n = Val D d' /\ Ole D d d') ->
  forall x y, R x y -> DLle x y.
Proof.
  cofix H.
  intros.
  destruct x, y.
  - apply H0 in H3. apply DLleEps. apply H with R; auto.
  - apply DLleEpsVal. apply H1 in H3. apply H with R; auto.
  - apply H2 in H3. destruct H3 as [n [d' [H31 H32]]].
    eapply DLleVal; eauto.
  - apply H2 in H3. destruct H3 as [n [d' [H31 H32]]].
    eapply DLleVal; eauto.
  Qed.

Lemma DLle_refl {D : cpo} : forall (c : Stream D),
  DLle c c.
Proof.
  intros. apply DLle_rec with eq.
  - intros. inversion H. reflexivity.
  - intros. inversion H.
  - intros. subst. exists 0. exists d. split.
    + simpl. reflexivity.
    + apply (Ole_refl D).
  - reflexivity.
  Qed.

Lemma DLle_exists_pred {D : cpo} : forall (c1 c2 : Stream D) (d : D) (n : nat),
  pred_nth c1 n = Val D d ->
  DLle c1 c2 ->
  exists n' d', pred_nth c2 n' = Val D d' /\ Ole D d d'.
Proof.
  intros c1 c2 d n. generalize dependent c1.
  generalize dependent c2. generalize dependent d.
  induction n; intros.
  - simpl in H. destruct c1.
    + discriminate.
    + inversion H. inversion H0; subst.
      exists n. exists d'. split. apply H3. apply H4.
  - simpl in H. destruct c1.
    + inversion H0; subst.
      * apply IHn with (c2 := y) in H.
        destruct H as [n' [d' [H H']]].
        exists (S n'). exists d'. simpl. split. apply H. apply H'. apply H2.
      * apply IHn with (c2 := (Val D d0)) in H.
        destruct H as [n' [d' [H H']]].
        2 : { apply H2. }
        exists 0. exists d0. split. reflexivity.
        destruct n'; simpl in H; inversion H; subst; apply H'.
    + inversion H; subst. clear H.
      inversion H0; subst.
      exists n0. exists d'. split. apply H1. apply H2.
  Qed.

Lemma DLle_trans {D : cpo} : forall (c1 c2 c3 : Stream D),
  DLle c1 c2 -> DLle c2 c3 -> DLle c1 c3.
Proof.
  intros. apply DLle_rec with (fun t1 => fun t2 => exists t, DLle t1 t /\ DLle t t2).
  - intros. destruct H1 as [t [H1 H2]].
    inversion H1; subst.
    + inversion H2; subst.
      exists y0. split; auto.
    + exists (Val D d). inversion H2; subst. split; auto.
      destruct n.
      * simpl in H5. discriminate.
      * simpl in H5. eapply DLleVal. apply H5. apply H6.
  - intros. destruct H1 as [t [H1 H2]].
    inversion H1; subst.
    + exists y. split; auto. inversion H2; auto.
    + exists (Val D d0).
      split; auto.
  - intros. destruct H1 as [t [H1 H2]].
    inversion H1; subst.
    pose proof (DLle_exists_pred t y d' n H4 H2).
    destruct H3 as [n' [d'0 [H31 H32]]].
    exists n'. exists d'0. split. apply H31.
    eapply (Ole_trans D). apply H5. apply H32.
  - exists c2. split; auto.
  Qed.

Definition DL_ord (D : cpo) : ord :=
  mk_ord
  (Stream D)
  DLle
  DLle_refl
  DLle_trans.

(*
   Here, to generate lubp, we need to parallely iterate sequence.
   We iterate 1,1 -> 2,1 -> 1,2 -> 3,1 -> 2,2 -> 1,3
   (where first number means nth element of sequence, second number means
    nth epsilon in stream)
   and whenever element is Eps, we add Eps to output value.
   Now if we meet value, since c is monotonic, we know later elements in sequence
   are finite (in sense of stream). Then we can extract its value, returning
   lubp of these values.
 *)

(*
   lubp procedure will require decision procedure based approach.
   See https://softwarefoundations.cis.upenn.edu/current/vfa-current/Decide.html
   for more details.
 *)

Definition DL_lubp (D : cpo) (c : fmono natO (DL_ord D)) : DL_ord D. Admitted.

Lemma DL_le_lub (D : cpo) :
  forall (c : fmono natO (DL_ord D)) (n : nat),
    (Ole (DL_ord D)) (c n) (DL_lubp D c).
Proof.
  Admitted.

Lemma DL_lub_le (D : cpo) :
  forall (c : fmono natO (DL_ord D)) (x : (DL_ord D)),
    (forall n, (Ole (DL_ord D)) (c n) x) -> (Ole (DL_ord D)) (DL_lubp D c) x.
Proof.
  Admitted.

Definition DL_cpo (D : cpo) := 
  mk_cpo
  (DL_ord D)
  (DL_lubp D)
  (DL_le_lub D)
  (DL_lub_le D).

CoFixpoint DL_bot (D : cpo) : Stream D := Eps D (DL_bot D).

Definition DL_destruct (D : cpo) (d : Stream D) :=
  match d with
  | Val _ d' => Val D d'
  | Eps _ d' => Eps D d'
  end.

Lemma DL_destruct_eq (D : cpo) :
  forall d, d = DL_destruct D d.
Proof.
  intros. case d; simpl; trivial. Qed.

Lemma bot_eq_eps_bot (D : cpo) : 
  DL_bot D = Eps D (DL_bot D).
Proof.
  assert (DL_destruct D (DL_bot D) = Eps D (DL_bot D)).
  { simpl. reflexivity. }
  rewrite <- H. apply DL_destruct_eq. Qed.

CoInductive Bisimilar (D : cpo) : Stream D -> Stream D -> Prop :=
  | Bisimilar_Val : forall d, Bisimilar D (Val D d) (Val D d)
  | Bisimilar_Eps : forall d d',
      Bisimilar D d d' -> Bisimilar D (Eps D d) (Eps D d').

Lemma bisimilar_dleq (D : cpo) :
  forall d d',
  Bisimilar D d d' -> Ole (DL_cpo D) d d'.
Proof.
  cofix H.
  intros. inversion H0; subst.
  - simpl. apply DLle_refl.
  - simpl. constructor. apply H. apply H1.
  Qed.

CoInductive Infinite (D : cpo) : Stream D -> Prop :=
  Infinite_Eps : forall d, Infinite D d -> Infinite D (Eps D d).
Inductive Finite (D : cpo) : Stream D -> Prop :=
  | Finite_Val : forall d, Finite D (Val D d)
  | Finite_Eps : forall d, Finite D (d) -> Finite D (Eps D d).

Lemma Infinite_not_Finite (D : cpo) :
  forall d, Infinite D d -> ~ Finite D d.
Proof.
  intros. intro H'. generalize dependent H. induction H'.
  - intro. inversion H.
  - intros. inversion H; subst. apply IHH' in H1. destruct H1.
  Qed.

Lemma finite_pred_nth (D : cpo) :
  forall d, Finite D d -> exists n d', pred_nth d n = Val D d'.
Proof.
  intros. induction H.
  - exists 0. exists d. reflexivity.
  - destruct IHFinite as [n [d' IHF]].
    exists (S n). exists d'. simpl. apply IHF.
  Qed.

Lemma infinite_bt (D : cpo) :
  forall d, Infinite D d -> Bisimilar D d (DL_bot D).
Proof.
  cofix H.
  intros. inversion H0; subst.
  rewrite bot_eq_eps_bot. constructor. apply H. apply H1. Qed.

Lemma pred_nth_over (D : cpo) :
  forall n d d',
  pred_nth d n = Val D d' ->
  pred_nth d (S n) = Val D d'.
Proof.
  induction n; intros.
  - simpl in H. destruct d; try discriminate. inversion H; subst.
    simpl. reflexivity.
  - simpl in H. destruct d.
    + simpl. apply IHn. apply H.
    + simpl. apply H.
  Qed.

Lemma pred_nth_val (D : cpo) :
  forall d n,
  pred_nth (Val D d) n = Val D d.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
  Qed.

Lemma DLle_bot_val (D : cpo) :
  forall d,
  DLle (DL_bot D) (Val D d).
Proof.
  cofix H.
  intros. rewrite bot_eq_eps_bot. constructor. apply H.
  Qed.

Lemma DL_pointed (D : cpo) :
  forall (d : DL_ord D),
  Ole (DL_ord D) (DL_bot D) d.
Proof.
  cofix H.
  intros. simpl. destruct d.
  - rewrite bot_eq_eps_bot. constructor. apply H.
  - apply DLle_bot_val.
  Qed.

Instance DL_Pointed (D : cpo) : Pointed (DL_cpo D).
Proof.
  exists (DL_bot D). apply (DL_pointed D). Qed.

Definition lift (D : cpo) (d : D): DL_cpo D := Val D d. 

Lemma lift_mono (D : cpo) :
  monotonic D (DL_cpo D) (lift D).
Proof.
  unfold monotonic. intros. simpl. unfold lift.
  apply DLleVal with (n:=0) (d':=y).
  - simpl. reflexivity.
  - apply H.
  Qed.

Definition lift_fmono (D : cpo) := mk_fmono D (DL_cpo D) (lift D) (lift_mono D).

Lemma lift_conti (D : cpo) :
  continuous D (DL_cpo D) (lift_fmono D).
Proof.
  unfold continuous. intros. simpl.
  unfold lift. econstructor.
  
  Admitted.

(* TODO : lift itself is also continuous. *)

CoFixpoint kleisli (D E : cpo) (f : fconti D (DL_cpo E)) (d : DL_cpo D): (DL_cpo E) :=
  match d with
  | Eps _ dl => Eps E (kleisli D E f dl)
  | Val _ d' => (fcontit D (DL_cpo E) f) d'
  end.

Lemma kleisli_mono (D E : cpo) :
  forall (f : fconti D (DL_cpo E)),
  monotonic (DL_cpo D) (DL_cpo E) (kleisli D E f).
Proof.
  Admitted.

Definition kleisli_fmono (D E : cpo) (f : fconti D (DL_cpo E)) := 
  mk_fmono (DL_cpo D) (DL_cpo E)
  (kleisli D E f)
  (kleisli_mono D E f).

Lemma kleisli_conti (D E : cpo) :
  forall (f : fconti D (DL_cpo E)),
  continuous (DL_cpo D) (DL_cpo E) (kleisli_fmono D E f).
Proof.
  Admitted.

Definition kleisli_fconti (D E : cpo) (f : fconti D (DL_cpo E)) :=
  mk_fconti (DL_cpo D) (DL_cpo E)
  (kleisli_fmono D E f)
  (kleisli_conti D E f).

(* TODO : kleisli itself is also continuous function *)


