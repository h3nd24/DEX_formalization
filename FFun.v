(** * FFun.v: finite partial functions *)

Require Import Arith.
Require Import Omega.
Require Import Tactics.

Section A.
Variable A:Set.
(** A formalization of finite functions from nat -> A *)

(** FFun.t *)
Record t : Set := make {
  lookup :> nat -> option A;
  domain_size : nat;
  lookup_domain : forall n, n<domain_size <-> (lookup n<>None)
}.

Lemma lookup_domain_empty : forall n, n<O <-> (@None A<>None).
Proof.
  split; intuition || omega.
Qed.

(** empty function *)
Definition empty : t := make (fun _ => None) O lookup_domain_empty.


Lemma lookup_domain_proof : forall (f:t) (a:A),
  forall n, n<(S f.(domain_size)) 
         <-> (match eq_nat_dec n f.(domain_size) with
                 left _ => Some a
               | right _ => f.(lookup) n
               end <> None).
Proof.
  intros (lookup0,domain_size0,lookup_domain0) a n; simpl; split; intros;
  destruct eq_nat_dec; subst.
  discriminate.
  destruct (lookup_domain0 n).
  apply H0.
  omega.
  omega.
  destruct (lookup_domain0 n).
  generalize (H1 H); omega.  
Qed.


(** add one image associated with the next key available *)
Definition extends (f:t) (a:A) : t :=
  make 
    (fun n => match eq_nat_dec n f.(domain_size) with
                left _ => Some a
              | right _ => f.(lookup) n
              end)
    (S f.(domain_size))
    (lookup_domain_proof f a).
     

(** Next key available *)
Definition next (f:t) : nat := f.(domain_size).

Lemma extends_old: forall (f:t) n a a',
   f n = Some a -> (extends f a') n = Some a.
Proof.
  intros (lookup0,domain_size0,lookup_domain0) n a a'; simpl; intros.
  destruct eq_nat_dec; subst.
  destruct (lookup_domain0 domain_size0).
  assert (domain_size0 < domain_size0).
  apply H1; rewrite H; discriminate.
  apply False_ind; omega.
  assumption.
Qed.

Lemma extends_new: forall f a,
  (extends f a) (next f) = Some a.
Proof.
  intros (lookup0,domain_size0,lookup_domain0) a; simpl; intros.
  destruct eq_nat_dec; auto.
  elim n; reflexivity. 
Qed.

Lemma extends_case: forall f n a a',
  (extends f a) n = Some a' ->
  f n = Some a' \/ (a=a' /\ n=next f).
Proof.
  intros (lookup0,domain_size0,lookup_domain0) n a a'; simpl; intros.
  destruct eq_nat_dec; subst.
  injection H; intros; subst; auto.
  auto.
Qed.

Lemma next_none: forall (f:t), f (next f) = None.
Proof.
  destruct f; simpl.
  destruct (lookup_domain0 domain_size0).
  destruct (lookup0 domain_size0); auto.
  assert (domain_size0 < domain_size0).
  apply H0; discriminate.
  apply False_ind; omega.
Qed.

(* derivable from previous lemma *)
Lemma next_clean: forall (f:t) n a,
  f n = Some a -> n<>(next f).
Proof.
  red; intros.
  subst; rewrite next_none in H; discriminate.
Qed.

(** image of a partial function *)
Definition image : t -> A -> Prop :=
  fun f a => (exists n:nat, f n = Some a).

Definition is_inj (f:t):=
 forall n n' a,
   f n = Some a -> f n'= Some a -> n = n'.

Lemma extends_inj: forall f a,
   ~(image f a) -> is_inj f -> is_inj (extends f a).
Proof.
  unfold is_inj; intros.
  elim extends_case with f n a a0; intros; 
  elim  extends_case with f n' a a0; intros; 
  intuition; subst; eauto.
  elim H; exists n; auto.
  elim H; exists n'; auto.
Qed.

Lemma inv_aux : forall (m n:nat)(f f':t)(lm lm' ln ln':A),
  is_inj f-> is_inj f'->
  f m = Some lm -> f' m = Some lm'->
  f n = Some ln -> f' n = Some ln'->
  lm = ln -> lm' = ln'.
Proof.
  intros.
  assert (m=n).
  subst.
  apply (H m n ln); auto.
  subst; auto.
  rewrite H4 in H2; inversion H2; auto.
Qed. 


(** compatibility between two finite functions  *)
Definition compat (f f': t): Prop :=
  forall n, f n = None <-> f' n = None.

Lemma compat_implies_next : forall f1 f2,
  compat f1 f2 -> next f1 = next f2.
Proof.
  unfold compat, next; intros.
  destruct (le_lt_dec (domain_size f1) (domain_size f2)).
  destruct (eq_nat_dec (domain_size f1) (domain_size f2)).
  auto.
  destruct (H (domain_size f1)).
  destruct (lookup_domain f2 (domain_size f1)).
  elim H2.
  omega.
  apply H0; apply next_none.
  destruct (H (domain_size f2)).
  destruct (lookup_domain f1 (domain_size f2)).
  elim H2.
  omega.
  apply H1; apply next_none.
Qed.

Lemma next_implies_compat : forall f1 f2,
  next f1 = next f2 -> compat f1 f2.
Proof.
  unfold compat, next; intros.
  destruct (le_lt_dec (domain_size f1) n).
  split; intros.
  destruct (lookup_domain f2 n).
  destruct (lookup f2 n); auto.
  assert (n < domain_size f2).
  apply H2; discriminate.
  apply False_ind; omega.
  destruct (lookup_domain f1 n).
  destruct (lookup f1 n); auto.
  assert (n < domain_size f1).
  apply H2; discriminate.
  apply False_ind; omega.
  split; intros.
  destruct (lookup_domain f1 n).
  elim H1; auto.
  destruct (lookup_domain f2 n).
  elim H1; try omega; auto.
Qed.

Lemma compat_extends:  forall f1 f2 n a1 a2 a,
  compat f1 f2 ->
  f1 n = Some a1 ->
  (extends f2 a) n = Some a2 ->
  f2 n = Some a2.
Proof.
  intros.
  caseeq (lookup f2 n); intros.
  assert (Haux:=extends_old f2 n _ a H2).
  rewrite  Haux in H1; assumption.
  destruct (H n).
  rewrite H4 in H0; auto; discriminate.
Qed.

Lemma compat_preserved_by_extends : forall b b' loc loc',
  compat b b' ->
  compat (extends b loc) (extends b' loc').
Proof.
  unfold compat, extends; intros.
  generalize (compat_implies_next _ _ H); unfold next; intros.
  split; intros; simpl in *.
  destruct (eq_nat_dec n (domain_size b)).
  discriminate H1.
  destruct (eq_nat_dec n (domain_size b')).
  elim n0; rewrite e; auto.
  destruct (H n); auto.
  destruct (eq_nat_dec n (domain_size b')).
  discriminate.
  destruct (eq_nat_dec n (domain_size b)).
  elim n0; rewrite e; auto.
  destruct (H n); auto.
Qed.



End A.

Implicit Arguments lookup [A].
Implicit Arguments domain_size [A].
Implicit Arguments lookup_domain [A].
Implicit Arguments image [A].
Implicit Arguments next [A].
Implicit Arguments compat [A].
Implicit Arguments extends [A].
Implicit Arguments is_inj [A].

