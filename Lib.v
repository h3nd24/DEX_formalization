(** Lib.v: various general-purpose properties *)
Require Export Tactics.
Require Export Relations.
Require Export List.
Require Export Bool.
Require Export ZArith.
Require Export EqBoolAux.
Require Export PosAux.
Require Export BinArray.
Require Export MapSignatures.


Lemma in_nth_error : forall (A:Set) (l:list A) n a,
  nth_error l n = Some a -> In a l.
Proof.
  induction l; simpl; intros.
  destruct n; discriminate.
  destruct n; simpl in H.
  inversion H; auto.
  right; eauto.
Qed.

Lemma app_cons : forall (A:Set) (l1 l2:list A) a,
  l1++a::l2 = (l1++a::nil)++l2.
Proof.
  induction l1; simpl; intros.
  reflexivity.
  rewrite IHl1; reflexivity.
Qed.

Lemma length_app_cons_nil : forall (A:Set) (l:list A) a,
  length (l++a::nil) = S (length l).
Proof.
  induction l; simpl; intros.
  reflexivity.
  rewrite IHl; reflexivity.
Qed.

Lemma app_inj_right : forall (A:Set) (l1 r1 l2 r2:list A),
  length l1 = length l2 ->
  l1++r1 = l2++r2 -> r1=r2.
Proof.
  induction l1; destruct l2; simpl; intros; try discriminate; auto.
  injection H; injection H0; intros; eauto.
Qed.

Lemma app_inj : forall (A:Set) (l1 r1 l2 r2:list A),
  length l1 = length l2 ->
  l1++r1 = l2++r2 -> l1=l2 /\ r1=r2.
Proof.
  induction l1; destruct l2; simpl; intros; try discriminate; auto.
  injection H; injection H0; intros.
  elim IHl1 with r1 l2 r2; intros; auto.
  subst; auto.
Qed.

Lemma app_exists_if_length : forall (A:Set) (l:list A) n,
  (n <= length l)%nat ->
  exists l1, exists l2, length l1 = n /\ l = l1 ++ l2.
Proof.
  induction l; simpl; intros.
  exists (@nil A).
  destruct n.
  exists (@nil A); simpl; auto.
  apply False_ind; omega.
  destruct n.
  exists (@nil A); exists (a::l); auto.
  destruct (IHl n) as [l1 [l2 [H1 H2]]].
  omega.
  exists (a::l1); exists l2; split; simpl; auto.
  rewrite H2; auto.
Qed.

Lemma app_length_le : forall (A:Set) (l1 l2:list A),
  (length l1 <= length (l1++l2))%nat.
Proof.
  induction l1; simpl; intros.
  omega.
  generalize (IHl1 l2); omega.
Qed.

Lemma length_app_length : forall (A B:Set) (l1 l3 :list A) (l2 l4 :list B),
  length l1 = length l2 ->
  length (l1++l3) = length (l2++l4) ->
  length l3 = length l4.
Proof.
  induction l1; destruct l2; intros; try discriminate; 
  simpl in *; auto.
  injection H; injection H0; intros; eapply IHl1; eauto.
Qed.

Lemma not_none_some : forall (A:Type) (a:option A) (b:A), 
  a <> None -> exists b, a = Some b.
Proof.
  intros; destruct a; try(exists a; auto); try (apply False_ind; auto).
Qed.

Section eq_dec.
  Variable t:Set.
  Variable P:t->t->Prop.
  Variable test_bool : t -> t -> bool.
  Definition test_bool_spec : Prop := forall x y, if test_bool x y then P x y else ~ P x y.
  Variable test_bool_prop : test_bool_spec.
  Lemma P_dec : forall l l':t, {P l l'}+{~P l l'}.
  Proof.
    intros x y; generalize (test_bool_prop x y); case (test_bool x y); auto.
  Qed.
End eq_dec.
Implicit Arguments P_dec.
Implicit Arguments test_bool_spec.
