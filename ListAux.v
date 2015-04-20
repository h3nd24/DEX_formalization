Require Export List.
Require Import Bool.

Lemma in_fold_cons : forall (A B:Type) (f:A->B) l,
  fold_right (fun a q => (f a)::q) nil l = map f l.
Proof.
  induction l; simpl; intros; auto.
Qed.

Lemma fold_right_map : forall (A B C:Type) (f:A->B->B) (g:C->A) (b:B) l,
  fold_right f b (map g l) = fold_right (fun a => f (g a)) b l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma fold_right_eq : forall (A B:Type) (f1 f2:A->B->B) (b:B) l,
  (forall a, f1 a = f2 a) ->
  fold_right f1 b l = fold_right f2 b l.
Proof.
  induction l; simpl; intros; auto.
   rewrite IHl ;auto.
   rewrite H; auto.
Qed.

Lemma fold_right_eq2 : forall (A B:Type) (f1 f2:A->B->B) (b:B) l,
  (forall a b, f1 a b = f2 a b) ->
  fold_right f1 b l = fold_right f2 b l.
Proof.
  induction l; simpl; intros; auto.
   rewrite IHl ;auto.
Qed.

Lemma in_map_inv : forall (A B:Type) x (f:A->B) l,
  In x (map f l) -> exists y, x=f y /\ In y l.
Proof.
 induction l; simpl; intuition.
 subst; eauto.
 destruct H; intuition eauto.
Qed.

Lemma in_flat_map_inv : forall (A B:Type) (f:A->list B) b l,
  In b (flat_map f l) -> exists a,
    In b (f a) /\ In a l.
Proof.
  induction l; simpl; intros.
  destruct H.
  destruct (@in_app_or _ _  _ _ H).
  exists a; split; auto.
  destruct (IHl H0).
  intuition eauto.
Qed.

Lemma in_flat_map : forall (A B:Type) (f:A->list B) b a l,
  In b (f a) -> In a l -> In b (flat_map f l).
Proof.
  induction l; simpl; intros.
  destruct H0.
  destruct H0; apply in_or_app.
  subst; auto.
  auto.
Qed.

Lemma fold_right_app : forall (B C:Type)(f:B->C->C) c l1 l2,
  fold_right f c (l1++l2) = 
     fold_right f (fold_right f c l2) l1.
Proof.
  induction l1; simpl; auto; intros.
  rewrite IHl1; auto.
Qed.

Lemma fold_right_flat_map : forall (A B C:Type)(f:B->C->C)(g:A->list B) c l,
  fold_right f c (flat_map g l) = 
     fold_right (fun a c => fold_right f c (g a)) c l.
Proof.
  induction l; simpl; auto.
  rewrite fold_right_app.
  rewrite IHl; auto.
Qed.

Section assoc.

Variable A B :Type.
Variable Aeq : A -> A -> bool.
Variable Aeq_spec : forall x y, if Aeq x y then x = y else x <> y.
Implicit Types x a : A.
Implicit Types l : list (A*B).

Fixpoint assoc x l {struct l} : option B :=
  match l with
    nil => None
  | (a,b)::q =>
     if (Aeq x a) then Some b else (assoc x q)
  end.

Fixpoint mem_assoc x l {struct l} : bool :=
  match l with
    nil => false
  | (a,_)::q =>
     if (Aeq x a) then true else (mem_assoc x q)
  end.

Fixpoint remove_assoc x l {struct l} : list (A*B) :=
  match l with
    nil => nil
  | (a,b)::q => if (Aeq x a) then q else (a,b)::(remove_assoc x q)
  end.

Fixpoint remove_all_assoc x l {struct l} : list (A*B) :=
  match l with
    nil => nil
  | (a,b)::q => if (Aeq x a) then remove_all_assoc x q
                else (a,b)::(remove_all_assoc x q)
  end.

Fixpoint modify_assoc x l (f:option B->option B) {struct l} : list (A*B) :=
  match l with
    nil => match f None with
             None => nil
           | Some b => (x,b)::nil
           end
  | (a,b)::q => if (Aeq x a) then 
                  match f (Some b) with
                    None => remove_all_assoc x q
                  | Some b => (a,b)::q
                  end
                else (a,b)::(modify_assoc x q f)
  end.

  Lemma assoc_remove_all_assoc1 : forall a l,
    assoc a (remove_all_assoc a l) = None.
  Proof.
    induction l; simpl; auto.
    destruct a0.
    assert (UU:=Aeq_spec a a0);destruct (Aeq a a0); simpl; subst; auto.
    assert (UU':=Aeq_spec a a0);destruct (Aeq a a0);simpl; subst; intuition.   
  Qed.

  Lemma assoc_remove_all_assoc2 : forall x a l,
    x <> a ->
    assoc x (remove_all_assoc a l) = assoc x l.
  Proof.
    induction l; simpl; intros; auto.
    destruct a0.
    assert (UU:=Aeq_spec a a0);destruct (Aeq a a0); simpl; subst.
    assert (UU:=Aeq_spec x a0);destruct (Aeq x a0); simpl; subst; intuition.
    assert (UU':=Aeq_spec x a0);destruct (Aeq x a0); simpl; subst; intuition.
  Qed.

  Lemma assoc_modify_assoc1 : forall l x f,
    assoc x (modify_assoc x l f) = f (assoc x l).
  Proof.
    induction l; simpl; intros.
    destruct (f None); simpl; auto.
    assert (UU:=Aeq_spec x x);destruct (Aeq x x); intuition.
    destruct a.
    assert (UU:=Aeq_spec x a);destruct (Aeq x a); subst; simpl.
    destruct f; simpl.
     assert (UU:=Aeq_spec a a);destruct (Aeq a a); intuition.
    apply assoc_remove_all_assoc1.
    assert (UU':=Aeq_spec x a);destruct (Aeq x a);intuition.
  Qed.

  Lemma assoc_modify_assoc2 : forall l x a f,
    x <> a ->
    assoc x (modify_assoc a l f) = assoc x l.
  Proof.
    induction l; simpl; intros.
    destruct f; simpl; auto.
     assert (UU:=Aeq_spec x a);destruct (Aeq x a); intuition.
    destruct a.
    assert (UU:=Aeq_spec x a);destruct (Aeq x a); intuition.
    assert (UU':=Aeq_spec a0 a);destruct (Aeq a0 a); subst.
    intuition. simpl.
    assert (UU:=Aeq_spec a a);destruct (Aeq a a); intuition.
    assert (UU':=Aeq_spec a0 a);destruct (Aeq a0 a); subst.
    destruct f; simpl.
   assert (UU':=Aeq_spec x a);destruct (Aeq x a); intuition.
   apply assoc_remove_all_assoc2; auto.
   simpl.   assert (VV':=Aeq_spec x a);destruct (Aeq x a); intuition.
  Qed.

End assoc.

Implicit Arguments assoc.
Implicit Arguments mem_assoc.
Implicit Arguments remove_assoc.
Implicit Arguments remove_all_assoc.
Implicit Arguments modify_assoc.

Section assoc_distinct.

Variable A B :Type.
Variable Aeq : A -> A -> bool.
Variable Aeq_spec : forall x y, if Aeq x y then x = y else x <> y.
Implicit Types x a : A.
Implicit Types l : list (A*B).

Inductive in_dom x : list (A*B) -> Prop :=
  in_dom_head : forall b l, in_dom x ((x,b)::l)
| in_dom_queue : forall a b l,
    in_dom x l -> in_dom x ((a,b)::l).

Inductive distinct_key : list (A*B) -> Prop :=
  distinct_key_nil : distinct_key nil
| distinct_key_cons : forall a b l,
    ~ in_dom a l -> distinct_key l -> distinct_key ((a,b)::l).

Record dlist : Type := mk_dlist { 
  dlist_list :> list (A*B); 
  dlist_distinct_key :> distinct_key dlist_list }.

Definition dassoc x (l:dlist) := assoc Aeq x l.

Fixpoint dmodify_assoc_aux x l (f:option B->option B) {struct l} : list (A*B) :=
  match l with
    nil => match f None with
             None => nil
           | Some b => (x,b)::nil
           end
  | (a,b)::q => if (Aeq x a) then 
                  match f (Some b) with
                    None => q 
                  | Some b => (a,b)::q
                  end
                else (a,b)::(dmodify_assoc_aux x q f)
  end.

Lemma in_dom_dmodify_assoc_aux : forall l a x f,
   in_dom a (dmodify_assoc_aux x l f) ->
   x=a \/ in_dom a l.
Proof.
  induction l; simpl; intros.
  destruct (f None); inversion_clear H; auto.
  destruct a.
  assert (UU:= Aeq_spec x a);destruct (Aeq x a).
  subst; destruct (f (Some b)).
  inversion_clear H; auto.
  right; constructor 2; auto.
  right; constructor 2; auto.
  inversion_clear H.
  right; constructor 1; auto.
  destruct (IHl _ _ _ H0); subst; auto.
  right; right; auto.
Qed.


Lemma dmodify_assoc_aux_distinct_key : forall x l f,
  distinct_key l -> distinct_key (dmodify_assoc_aux x l f).
Proof.
  induction 1; simpl.
  destruct f; simpl; repeat constructor.
  intros H; inversion H.
  assert (UU:=Aeq_spec x a);destruct (Aeq x a); subst; simpl.
  destruct (f (Some b)); auto.
  constructor; auto.
  constructor; auto.
  intros H'; elim H.
  destruct (in_dom_dmodify_assoc_aux _ _ _ _ H'); intuition.
Qed.

Definition dmodify_assoc x (l:dlist) f : dlist :=
  mk_dlist (dmodify_assoc_aux x l f) (dmodify_assoc_aux_distinct_key x l f l).

Lemma assoc_not_in_dom : forall l x,
  ~ in_dom x l -> assoc Aeq x l = None.
Proof.
  induction l; simpl; intros; auto.
  destruct a.
  assert (UU := Aeq_spec x a);destruct (Aeq x a).
  elim H; subst; constructor 1.
  apply IHl; intro; elim H; constructor 2; auto.
Qed.

  Lemma assoc_dmodify_assoc_aux1 : forall l x f,
    distinct_key l ->
    assoc Aeq x (dmodify_assoc_aux x l f) = f (assoc Aeq x l).
  Proof.
    induction l; simpl; intros.
    destruct (f None); simpl; auto.
    assert (UU:= Aeq_spec x x); destruct  (Aeq x x);intuition.
    destruct a.
    assert (UU:= Aeq_spec x a); destruct (Aeq x a); subst; simpl.
    destruct f; simpl.
     assert (UU:= Aeq_spec a a); destruct  (Aeq a a);intuition.
    apply assoc_not_in_dom; inversion H; auto.
    assert (UU':= Aeq_spec x a);destruct (Aeq x a); inversion H; intuition.
  Qed.

  Lemma assoc_dmodify_assoc1 : forall (l:dlist) x f,
    dassoc x (dmodify_assoc x l f) = f (dassoc x l).
  Proof.
    unfold dassoc; destruct l; simpl; intros.
    apply assoc_dmodify_assoc_aux1; auto.
  Qed.

  Lemma assoc_dmodify_assoc_aux2 : forall l x a f,
    distinct_key l ->
    x <> a ->
    assoc Aeq x (dmodify_assoc_aux a l f) = assoc Aeq x l.
  Proof.
    induction l; simpl; intros.
    destruct f; simpl; auto.
    assert (UU:= Aeq_spec x a);destruct (Aeq x a); intuition.
    destruct a.
    assert (UU:= Aeq_spec a0 a);destruct (Aeq a0 a); subst; simpl; intuition.
    destruct f; simpl; auto.
    assert (UU:= Aeq_spec x a);destruct (Aeq x a); intuition.
    assert (UU:= Aeq_spec x a);destruct (Aeq x a); intuition.
    assert (UU':= Aeq_spec x a);destruct (Aeq x a); intuition.
   inversion_clear H;auto.
  Qed.

  Lemma assoc_dmodify_assoc2 : forall (l:dlist) x a f,
    x <> a ->
    dassoc x (dmodify_assoc a l f) = dassoc x l.
  Proof.
    unfold dassoc; destruct l; simpl; intros.
    apply assoc_dmodify_assoc_aux2; auto.
  Qed.

  Definition dnil : dlist := mk_dlist nil distinct_key_nil.

  Lemma assoc_dnil : forall x, assoc Aeq x dnil = None.
  Proof.
    unfold dnil; simpl; auto.
  Qed.

  Lemma in_in_dom : forall a b l, In (a,b)l -> in_dom a l.
  Proof.
    induction l; simpl; intuition;
    subst; constructor; auto.
  Qed.

  Lemma in_dassoc_prop1 : forall x b (l:dlist),
    In (x,b) l -> dassoc x l = Some b.
  Proof.
    destruct l as [l Hl]; unfold dassoc.
    induction l; simpl; intros.
    elim H.
    destruct H; subst.
    assert (UU:= Aeq_spec x x);destruct (Aeq x x); intuition.
    destruct a.
    assert (UU:= Aeq_spec x a);destruct (Aeq x a); subst.
    inversion_clear Hl.
    elim H0; apply in_in_dom with b; auto.
    simpl in IHl.
    rewrite IHl; auto.
    inversion_clear Hl; auto.
  Qed.

  Lemma in_assoc_prop : forall x b l, 
    assoc Aeq x l = Some b -> In (x,b) l.
  Proof.
    induction l; simpl; intros.
    discriminate.
    destruct a.
    assert (UU:=Aeq_spec x a);destruct (Aeq x a).
    injection H; intros; subst; auto.
    auto.
  Qed.

  Lemma in_dassoc_prop2 : forall x b (l:dlist), 
    dassoc x l = Some b -> In (x,b) l.
  Proof.
    destruct l as [l Hl]; simpl; intros.
    apply in_assoc_prop; auto.
  Qed.

End assoc_distinct.

Implicit Arguments dmodify_assoc.
Implicit Arguments dassoc.

Section for_all.

  Variable A : Type.
  Variable test : A -> bool.

  Definition for_all (l:list A) : bool := 
    fold_right
    (fun a => andb (test a)) true l.

  Lemma for_all_true : forall l,
    for_all l = true -> forall a, In a l -> test a = true.
  Proof.
    induction l; simpl; intros.
    elim H0.
    destruct (andb_prop _ _ H).
    destruct H0; subst; auto.
  Qed.

  Lemma for_all_correct : forall l,
    if for_all l
      then forall a, In a l -> test a = true
      else ~ forall a, In a l -> test a = true.
  Proof.
    induction l; simpl; intros.
    elim H.
    case_eq (test a); simpl; intros.
    destruct (for_all l); intuition.
    subst; auto.
    intuition.
    rewrite H0 in H; auto; discriminate.
  Qed.


End for_all.


  Definition dlist_for_all (A B:Type) (test:A->B->bool) (l:dlist A B) : bool := 
    for_all (A*B) (fun p => test (fst p) (snd p)) l.

  Lemma dlist_for_all_correct : forall A B (Aeq : A -> A -> bool),
    (forall x y, if Aeq x y then x = y else x <> y) ->
    forall test l,
    if dlist_for_all A B test l 
    then forall a b, dassoc Aeq a l = Some b -> test a b = true
    else ~ forall a b, dassoc Aeq a l = Some b -> test a b = true.
  Proof.
    intros; unfold dlist_for_all.
    generalize (for_all_correct _ (fun p : A * B => test (fst p) (snd p)) l);
      destruct (for_all _ (fun p : A * B => test (fst p) (snd p)) l); simpl; intros.
    apply (H0 (a,b)).
    eapply in_assoc_prop; eauto.
    intro; elim H0; clear H0; intros.
    destruct a; simpl.
    apply H1.
    apply in_dassoc_prop1; auto.
  Qed.

Definition compare (A B:Type) (Aeq : A -> A -> bool)
  (test:option B->option B->bool) (l1 l2:dlist A B) : bool :=
  dlist_for_all A B (fun k a1 => test (Some a1) (dassoc Aeq k l2)) l1
  &&
  dlist_for_all A B (fun k a2 => test (dassoc Aeq k l1)  (Some a2)) l2.

  Lemma compare_correct : forall A B (Aeq : A -> A -> bool),
    (forall x y, if Aeq x y then x = y else x <> y) ->
    forall f l1 l2,
    f None None = true ->
    if compare A B Aeq f l1 l2
      then forall k, f (dassoc Aeq k l1) (dassoc Aeq k l2) = true
      else ~ forall k, f (dassoc Aeq k l1) (dassoc Aeq k l2) = true.
  Proof.
    unfold compare; intros.
    generalize (dlist_for_all_correct A B Aeq H (fun (k : A) (a1 : B) => f (Some a1) (dassoc Aeq k l2)) l1);
      destruct (dlist_for_all A B (fun (k : A) (a1 : B) => f (Some a1) (dassoc Aeq k l2)) l1); simpl; intros.
    generalize (dlist_for_all_correct A B Aeq H (fun (k : A) (a2 : B) => f (dassoc Aeq k l1) (Some a2)) l2);
      destruct (dlist_for_all A B (fun (k : A) (a2 : B) => f (dassoc Aeq k l1) (Some a2)) l2); simpl; intros.
    generalize (H1 k); clear H1; generalize (H2 k); clear H2; intros.
    destruct (dassoc Aeq k l1); auto.
    destruct (dassoc Aeq k l2); auto.
    intro; elim H2; clear H2; intros.
    rewrite <- H2; auto.
    intro; elim H1; clear H1; intros.
    rewrite <- H1; auto.
  Qed.



