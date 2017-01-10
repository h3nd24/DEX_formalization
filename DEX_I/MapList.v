Require Export ZArith.
Require Export PosAux.
Require Export List.
Require Export Bool.

Module Type MAPLIST.
 
  Parameter t : Type -> Type.
  Parameter key : Set.  
  Parameter eq_key : key -> key -> bool.
  Parameter eq_key_spec :
      forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.

  Parameter key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2. 

  Parameter get : forall A:Type, t A -> key -> option A. 
  Parameter update : forall A:Type, t A -> key -> A -> t A.

  Parameter get_update1 : forall A t k v,
    get A (update A t k v) k = Some v.
  Parameter get_update2 : forall A t k1 k2 v,
    k1 <> k2 ->
    get A (update A t k2 v) k1 = get A t k1.

  Parameter empty : forall (A:Type), t A.
  Parameter get_empty : forall A k, get A (empty A) k = None.

  Parameter fold : forall (A B:Type), 
   (key->A->B->B) -> t A -> B -> B.

  Parameter dom : forall A, t A -> list key.
  Parameter in_dom_get_some : forall A m p,
    In p (dom A m) -> get A m p <> None.
  Parameter get_some_in_dom : forall A m p,
    get A m p <> None -> In p (dom A m).
  Parameter domain_inv : forall A m v p, 
    In p (dom A m) -> dom A (update A m p v) = dom A m.

  Parameter for_all : forall A : Type, (key -> A -> bool) -> t A -> bool.
  Parameter for_all_true : forall (A : Type) (test:key -> A -> bool) (m : t A),
    for_all A test m = true -> forall k a, get A m k = Some a -> test k a = true.

  Definition Empty (A:Type) (t:t A) : Prop :=
    forall k, get A t k = None.

  Implicit Arguments get.
  Implicit Arguments update.
  Implicit Arguments empty.
  Implicit Arguments fold.
  Implicit Arguments dom.
  Implicit Arguments Empty.

End MAPLIST.

Module MapList_Base <: MAPLIST with Definition key:=N.

  Definition key := N.
  Definition t A := list (key * A).
  Definition eq_key := Neq.
  Lemma eq_key_spec : forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Proof. exact Neq_spec. Qed.

  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof.
   intros k1 k2;generalize (eq_key_spec k1 k2);destruct (eq_key k1 k2);auto.
  Qed.

  Fixpoint get (A:Type) (l:t A) (k:key) := 
    match l with
      | nil => None
      | h :: t => if Neq k (fst h) then Some (snd h) else get A t k
    end.

  Fixpoint update (A:Type) (l:t A) (k:N) (v:A) : t A :=
    match l with
      | nil => (k, v) :: nil
      | h :: t => if Neq k (fst h) then (k, v) :: t else h :: (update A t k v)
    end.

  Lemma get_update1 : forall A t k v,
    get A (update A t k v) k = Some v.
  Proof.
    induction t0; intros.
    simpl. rewrite Neq_refl. auto.
    simpl. 
    generalize (Neq_spec k (fst a));destruct (Neq k (fst a)) eqn:Heq; intros.
    simpl. rewrite Neq_refl; auto.
    simpl. rewrite Heq. apply IHt0.
  Qed.

  Lemma get_update2 : forall A t k1 k2 v,
    k1 <> k2 ->
    get A (update A t k2 v) k1 = get A t k1.
  Proof.
    induction t0; intros.
    simpl. generalize (Neq_spec k1 k2);destruct (Neq k1 k2) eqn:Heq; intros; auto.
      contradiction.
    simpl. 
    generalize (Neq_spec k2 (fst a));destruct (Neq k2 (fst a)) eqn:Heq; intros.
    simpl.
    generalize (Neq_spec k1 k2);destruct (Neq k1 k2) eqn:Heq'; intros. contradiction.
    generalize (Neq_spec k1 (fst a));destruct (Neq k1 (fst a)) eqn:Heq''; intros.
    rewrite <- H0 in H2; contradiction.
    auto.
    simpl.
    generalize (Neq_spec k1 (fst a));destruct (Neq k1 (fst a)) eqn:Heq''; intros; auto.
  Qed.

  Definition empty (A:Type) := @nil (key * A).
  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    unfold empty. auto.
  Qed.

  Definition fold (A B:Type) (f:key->A->B->B) (l:t A) (acc:B) := 
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0) acc l.

  Fixpoint dom (A:Type) (l:t A) :=
    match l with
      | nil => nil
      | h :: t => (fst h) :: (dom A t)
    end.

  Lemma in_dom_get_some_aux : forall A m p, get A m p = None -> ~In p (dom A m).
  Proof.
    induction m.
    unfold not; intros. inversion H0.
    unfold not; simpl; intros.
    generalize (Neq_spec (fst a) p); destruct (Neq (fst a) p) eqn:Heq; intros.
    subst. rewrite Neq_refl in H. inversion H.
    rewrite Neq_sym in Heq.
    rewrite Heq in H. apply IHm in H. inversion H0; auto.
  Qed.

  Lemma in_dom_get_some : forall A m p,
    In p (dom A m) -> get A m p <> None.
  Proof.
    unfold not; intros.
    apply in_dom_get_some_aux in H0. auto.
  Qed.
  
  Lemma in_dom_get_some' : forall A m p,
    In p (dom A m) -> exists v, get A m p = Some v.
  Proof.
    intros. apply in_dom_get_some in H.
    destruct (get A m p). exists a; auto.
      apply False_ind; auto.
  Qed.

  Lemma get_some_in_dom' : forall A m p v,
    get A m p = Some v -> In p (dom A m).
  Proof.
    induction m.
    intros. inversion H.
    intros. inversion H.
    destruct (Neq p (fst a)) eqn:Heq.
    left. generalize (Neq_spec p (fst a)). rewrite Heq; intros; subst; auto.
    right; apply IHm with (v:=v); auto.
  Qed.

  Lemma get_some_in_dom : forall A m p,
    get A m p <> None -> In p (dom A m).
  Proof.
    intros.
    assert (exists v, get A m p = Some v). destruct (get A m p). exists a; auto.
      apply False_ind; auto.
    destruct H0. apply get_some_in_dom' in H0; auto.
  Qed.

  Lemma domain_inv : forall A m v p, 
    In p (dom A m) -> dom A (update A m p v) = dom A m.
  Proof.
    induction m; intros.
    inversion H.
    simpl.
    generalize (Neq_spec (fst a) p); destruct (Neq (fst a) p) eqn:Heq; intros.
    subst. rewrite Neq_refl; auto.
    inversion H. contradiction.
    rewrite Neq_sym in Heq; rewrite Heq. simpl.
    apply IHm with (v:=v) in H1; rewrite H1; auto.
  Qed.

  Fixpoint for_all (A:Type) (f:key -> A -> bool) (l:t A) := 
    match l with
      | nil => true
      | (k, v) :: l' => (f k v) && (for_all A f l')
    end.

  Lemma for_all_true : forall (A : Type) (test:key -> A -> bool) (m : t A),
    for_all A test m = true -> forall k a, get A m k = Some a -> test k a = true.
  Proof.
    induction m; simpl; intros.
    inversion H0. destruct a.
    elim (andb_prop _ _ H); intros; auto.
    simpl in H0.
    generalize (Neq_spec k k0); destruct (Neq k k0) eqn:Heq; intros. 
    inversion H0. subst. auto.
    apply IHm; auto.
  Qed.

  Definition Empty (A:Type) (t:t A) : Prop :=
    forall k, get A t k = None.

  Implicit Arguments get.
  Implicit Arguments update.
  Implicit Arguments empty.
  Implicit Arguments fold.
  Implicit Arguments dom.
  Implicit Arguments for_all.

End MapList_Base.

Module MapList <: MAPLIST  with Definition key := N := MapList_Base.