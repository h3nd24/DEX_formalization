
Require Import EqBoolAux.
Require Export ListAux.
Require Import Bool.

Module Type MAP_BASE.
 
  Parameter t : Type -> Type.
  Parameter key : Set.
  Parameter eq_key : key -> key -> bool.
  Parameter eq_key_spec :
      forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Parameter key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2. 

  Parameter get : forall A:Type, t A -> key -> option A.
  Parameter modify : forall A:Type, t A -> key -> (option A -> option A) -> t A.

  Parameter get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Parameter get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.

  Parameter empty : forall (A:Type), t A.
  Parameter get_empty : forall A k, get A (empty A) k = None.

  Parameter elements : forall A, t A -> list (key*A).
  Parameter in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a.
  Parameter get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).

  Parameter fold : forall (A B:Type), 
   (key->A->B->B) -> t A -> B -> B.
  Parameter fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.

  Parameter compare : forall (A:Type), (option A -> option A -> bool) -> t A -> t A -> bool.
  Parameter compare_correct : forall A comp t1 t2,
    comp None None = true ->
    if compare A comp t1 t2
      then forall k, comp (get A t1 k) (get A t2 k) = true
      else ~ forall k, comp (get A t1 k) (get A t2 k) = true.

  Implicit Arguments get.
  Implicit Arguments modify.
  Implicit Arguments empty.
  Implicit Arguments elements.
  Implicit Arguments fold.
  Implicit Arguments compare.

End MAP_BASE.

Module Type MAP.
 
  Parameter t : Type -> Type.
  Parameter key : Set.  
  Parameter eq_key : key -> key -> bool.
  Parameter eq_key_spec :
      forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.

  Parameter key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2. 

  Parameter get : forall A:Type, t A -> key -> option A. 
  Parameter modify : forall A:Type, t A -> key -> (option A -> option A) -> t A.
  Parameter update : forall A:Type, t A -> key -> A -> t A.

  Parameter get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Parameter get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.

  Parameter get_update1 : forall A t k v,
    get A (update A t k v) k = Some v.
  Parameter get_update2 : forall A t k1 k2 v,
    k1 <> k2 ->
    get A (update A t k2 v) k1 = get A t k1.

  Parameter empty : forall (A:Type), t A.
  Parameter get_empty : forall A k, get A (empty A) k = None.

  Parameter elements : forall A, t A -> list (key*A).
  Parameter in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a.
  Parameter get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).

  Parameter fold : forall (A B:Type), 
   (key->A->B->B) -> t A -> B -> B.
  Parameter fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.

  Parameter dom : forall A, t A -> list key.
  Parameter in_dom_get_some : forall A m p,
    In p (dom A m) -> get A m p <> None.
  Parameter get_some_in_dom : forall A m p,
    get A m p <> None -> In p (dom A m).
  Parameter domain_inv : forall A m v p, 
    In p (dom A m) -> dom A (update A m p v) = dom A m.

  Parameter for_all : forall A : Type, (key -> A -> bool) -> t A -> bool.
  Parameter for_all_spec : forall (A : Type) (test:key -> A -> bool) (m : t A),
    if for_all A test m 
      then forall k a, get A m k = Some a -> test k a = true
      else ~forall k a, get A m k = Some a -> test k a = true.
  Parameter spec_all_for_true : forall (A : Type) (test:key -> A -> bool) (m : t A),
    (forall k a, get A m k = Some a -> test k a = true) -> for_all A test m = true.
  Parameter for_all_true : forall (A : Type) (test:key -> A -> bool) (m : t A),
    for_all A test m = true -> forall k a, get A m k = Some a -> test k a = true.
  Parameter for_all_false : forall (A : Type) (test:key -> A -> bool) (m : t A),
    for_all A test m = false -> ~forall k a, get A m k = Some a -> test k a = true.

  Parameter compare : forall (A:Type), (option A -> option A -> bool) -> t A -> t A -> bool.
  Parameter compare_correct : forall A comp t1 t2,
    comp None None = true ->
    if compare A comp t1 t2
      then forall k, comp (get A t1 k) (get A t2 k) = true
      else ~ forall k, comp (get A t1 k) (get A t2 k) = true.

  Definition Equals (A:Type) (t1 t2:t A) : Prop :=
    forall k, get A t1 k = get A t2 k.

  Definition Empty (A:Type) (t:t A) : Prop :=
    forall k, get A t k = None.

  Parameter equals : forall (A:Type), (A->A->bool) -> t A -> t A -> bool.
  Parameter equals_correct : forall (A:Type) (Aeq:A->A->bool),
    (forall x y, if Aeq x y then x = y else x <> y) ->
    forall t1 t2, 
      if equals A Aeq t1 t2
        then Equals A t1 t2
        else ~ Equals A t1 t2.

  Parameter empty_test : forall (A:Type), t A -> bool.
  Parameter empty_test_correct : forall (A:Type) t, 
      if empty_test A t
        then Empty A t
        else ~ Empty A t.
  
(*
  Parameter search : forall A:Type, (key->A->bool) -> t A -> option (key*A).
  Parameter search_succed : forall A test (m:t A) k a,
    search A test m = Some (k,a) ->
    get A m k = Some a /\ test k a = true.
  Parameter search_failed : forall A test (m:t A),
    search A test m = None ->
    forall a k, get A m k = Some a -> test k a = false.
*)

  Implicit Arguments get.
  Implicit Arguments modify.
  Implicit Arguments update.
  Implicit Arguments empty.
  Implicit Arguments elements.
  Implicit Arguments fold.
  Implicit Arguments dom.
  Implicit Arguments for_all.
  Implicit Arguments compare.
  Implicit Arguments Equals.
  Implicit Arguments Empty.
  Implicit Arguments equals.
  Implicit Arguments empty_test.
(*  Implicit Arguments search. *)

End MAP.

Module Map_Of_MapBase (M:MAP_BASE) <: MAP
  with Definition t := M.t
  with Definition key := M.key.

  Definition t := M.t.
  Definition key := M.key.
  Definition eq_key := M.eq_key.
  Definition eq_key_spec := M.eq_key_spec.
  Definition key_dec := M.key_dec.

  Definition get := M.get.
  Definition modify := M.modify.
  Definition update (A:Type)(m:t A)(k:key)(v:A) : t A :=
    M.modify m k (fun _ => Some v).
  Definition get_modify1 := M.get_modify1.
  Definition get_modify2 := M.get_modify2.

  Lemma get_update1 : forall A t k v,
    get A (update A t k v) k = Some v.
  Proof.
    intros; unfold get, update.
    rewrite get_modify1; reflexivity.
  Qed.

  Lemma get_update2 : forall A t k1 k2 v,
    k1 <> k2 ->
    get A (update A t k2 v) k1 = get A t k1.
  Proof.
    intros; unfold get, update.
    rewrite get_modify2; auto.
  Qed.

  Definition empty := M.empty.
  Definition get_empty := M.get_empty.
  Definition elements := M.elements.
  Definition in_elements_get_some := M.in_elements_get_some.
  Definition get_some_in_elements := M.get_some_in_elements.
  Definition fold := M.fold.
  Definition fold_prop := M.fold_prop.

  Definition dom (A:Type)(m:t A) : list key := 
    M.fold (fun k a l => k::l) m nil.

  Lemma in_fold_cons : forall (A:Type) k l,
    In k (fold_right
           (fun (pa : M.key * A) (b0 : list key) =>
            let (p0, _) := pa in p0 :: b0) nil l) ->
    exists a, In (k,a) l.
  Proof.
    intros until l.
    rewrite <- (fold_right_eq2 _ _ (fun (pa:key*A) b0 => (fst pa)::b0)).
    rewrite in_fold_cons; intros.
    destruct (in_map_inv _ _ _ _ _ H).
    destruct x; simpl in *; intuition; subst; eauto.
    destruct a; simpl; auto.
  Qed.

  Lemma in_fold_cons_inv : forall (A:Type) k l a,
    In (k,a) l ->
    In k (fold_right
           (fun (pa : M.key * A) (b0 : list key) =>
            let (p0, _) := pa in p0 :: b0) nil l).
  Proof.
    intros.
    rewrite <- (fold_right_eq2 _ _ (fun (pa:key*A) b0 => (fst pa)::b0)).
    rewrite ListAux.in_fold_cons.    
    replace k with (fst (k,a)); auto.
    apply in_map; auto.
    destruct a0; simpl; auto.
  Qed.

  Lemma in_dom_get_some : forall A m p,
    In p (dom A m) -> get A m p <> None.
  Proof.
    intros.
    unfold dom in H; rewrite <- fold_prop in H.
    destruct (in_fold_cons _ _ _ H) as [a H1].
    unfold get; rewrite (in_elements_get_some A m p a); auto.
    discriminate.
  Qed.

  Lemma get_some_in_dom : forall A m p,
    get A m p <> None -> In p (dom A m).
  Proof.
    intros.
    unfold dom; rewrite <- fold_prop.
    generalize (get_some_in_elements A m p).
    generalize H; clear H.
    unfold get; case (M.get m p); intros.
    apply (in_fold_cons_inv _ _ _ _ (H0 a (refl_equal _))).
    elim H; auto.
  Qed.

  Variable domain_inv : forall A m v p, 
    In p (dom A m) -> dom A (update A m p v) = dom A m.

  Section for_all.

    Variable A : Type.
    Variable test : key -> A -> bool.

    Definition for_all (m:t A) : bool := 
      M.fold (fun k a => andb (test k a)) m true.

    Lemma for_all_spec_aux : forall l,
      if fold_right
      (fun (pa:key*A) b0 => let (p0, a) := pa in test p0 a && b0) true l 
      then forall k a, In (k,a) l -> test k a = true
      else ~ forall k a, In (k,a) l -> test k a = true.
    Proof.
      induction l; simpl; intros.
      elim H.
      destruct a.
      case_eq (test k a); simpl; intros.
      destruct (fold_right
             (fun (pa : key * A) (b0 : bool) =>
              let (p0, a) := pa in test p0 a && b0) true l);
      intuition.
      inversion H1; subst; auto.
      intuition.
      generalize (H0 k a); rewrite H; intros.
      assert (false=true); auto; discriminate.    
    Qed.

Lemma spec_all_for_aux : forall l,
  (forall k a, In (k,a) l -> test k a = true) ->
  (fold_right (fun (pa:key*A) b0 => let (p0, a) := pa in test p0 a && b0) true l = true).
Proof.
  intro l. induction l as [|x xs]. auto.
  intros. destruct x.
  replace (fold_right
  (fun (pa : key * A) (b0 : bool) => let (p0, a) := pa in test p0 a && b0)
  true ((k,a) :: xs)) with
  (test (k) (a) && fold_right
  (fun (pa : key * A) (b0 : bool) => let (p0, a) := pa in test p0 a && b0)
  true (xs)); auto. apply andb_true_intro; auto. split.
  apply H. left; auto. apply IHxs. intros k' a' I.
  apply H. apply in_cons; auto.
Qed.

Lemma spec_all_for_true : forall m,
      (forall k a, get A m k = Some a -> test k a = true) -> 
      for_all m = true.
    Proof.
      intro m. unfold for_all. intros.
      rewrite <- fold_prop.
      apply spec_all_for_aux.
      intros. apply in_elements_get_some in H0.
      generalize H0. auto.
Qed.

    Lemma for_all_spec : forall m,
      if for_all m 
        then forall k a, get A m k = Some a -> test k a = true
        else ~ forall k a, get A m k = Some a -> test k a = true.
    Proof.
      unfold for_all; intros.
      rewrite <- fold_prop.
      generalize (for_all_spec_aux (M.elements m)). unfold key.
        destruct (fold_right
         (fun (pa : M.key * A) (b0 : bool) =>
          let (p0, a) := pa in test p0 a && b0) true 
         (M.elements m)); intros.
      apply H.
      apply get_some_in_elements; auto.
      intro; elim H; clear H; intros.
      apply H0; apply in_elements_get_some; auto.
    Qed.

    Lemma for_all_true : forall (m : t A),
      for_all m = true -> forall k a, get A m k = Some a -> test k a = true.
    Proof.
      intros.
      generalize (for_all_spec m); rewrite H; auto.
    Qed.

    Lemma for_all_false : forall (m : t A),
      for_all m = false -> ~forall k a, get A m k = Some a -> test k a = true.
    Proof.
      intros.
      generalize (for_all_spec m); rewrite H; auto.
    Qed.

  End for_all.

  Definition compare := M.compare.
  Definition compare_correct := M.compare_correct.

  Definition Equals (A:Type) (t1 t2:t A) : Prop :=
    forall k, get A t1 k = get A t2 k.

  Definition Empty (A:Type) (t:t A) : Prop :=
    forall k, get A t k = None.

  Definition equals : forall (A:Type) (Aeq:A->A->bool), t A -> t A -> bool :=
    fun A Aeq =>
      compare _ 
        (fun x y => 
          match x, y with
            | None, None => true
            | None, _ => false
            | Some _, None => false
            | Some x, Some y => Aeq x y
          end)  .

  Lemma equals_correct : forall (A:Type) (Aeq:A->A->bool),
    (forall x y, if Aeq x y then x = y else x <> y) ->
    forall t1 t2, 
      if equals A Aeq t1 t2
        then Equals A t1 t2
        else ~ Equals A t1 t2.
  Proof.
    unfold equals, Equals, compare, get; intros.
    set (f:=(fun x y : option A =>
         match x with
         | Some x0 => match y with
                      | Some y0 => Aeq x0 y0
                      | None => false
                      end
         | None => match y with
                   | Some _ => false
                   | None => true
                   end
         end)).
    generalize (M.compare_correct A f t1 t2); destruct (M.compare f t1 t2); intros.
    generalize (H0 (refl_equal _) k).
    unfold f; destruct (M.get t1 k); destruct (M.get t2 k); simpl; intros; try discriminate.
    generalize (H a a0); rewrite H1; intros; subst; auto.
    auto.
    intro; elim H0; clear H0; auto.
    intros k; rewrite (H1 k).
    destruct (M.get t2 k); simpl; auto.
    generalize (H a a); destruct (Aeq a a); auto.
  Qed.

  Definition empty_test : forall (A:Type), t A -> bool :=
    fun A m => fold A bool (fun _ _ _ => false) m true.

  Lemma empty_test_correct_aux : forall (A:Type) l,
    if fold_right
      (fun (pa : M.key * A) (_ : bool) => let (_, _) := pa in false) true l 
      then l = nil else l <> nil.
  Proof.
    induction l; simpl; auto.
    destruct a.
    discriminate.
  Qed.

  Lemma empty_test_correct : forall (A:Type) t, 
    if empty_test A t
      then Empty A t
      else ~ Empty A t.
  Proof.
    unfold empty_test, Empty, get; intros.
    rewrite <- fold_prop.
    generalize (empty_test_correct_aux A (M.elements t0));
      destruct (fold_right
        (fun (pa : M.key * A) (_ : bool) => let (_, _) := pa in false) true
        (M.elements t0)); intros.
    case_eq (M.get t0 k); intros; auto.
    generalize (get_some_in_elements _ _ _ _ H0); rewrite H; intros H2; elim H2.
    intro; elim H; clear H.
    case_eq (M.elements t0); auto.
    intros (k,a) l H.
    generalize (H0 k); rewrite (in_elements_get_some A t0 k a).
    intros; discriminate.
    rewrite H; left; auto.
  Qed.

End Map_Of_MapBase.

Module Type MAP_BOT_BASE.
 
  Parameter t : Type -> Type.
  Parameter key : Set.
  Parameter key_dec : forall k1 k2:key, {k1=k2}+{~k1=k2}.

  Parameter get : forall A:Type, A -> t A -> key -> A.
  Parameter modify : forall A:Type, A -> t A -> key -> (A -> A) -> t A.

  Parameter get_modify1 : forall A bot t k f,
    get A bot (modify A bot t k f) k = f (get A bot t k).
  Parameter get_modify2 : forall A bot t k1 k2 f,
    k1 <> k2 ->
    get A bot (modify A bot t k2 f) k1 = get A bot t k1.

  Parameter init : forall (A:Type), A -> t A.
  Parameter get_init : forall A bot k, get A bot (init A bot) k = bot.

End MAP_BOT_BASE.

Module Type MAP_BOT.
 
  Parameter t : Type -> Type.
  Parameter key : Set.
  Parameter key_dec : forall k1 k2:key, {k1=k2}+{~k1=k2}.

  Parameter get : forall A:Type, A -> t A -> key -> A.
  Parameter modify : forall A:Type, A -> t A -> key -> (A -> A) -> t A.
  Parameter update : forall A:Type, A -> t A -> key -> A -> t A.

  Parameter get_modify1 : forall A bot t k f,
    get A bot (modify A bot t k f) k = f (get A bot t k).
  Parameter get_modify2 : forall A bot t k1 k2 f,
    k1 <> k2 ->
    get A bot (modify A bot t k2 f) k1 = get A bot t k1.

  Parameter get_update1 : forall A bot t k v,
    get A bot (update A bot t k v) k = v.
  Parameter get_update2 : forall A bot t k1 k2 v,
    k1 <> k2 ->
    get A bot (update A bot t k2 v) k1 = get A bot t k1.

  Parameter init : forall (A:Type), A -> t A.
  Parameter get_init : forall A bot k, get A bot (init A bot) k = bot.

End MAP_BOT.

Module MapBot_Of_MapBotBase (M:MAP_BOT_BASE) <: MAP_BOT
  with Definition t := M.t
  with Definition key := M.key.

  Definition t := M.t.
  Definition key := M.key.
  Definition key_dec := M.key_dec.
  Definition get := M.get.
  Definition modify := M.modify.
  Definition update (A:Type)(bot:A)(m:t A)(k:key)(v:A) : t A :=
    M.modify A bot m k (fun _ => v).
  Definition get_modify1 := M.get_modify1.
  Definition get_modify2 := M.get_modify2.

  Lemma get_update1 : forall A bot t k v,
    get A bot (update A bot t k v) k = v.
  Proof.
    intros; unfold get, update.
    rewrite get_modify1; reflexivity.
  Qed.

  Lemma get_update2 : forall A bot t k1 k2 v,
    k1 <> k2 ->
    get A bot (update A bot t k2 v) k1 = get A bot t k1.
  Proof.
    intros; unfold get, update.
    rewrite get_modify2; auto.
  Qed.

  Definition init := M.init.
  Definition get_init := M.get_init.

End MapBot_Of_MapBotBase.

Module Type MAP_PROJ.
  Parameter element : Type. 
  Parameter key : Set.  
  Parameter proj : element -> key.
  Parameter t : Type.
  
  Parameter eq_key : key -> key -> bool.
  Parameter eq_key_spec :
      forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.

  Parameter key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2. 

  Parameter get : t -> key -> option element. 

  Parameter update : t -> element -> t.

  Parameter get_proj : forall t k v, get t k = Some v -> proj v = k.
  Parameter get_update1 : forall t v,
    get (update t v) (proj v) = Some v.
  Parameter get_update2 : forall t k v,
    k <> proj v ->
    get (update t v) k = get t k.

  Parameter empty : t.
  Parameter get_empty : forall k, get empty k = None.

  Parameter elements_tr : t -> list element -> list element.

  Parameter in_elements_tr : forall t res a,  
    In a (elements_tr t res) -> 
    (exists k, get t k = Some a) \/ In a res.
  Parameter get_some_in_elements_tr : forall t res a,
    (exists k, get t k = Some a) \/ In a res -> 
    In a (elements_tr t res).

  Parameter elements : t -> list element.
  Parameter in_elements_get_some : forall m a,
    In a (elements m) -> get m (proj a) = Some a.
  Parameter get_some_in_elements : forall m p a,
    get m p = Some a -> In a (elements m).

End MAP_PROJ.

Module MapProjTools (M:MAP_PROJ).
  Import M.

  Definition for_all (test:element->bool) m := for_all _ test (elements m).

  Lemma for_all_true : forall test m,
    for_all test m = true -> 
    forall a,
      get m (proj a) = Some a -> test a = true.
  Proof.
    intros.
    apply (for_all_true _ _ _ H).
    apply get_some_in_elements with (1:=H0).
  Qed.

End MapProjTools.