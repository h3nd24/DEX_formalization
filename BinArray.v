Add LoadPath "..".
Require Import PosAux.
Require Import EqBoolAux.
Require Import Bool.
Require Export BinArrayBot.

Section dom.
Variable A B : Type.

Fixpoint inv_pos (p1 p2:positive) {struct p1} : positive :=
 match p1 with
  | xH => p2
  | (xO p) => (inv_pos p (xO p2))
  | (xI p) => (inv_pos p (xI p2))
 end.

Fixpoint elements_rec (t : tree (option A)) (p:positive) (acc:list (positive*A)) {struct t} : list (positive*A) :=
  match t with
  | leaf => acc
  | node None tO tI =>
      elements_rec tI (xI p) (elements_rec tO (xO p) acc)
  | node (Some a) tO tI =>
      elements_rec tI (xI p) (cons ((inv_pos p xH),a) (elements_rec tO (xO p) acc))
end.

Lemma in_elements_rec_in_acc :
 forall (t1 : tree (option A)) p q acc,
   In q acc ->
   In q (elements_rec t1 p acc).
Proof.
  induction t1 as [| a t0 IHt0 t2 IHt2]; simpl in |- *;
   intros. 
   auto.
   destruct a; apply IHt2; auto.
   right; auto.
Qed.

Lemma in_elements_rec_in_dom :
 forall (t1 : tree _) p q acc a,
   apply_tree _ None t1 p = Some a ->
   In ((inv_pos q p),a) (elements_rec t1 q acc).
Proof.
  induction t1 as [| a t0 IHt0 t2 IHt2]; simpl in |- *;
  intros. 
  discriminate H.
  destruct a.
  destruct p.
  replace (inv_pos q (xI p)) with (inv_pos (xI q) p); auto.
  apply in_elements_rec_in_acc; right; auto.
  replace (inv_pos q (xO p)) with (inv_pos (xO q) p); auto.
  apply in_elements_rec_in_acc; left; auto.
  injection H; intros; subst; auto.
  destruct p.
  replace (inv_pos q (xI p)) with (inv_pos (xI q) p); auto.
  apply in_elements_rec_in_acc; auto.
  replace (inv_pos q (xO p)) with (inv_pos (xO q) p); auto.
  discriminate H.
Qed.

Lemma in_elements_rec_in_dom_inv :
 forall (t1 : tree _) p' a' q acc,
   In (p',a') (elements_rec t1 q acc) ->
   (exists p, p' = (inv_pos q p)
     /\ apply_tree _ None t1 p = Some a')
   \/ In (p',a') acc.
Proof.
  induction t1 as [| a t0 IHt0 t2 IHt2]; simpl in |- *;
  intros. 
  intuition.
  destruct a.
  destruct (IHt2 _ _ _ _ H).
  destruct H0 as [p [H1 H2]].
  left; exists (xI p); split; auto.
  destruct H0.
  injection H0; intros.
  left; exists xH; intuition.
  subst; auto.
  destruct (IHt0 _ _ _ _ H0); clear H0.
  destruct H1 as [p [H3 H2]].
  left; exists (xO p); split; auto.
  auto.
  destruct (IHt2 _ _ _ _ H).
  destruct H0 as [p [H1 H2]].
  left; exists (xI p); split; auto.
  destruct (IHt0 _ _ _ _ H0); clear H0.
  destruct H1 as [p [H3 H2]].
  left; exists (xO p); split; auto.
  auto.
Qed.

Definition elements (t : tree (option A)) := elements_rec t xH nil.

Lemma in_elements_prop1 : forall t1 p a,
   apply_tree _ None t1 p = Some a ->
   In (p,a) (elements t1).
Proof.
  unfold elements; intros.
  replace p with (inv_pos 1 p); auto.
  apply in_elements_rec_in_dom; auto.
Qed.

Lemma in_elements_prop2 : forall t1 p a,
  In (p,a) (elements t1) -> 
   apply_tree _ None t1 p = Some a.
Proof.
  unfold elements; intros.
  destruct (in_elements_rec_in_dom_inv _ _ _ _ _ H).
  destruct H0 as [q [H1 H2]].
  simpl in H1.
  subst; auto.
  elim H0.
Qed.

Variable f : positive -> A -> B -> B.

Fixpoint fold_rec (t : tree (option A)) (p:positive) (acc:B) {struct t} : B :=
  match t with
  | leaf => acc
  | node None tO tI =>
      fold_rec tI (xI p) (fold_rec tO (xO p) acc)
  | node (Some a) tO tI =>
      fold_rec tI (xI p) (f (inv_pos p xH) a (fold_rec tO (xO p) acc))
end.

Let f' := (fun (pa : positive * A) (b0 : B) => let (p0, a) := pa in f p0 a b0).

Lemma fold_rec_prop : forall t l b1 b2 p,
  fold_right f' b1 l = b2 ->
  fold_right f' b1 (elements_rec t p l)= fold_rec t p b2.
Proof.
  induction t; intros; simpl; auto.
  destruct a; auto.
  apply IHt2; simpl.
  replace (fold_rec t1 (xO p) b2)
    with (fold_right f' b1 (elements_rec t1 (xO p) l)); auto.
Qed.

Definition fold (t : tree (option A)) b :=
  fold_rec t xH b.

Lemma fold_prop : forall t b,
  fold_right f' b (elements t)= fold t b.
Proof.
  unfold fold, elements; intros.
  apply fold_rec_prop; auto.
Qed.

End dom.

Section compare.
  Variable A : Type.
  Variable test2 : option A -> option A -> bool.

  Section forall_test.
  Variable test1 : positive -> option A -> bool.

  Definition forall_test (t1 : tree (option A)) : bool :=
    fold _ _ (fun p a b => test1 p (Some a)  && b) t1 true.

  Lemma forall_test_fold_right_correct : forall l,
    if fold_right
        (fun (pa:positive*A) b0 =>let (p0, a) := pa in test1 p0 (Some a) && b0) true 
        l 
      then forall p a, In (p,a) l -> test1 p (Some a) = true
      else ~ forall p a, In (p,a) l -> test1 p (Some a) = true.
  Proof.
    induction l; simpl.
    intuition.
    destruct a as [p a].
    case_eq (test1 p (Some a)); simpl; intros.
    destruct (fold_right
             (fun (pa : positive * A) (b0 : bool) =>
              let (p0, a) := pa in test1 p0 (Some a) && b0) true l); simpl in *; intros.
    destruct H0; auto.
    inversion H0; subst; auto.
    intro; elim IHl; clear IHl; intros; auto.
    intro H1; rewrite H1 in H; auto; discriminate.
  Qed.

  Lemma forall_test_correct : forall t1,
    (forall k, test1 k None = true) ->
    if forall_test t1
      then forall k, test1 k (apply_tree _ None t1 k) = true
      else ~ forall k, test1 k (apply_tree _ None t1 k) = true.
  Proof.
    unfold forall_test; intros.
    rewrite <- fold_prop.
    generalize (forall_test_fold_right_correct (elements A t1)).
    destruct (fold_right
         (fun (pa : positive * A) (b0 : bool) =>
          let (p0, a) := pa in test1 p0 (Some a) && b0) true 
         (elements A t1)); intros.
    case_eq (apply_tree (option A) None t1 k); simpl; auto.
    intros; apply H0.
    eapply in_elements_prop1; eauto.
    intro; elim H0; clear H0; intros.
    rewrite <- (in_elements_prop2 _ _ _ _ H0); auto.
  Qed.
  End forall_test.

  Fixpoint compare (t1 t2 : tree (option A)) {struct t1} : bool :=
    match t1,t2 with
      | leaf,leaf => true
      | leaf,_ => forall_test (fun p => test2 None) t2
      | node _ _ _,leaf => forall_test (fun p x => test2 x None) t1
      | node a1 l1 r1, node a2 l2 r2 => 
        test2 a1 a2 && compare l1 l2 && compare r1 r2
    end.

  Lemma compare_correct : forall t1 t2,
    test2 None None = true ->
    if compare t1 t2
      then forall k, test2 (apply_tree _ None t1 k) (apply_tree _ None t2 k) = true
      else ~ forall k, test2 (apply_tree _ None t1 k) (apply_tree _ None t2 k) = true.
  Proof.
    induction t1; destruct t2; simpl; intros; auto.
    generalize (forall_test_correct (fun _ => test2 None)
        (node (option A) o t2_1 t2_2));
    destruct (forall_test (fun _ => test2 None)
        (node (option A) o t2_1 t2_2)); intros.
    destruct k.
    apply H0 with (k:=xI k); auto.
    apply H0 with (k:=xO k); auto.
    apply H0 with (k:=xH); auto.
    intro; elim H0; auto; clear H0.
    generalize (forall_test_correct (fun _ x => test2 x None)
        (node (option A) a t1_1 t1_2));
    destruct (forall_test (fun _ x => test2 x None)
        (node (option A) a t1_1 t1_2)); intros.
    destruct k.
    apply H0 with (k:=xI k); auto.
    apply H0 with (k:=xO k); auto.
    apply H0 with (k:=xH); auto.
    intro; elim H0; auto; clear H0.
    case_eq (test2 a o); simpl; intros.
    generalize (IHt1_1 t2_1); destruct (compare t1_1 t2_1); simpl; intros; clear IHt1_1.
    generalize (IHt1_2 t2_2); destruct (compare t1_2 t2_2); simpl; intros; clear IHt1_2.
    destruct k; auto.
    intro; elim H2; clear H2; intros; auto.
    apply H3 with (k:=xI k); auto.
    intro; elim H1; clear H1; intros; auto.
    apply H2 with (k:=xO k); auto.
    intros H1; rewrite (H1 xH) in H0; discriminate.
  Qed.

End compare.

Lemma positive_dec: forall p1 p2:positive, {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
Qed.


Module BinMap_Base <: MAP_BASE with Definition key := positive.

  Definition t A := tree (option A).
  Definition key := positive.
  Definition eq_key := Peq.

  Lemma eq_key_spec : forall x y, if eq_key x y then x = y else x <> y.
  Proof. exact Peq_spec. Qed.

  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof.
   intros k1 k2;generalize (eq_key_spec k1 k2);destruct (eq_key k1 k2);auto.
  Qed.

  Definition get (A:Type) := apply_tree (option A) None.
  Definition modify (A:Type) := modify_tree (option A) None.

  Lemma get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Proof.
    intros; unfold get, modify; rewrite apply_modify_tree1; auto.
  Qed.

  Lemma get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.
  Proof.
    intros; unfold get, modify; rewrite apply_modify_tree2; auto.    
  Qed.

  Definition empty (A:Type) := leaf (option A).
  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    unfold empty, get; simpl; intros; reflexivity.
  Qed.

  Definition elements : forall A, t A -> list (key*A) :=
   elements.
  Lemma in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a. 
  Proof in_elements_prop2.
  Lemma get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).
  Proof in_elements_prop1.

  Definition fold : forall (A B:Type), 
   (key->A->B->B) -> t A -> B -> B := fold.
  Lemma fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.
  Proof fold_prop.


  Definition compare : forall A, (option A->option A->bool) -> t A -> t A -> bool :=
    compare.

  Lemma compare_correct : forall A f t1 t2,
    f None None = true ->
    if compare A f t1 t2
      then forall k, f (get A t1 k) (get A t2 k) = true
      else ~ forall k, f (get A t1 k) (get A t2 k) = true.
  Proof compare_correct.




End BinMap_Base.

Module BinMap <: MAP  with Definition key := positive := 
  Map_Of_MapBase BinMap_Base.


Module BinNatMap_Base <: MAP_BASE with Definition key := N.

  Definition t A := (option A*BinMap_Base.t A)%type.
  Definition key := N.
  Definition eq_key := Neq.
  Lemma eq_key_spec : forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Proof. exact Neq_spec. Qed.

  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof.
   intros k1 k2;generalize (eq_key_spec k1 k2);destruct (eq_key k1 k2);auto.
  Qed.

  Definition get (A:Type)(m:t A)(k:key) :=
    match k with
      N0 => fst m
    | Npos p => BinMap_Base.get _ (snd m) p
    end.
  Definition modify (A:Type)(m:t A)(k:key)(f:option A->option A) := 
    let (v',m') := m in
    match k with
      N0 => (f v',m')
    | Npos p => (v',BinMap_Base.modify _ m' p f)
    end.
  Lemma get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Proof.
    destruct k; destruct t0; simpl; intros; auto.
    apply BinMap_Base.get_modify1.
  Qed.
  Lemma get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.
  Proof.
    destruct k1; destruct k2; destruct t0; simpl; intros; auto.
    elim H; auto.
    apply BinMap_Base.get_modify2.
    intro; elim H; subst; auto.
  Qed.

  Definition empty (A:Type) := (None (A:=A),BinMap_Base.empty A).
  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    unfold empty, get; destruct k; intros; simpl;trivial.
  Qed.

  Definition f' (A:Type) := (fun pa:positive*A => let (p,a) := pa in (Npos p,a)).

  Definition elements : forall A, t A -> list (key*A) :=
    fun A m => let (v,m) := m in
     match v with
       None => map (f' A) (BinMap_Base.elements _ m)
     | Some a => (N0,a)::(map (f' A) (BinMap_Base.elements _ m))
    end.

  Lemma in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a. 
  Proof.
    unfold elements, get; intros.
    destruct m; destruct p; simpl in *.
    destruct o.
    destruct H.
    injection H; intros; subst; auto.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; discriminate H.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; discriminate H.
    destruct o.
    destruct H.
    discriminate H.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; injection H; clear H; intros; subst.
    apply BinMap_Base.in_elements_get_some; auto.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; injection H; clear H; intros; subst.
    apply BinMap_Base.in_elements_get_some; auto.
  Qed.

  Lemma get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).
  Proof.
    unfold get, elements; intros.
    destruct p; destruct m; simpl in *; subst.
    left; auto.
    destruct o; try right;
    apply (in_map (f' A) (BinMap_Base.elements _ t0) (p,a));
    apply BinMap_Base.get_some_in_elements; auto.
  Qed.

  Definition fold (A B:Type) (f:key->A->B->B) (m:t A) (b:B) : B :=  
    let (v,m) := m in
      match v with
        None =>  BinMap_Base.fold _ _ (fun p a b => f (Npos p) a b) m b
      | Some v =>  f N0 v (BinMap_Base.fold _ _ (fun p a b => f (Npos p) a b) m b) 
      end.

  Lemma fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.
  Proof.
    unfold fold, elements; intros.
    destruct t0.
    destruct o; simpl; 
    try apply f_equal with (f := (f N0 a));
    rewrite <- BinMap_Base.fold_prop;
    rewrite fold_right_map; apply fold_right_eq;
    intros (p,a'); simpl; auto.
  Qed.

  Definition compare : forall A, (option A->option A->bool) -> t A -> t A -> bool :=
    fun A f m1 m2 =>
      let (a1,m1) := m1 in 
        let (a2,m2) := m2 in
          f a1 a2 && BinMap_Base.compare A f m1 m2.

  Lemma compare_correct : forall A f t1 t2,
    f None None = true ->
    if compare A f t1 t2
      then forall k, f (get A t1 k) (get A t2 k) = true
      else ~ forall k, f (get A t1 k) (get A t2 k) = true.
  Proof.
    destruct t1; destruct t2; simpl.
    case_eq (f o o0); simpl.
    generalize (BinMap_Base.compare_correct _ f t0 t1);
      destruct (BinMap_Base.compare _ f t0 t1); simpl; intros.
    destruct k; simpl; auto.
    intro; elim H; clear H; intros; auto.
    apply (H2 (Npos k)).
    red; intros.
    generalize (H1 N0); simpl; intro.
    congruence.
  Qed.


End BinNatMap_Base.

Module BinNatMap <: MAP  with Definition key := N := 
  Map_Of_MapBase BinNatMap_Base.

Module MapPair_Base (M1 M2:MAP_BASE) <: MAP_BASE
  with Definition key := (M1.key * M2.key)%type.

  Definition t (A:Type) := M1.t (M2.t A).
  Definition key := (M1.key*M2.key)%type.
  Definition get (A:Type)(m:t A)(k:key) := 
    match (M1.get m (fst k)) with
      None => None
    | Some m => M2.get m  (snd k)
    end.
  Definition modify (A:Type)(m:t A)(k:key)(f:option A->option A) :=
    M1.modify m (fst k) 
     (fun m => match m with
        None => Some (M2.modify (@M2.empty _) (snd k) f)
      | Some m => Some (M2.modify m (snd k) f)
      end).
  Definition empty (A:Type) := M1.empty (M2.t A).

  Lemma get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Proof.
    intros; unfold get, modify.
    rewrite M1.get_modify1.
    destruct (M1.get t0 (fst k));
    rewrite M2.get_modify1; auto.
    rewrite M2.get_empty; auto.
  Qed.

  Lemma get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.
  Proof.
    intros; unfold get, modify.
    destruct (M1.key_dec (fst k1) (fst k2)).
    rewrite H0.
    rewrite M1.get_modify1; auto.
    destruct (M1.get t0 (fst k2));
    rewrite M2.get_modify2; auto.
    intro; elim H.
    destruct k1; destruct k2; simpl in *; congruence.
    rewrite M2.get_empty; auto.
    intro; elim H.
    destruct k1; destruct k2; simpl in *; congruence.
    rewrite M1.get_modify2; auto.
  Qed.

  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    intros; unfold get, empty.
    rewrite M1.get_empty.
    reflexivity.
  Qed.

  Definition eq_key := prod_eq _ M1.eq_key _ M2.eq_key.

  Lemma eq_key_spec : forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Proof. 
    exact (prod_eq_spec _  M1.eq_key M1.eq_key_spec _  M2.eq_key M2.eq_key_spec). 
  Qed.

  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof. exact (Aeq_dec _ eq_key eq_key_spec). Qed.

  Definition elements  (A:Type) (m:t A) : list (key*A) :=
   flat_map (fun km1:M1.key*_ => let (k1,m) := km1 in
               (map (fun ka2:M2.key*A => let (k2,a) := ka2 in ((k1,k2),a)) (M2.elements m))) 
            (M1.elements m).

  Lemma in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a. 
  Proof.
    unfold elements, get; intros.
    destruct (in_flat_map_inv _ _ _ _ _ H); clear H.
    destruct x; destruct H0.
    destruct (in_map_inv _ _ _ _ _ H).
    destruct x.
    destruct H1; injection H1; intros; subst.
    simpl.
    rewrite (M1.in_elements_get_some _ _ _ _ H0).
    apply (M2.in_elements_get_some _ _ _ _ H2).
  Qed.

  Lemma get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).
  Proof.
    unfold elements, get; intros.
    generalize (M1.get_some_in_elements _ m (fst p)) H; clear H.
    case (M1.get m (fst p)); intros.
    apply in_flat_map with (a:=(fst p,t0)); auto.
    destruct p; simpl in *.
    apply (in_map (fun ka2 : M2.key * A => let (k2, a0) := ka2 in (k, k2, a0))
       (M2.elements t0) (k0,a)).
    apply M2.get_some_in_elements; auto.
    discriminate.
  Qed.

  Definition fold (A B:Type) (f:key->A->B->B) (m:t A) (b:B) : B :=  
    M1.fold (fun k1 m b => M2.fold (fun k2 => f (k1,k2)) m b) m b.

  Lemma fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.
  Proof.
    unfold fold, elements; intros.
    rewrite fold_right_flat_map.
    rewrite <- M1.fold_prop.
    apply fold_right_eq2; intros.
    destruct a.
    rewrite <- M2.fold_prop.
    rewrite fold_right_map; apply fold_right_eq;
    intros (p,a'); simpl; auto.
  Qed.

  Module MM2 := Map_Of_MapBase M2.

  Definition compare : forall A, (option A->option A->bool) -> t A -> t A -> bool :=
    fun A f => 
      M1.compare 
        (fun m1 m2 => 
          match m1 ,m2 with
            | None, None => true
            | None, Some m2 => MM2.for_all _ (fun _ a => f None (Some a)) m2
            | Some m1, None => MM2.for_all _ (fun _ a => f (Some a) None) m1
            |Some m1, Some m2 => M2.compare f m1 m2
          end).

  Lemma compare_correct : forall A f t1 t2,
    f None None = true ->
    if compare A f t1 t2
      then forall k, f (get A t1 k) (get A t2 k) = true
      else ~ forall k, f (get A t1 k) (get A t2 k) = true.
  Proof.
    unfold compare, get; intros.
    match goal with
      [ |- context[M1.compare ?f ?m1 ?m2] ] =>
      generalize (M1.compare_correct _ f m1 m2);
        destruct (M1.compare f m1 m2)
    end; intros.
    destruct k as [k1 k2]; simpl.
    generalize (H0 (refl_equal _) k1); 
      destruct (M1.get t1 k1); destruct (M1.get t2 k1); simpl; intros; auto.
    generalize (M2.compare_correct A f t0 t3); rewrite H1; auto.
    generalize (MM2.for_all_spec _ (fun (_ : MM2.key) (a : A) => f (Some a) None) t0);
      rewrite H1; intros.
    generalize (H2  k2); unfold MM2.get; destruct (M2.get t0 k2); simpl; auto.
    generalize (MM2.for_all_spec _ (fun (_ : MM2.key) (a : A) => f None (Some a)) t0);
      rewrite H1; intros.
    generalize (H2 k2); unfold MM2.get; destruct (M2.get t0 k2); simpl; auto.
    intro; elim H0; clear H0; intros; auto.
    case_eq (M1.get t1 k); case_eq (M1.get t2 k); intros; auto.
    generalize (M2.compare_correct A f t3 t0); destruct (M2.compare f t3 t0); auto.
    intros H3; elim H3; clear H3; auto; intros.
    generalize (H1 (k,k0)); simpl; rewrite H0; rewrite H2; auto.
    generalize (MM2.for_all_spec _ (fun (_ : MM2.key) (a : A) => f (Some a) None) t0);
      destruct (MM2.for_all _ (fun (_ : MM2.key) (a : A) => f (Some a) None) t0); auto; intros.
    elim H3; intros; clear H3.
    generalize (H1 (k,k0)); simpl; rewrite H0; rewrite H2.
    unfold MM2.get in H4; rewrite H4; auto.
    generalize (MM2.for_all_spec _ (fun (_ : MM2.key) (a : A) => f None (Some a)) t0);
      destruct (MM2.for_all _ (fun (_ : MM2.key) (a : A) => f None (Some a)) t0); auto; intros.
    elim H3; intros; clear H3.
    generalize (H1 (k,k0)); simpl; rewrite H0; rewrite H2.
    unfold MM2.get in H4; rewrite H4; auto.
  Qed.

End MapPair_Base.

Module MapOption_Base (M:MAP_BASE) <: MAP_BASE with Definition key := option M.key.

  Definition t A := (option A*M.t A)%type.
  Definition key := option M.key.
  Definition eq_key x y := 
    match x, y with
      | None, None => true
      | Some x, Some y => M.eq_key x y
      | _, _ => false
    end.
  Lemma eq_key_spec : forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Proof.
    destruct k1; destruct k2; simpl; try auto || discriminate.
    generalize (M.eq_key_spec k k0); destruct (M.eq_key k k0); try congruence.
  Qed.

  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof.
   intros k1 k2;generalize (eq_key_spec k1 k2);destruct (eq_key k1 k2);auto.
  Qed.

  Definition get (A:Type)(m:t A)(k:key) :=
    match k with
      None => fst m
    | Some p => M.get (snd m) p
    end.
  Definition modify (A:Type)(m:t A)(k:key)(f:option A->option A) := 
    let (v',m') := m in
    match k with
      None => (f v',m')
    | Some p => (v',M.modify m' p f)
    end.
  Lemma get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Proof.
    destruct k; destruct t0; simpl; intros; auto.
    apply M.get_modify1.
  Qed.
  Lemma get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.
  Proof.
    destruct k1; destruct k2; destruct t0; simpl; intros; auto.
    apply M.get_modify2.
    intro; elim H; subst; auto.
    elim H; auto.
  Qed.

  Definition empty (A:Type) := (None (A:=A),M.empty A).
  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    unfold empty, get; destruct k; intros; simpl; auto.
    apply M.get_empty.
  Qed.

  Definition f' (A:Type) := (fun pa:M.key*A => let (p,a) := pa in (Some p,a)).

  Definition elements : forall A, t A -> list (key*A) :=
    fun A m => let (v,m) := m in
     match v with
       None => map (f' A) (M.elements m)
     | Some a => (None,a)::(map (f' A) (M.elements m))
    end.

  Lemma in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a. 
  Proof.
    unfold elements, get; intros.
    destruct m; destruct p; simpl in *.
    destruct o.
    destruct H.
    discriminate H.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x.
    injection H; intros; subst.
    apply M.in_elements_get_some; auto.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x.
    injection H; intros; subst.
    apply M.in_elements_get_some; auto.
    destruct o.
    destruct H.
    injection H; intros; subst; auto.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; discriminate.
    destruct (in_map_inv _ _ _ _ _ H); clear H.
    destruct H0; unfold f' in *.
    destruct x; discriminate.
  Qed.

  Lemma get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).
  Proof.
    unfold get, elements; intros.
    destruct p; destruct m; simpl in *; subst.
    destruct o; try right;
    apply (in_map (f' A) (M.elements t0) (k,a));
    apply M.get_some_in_elements; auto.
    left; auto.
  Qed.

  Definition fold (A B:Type) (f:key->A->B->B) (m:t A) (b:B) : B :=  
    let (v,m) := m in
      match v with
        None =>  M.fold (fun p a b => f (Some p) a b) m b
      | Some v =>  f (@None _) v (M.fold (fun p a b => f (Some p) a b) m b) 
      end.

  Lemma fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.
  Proof.
    unfold fold, elements; intros.
    destruct t0.
    destruct o; simpl; 
    try apply f_equal with (f := (f None a));
    rewrite <- M.fold_prop;
    rewrite fold_right_map; apply fold_right_eq;
    intros (p,a'); simpl; auto.
  Qed.

  Definition compare : forall A, (option A->option A->bool) -> t A -> t A -> bool :=
    fun A f m1 m2 =>
      let (a1,m1) := m1 in 
        let (a2,m2) := m2 in
          f a1 a2 && M.compare f m1 m2.

  Lemma compare_correct : forall A f t1 t2,
    f None None = true ->
    if compare A f t1 t2
      then forall k, f (get A t1 k) (get A t2 k) = true
      else ~ forall k, f (get A t1 k) (get A t2 k) = true.
  Proof.
    destruct t1; destruct t2; simpl.
    case_eq (f o o0); simpl.
    generalize (M.compare_correct _ f t0 t1);
      destruct (M.compare f t0 t1); simpl; intros.
    destruct k; simpl; auto.
    intro; elim H; clear H; intros; auto.
    apply (H2 (Some k)).
    red; intros.
    generalize (H1 None); simpl; intro.
    congruence.
  Qed.

End MapOption_Base.


Module Type HASH_TYPE.
  Parameter t : Set.
  Parameter eq_t : t -> t -> bool.
  Parameter eq_t_spec : forall t1 t2, if eq_t t1 t2 then t1 = t2 else t1 <> t2.
  Parameter eq_dec : forall x y:t, x=y \/ ~x=y.
  Parameter key : Set.
  Parameter hash : t -> key.
End HASH_TYPE.

Module MapHash_Base 
  (H:HASH_TYPE) (M:MAP_BASE with Definition key := H.key) <:
    MAP_BASE with Definition key := H.t.

  Record hashtab (A:Type) : Type := mk_hashtab {
    tab :> M.t (dlist H.t A);
    tab_inv :> forall k l, M.get tab k = Some l -> 
      forall x a, In (x,a) l -> H.hash x = k
  }.

  Definition t A := hashtab A.
  Definition key := H.t.
  Definition eq_key := H.eq_t.
  Definition eq_key_spec := H.eq_t_spec.
  Lemma key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2.
  Proof H.eq_dec.

  Definition get (A:Type) (m:t A) (k:key) : option A := 
    match (M.get m (H.hash k)) with
      None => None
    | Some l => dassoc H.eq_t k l
    end.

  Definition modify_aux (A:Type) (m:t A) (k:key) (f:option A->option A) : M.t (dlist H.t A) := 
    M.modify m (H.hash k) 
     (fun ol => match ol with 
                  None => 
                    match f None with
                      None => Some (@dnil _ _)
                    | Some b => Some (dmodify_assoc H.eq_t H.eq_t_spec k (@dnil _ _) (fun _ => Some b))
                    end
                | Some l => Some (dmodify_assoc H.eq_t H.eq_t_spec k l f)
                end).

  Lemma modify_aux_prop : forall A m k f,
   forall (k0 : M.key) (l : dlist H.t A),
   M.get (modify_aux A m k f) k0 = Some l ->
   forall (x : H.t) (a : A), In (x, a) l -> H.hash x = k0.
    intros A m k f; unfold modify_aux; intros k0 l.
    destruct (M.key_dec (H.hash k) k0).
    rewrite H.
    rewrite M.get_modify1.
    destruct m as [m Hm]; simpl in *.
    generalize (Hm k0); clear Hm.
    destruct (M.get m k0); intros.
    inversion_clear H1 in H2.
    generalize (in_dassoc_prop1 _ _ H.eq_t H.eq_t_spec _ _ _ H2); intros.
    destruct (H.eq_dec k x); subst; auto.
    rewrite assoc_dmodify_assoc2 in H1; auto.
    generalize (in_dassoc_prop2 _ _ H.eq_t H.eq_t_spec _ _ _ H1); intros.
    apply H0 with d a; auto.
    clear H0; destruct (f None).
    inversion_clear H1 in H2.
    simpl in H2.
    destruct H2.
    injection H0; intros; subst; auto.
    elim H0.
    inversion_clear H1 in H2; inversion_clear H2.
    rewrite M.get_modify2; auto.
    destruct m; simpl in *; eauto.
  Qed.

  Definition modify (A:Type) (m:t A) (k:key) (f:option A->option A) : t A :=
    mk_hashtab _ (modify_aux A m k f) (modify_aux_prop A m k f).
  
  Lemma get_modify1 : forall A t k f,
    get A (modify A t k f) k = f (get A t k).
  Proof.
    intros; unfold get, modify, modify_aux; simpl.
    rewrite M.get_modify1; auto.
    destruct (M.get t0 (H.hash k)).
    apply assoc_dmodify_assoc1.
    destruct f; simpl; auto.
    rewrite assoc_dmodify_assoc1; auto.
  Qed.

  Lemma get_modify2 : forall A t k1 k2 f,
    k1 <> k2 ->
    get A (modify A t k2 f) k1 = get A t k1.
  Proof.
    intros; unfold get, modify, modify_aux; simpl.
    destruct (M.key_dec (H.hash k1) (H.hash k2)).
    rewrite H0;  rewrite M.get_modify1.
    destruct (M.get t0 (H.hash k2)); simpl.
    apply assoc_dmodify_assoc2; auto.
    destruct f; simpl; auto.
    rewrite assoc_dmodify_assoc2; auto.
    rewrite M.get_modify2; auto.
  Qed.

  Lemma empty_prop : forall A,
   forall (k0 : M.key) (l : dlist H.t A),
   M.get (@M.empty _) k0 = Some l ->
   forall (x : H.t) (a : A), In (x, a) l -> H.hash x = k0.
  Proof.
    intros.
    rewrite M.get_empty in H.
    discriminate H.
  Qed.

  Definition empty (A:Type) : t A := mk_hashtab _ (@M.empty _) (empty_prop _).
  Lemma get_empty : forall A k, get A (empty A) k = None.
  Proof.
    unfold empty, get; simpl; intros.
    rewrite M.get_empty; auto.
  Qed.

  Definition elements A (m:t A) : list (key*A) :=
    flat_map (fun c => dlist_list _ _ (snd c)) (M.elements m).

  Lemma in_elements_get_some : forall A m p a,
    In (p,a) (elements A m) -> get A m p = Some a. 
  Proof.
    unfold elements, get; intros.
    destruct (in_flat_map_inv _ _ _ _ _ H).
    rewrite (M.in_elements_get_some _ m (H.hash p) (snd x)).
    apply in_dassoc_prop1; intuition.
    exact (H.eq_t_spec x0 y).
     destruct m; simpl in *.
    assert (H.hash p = fst x).
    apply tab_inv0 with (snd x) a; intuition.
    destruct x; simpl in *.
    apply M.in_elements_get_some; auto.
    rewrite H1; destruct x; intuition.
  Qed.

  Lemma get_some_in_elements : forall A m p a,
    get A m p = Some a -> In (p,a) (elements A m).
  Proof.
    unfold elements, get; intros.
    generalize (refl_equal (M.get m (H.hash p)));
    pattern (M.get m (H.hash p)) at -1;
    case (M.get m (H.hash p)); intros.
    rewrite H0 in H.
    apply in_flat_map with (H.hash p,d); simpl.
    eapply in_dassoc_prop2; eauto.
    exact H.eq_t_spec.
    apply M.get_some_in_elements; auto.
    rewrite H0 in H; discriminate.
  Qed.

  Definition fold (A B:Type)(f:key->A->B->B) (m:t A) (b:B) :B := 
     fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements _ m).

  Lemma fold_prop : forall (A B:Type) f t b,
    fold_right (fun (pa : key * A) (b0 : B) => let (p0, a) := pa in f p0 a b0)
       b (elements A t) = fold A B f t b.
  Proof.
    reflexivity.
  Qed.

  Definition compare : forall A, (option A->option A->bool) -> t A -> t A -> bool :=
    fun A f => 
      M.compare 
        (fun ol1 ol2 => 
          match ol1 ,ol2 with
            | None, None => true
            | None, Some l2 => ListAux.for_all _ (fun p => f None (Some (snd p))) l2
            | Some l1, None => ListAux.for_all _ (fun p => f (Some (snd p)) None) l1
            | Some l1, Some l2 => ListAux.compare _ _  H.eq_t f l1 l2
          end).

  Lemma compare_correct : forall A f t1 t2,
    f None None = true ->
    if compare A f t1 t2
      then forall k, f (get A t1 k) (get A t2 k) = true
      else ~ forall k, f (get A t1 k) (get A t2 k) = true.
  Proof.
    unfold compare, get; intros.
    match goal with
      [ |- if M.compare ?f ?t1 ?t2 then _ else _ ] =>
      generalize (M.compare_correct _ f t1 t2);
        destruct (M.compare f t1 t2)
    end; intros.
    generalize (H0 (refl_equal _) (H.hash k)); clear H0; intros.
    destruct (M.get t1 (H.hash k)).
    destruct (M.get t2 (H.hash k)).
    generalize (ListAux.compare_correct H.t A H.eq_t H.eq_t_spec f d d0); rewrite H0; auto.
    generalize (ListAux.for_all_correct  _ (fun p : H.t * A => f (Some (snd p)) None) d);
      rewrite H0; intros.
    case_eq (dassoc H.eq_t k d); intros; auto.
   apply (H1 (k,a)).
   eapply ListAux.in_dassoc_prop2; eauto.
   apply H.eq_t_spec.
    destruct (M.get t2 (H.hash k)); auto.
    generalize (ListAux.for_all_correct  _ (fun p : H.t * A => f None (Some (snd p))) d);
      rewrite H0; intros.
    case_eq (dassoc H.eq_t k d); intros; auto.
   apply (H1 (k,a)).
   eapply ListAux.in_dassoc_prop2; eauto.
   apply H.eq_t_spec.
   intro; elim H0; auto; clear H0; intros.
   case_eq (M.get t1 k); intros;
   case_eq (M.get t2 k); intros.
   generalize (ListAux.compare_correct H.t A H.eq_t H.eq_t_spec f d d0);
     destruct (ListAux.compare H.t A H.eq_t f d d0); auto; intros.
   elim H3; clear H3; intros; auto.
   case_eq (dassoc H.eq_t k0 d); intros.
   assert (H.hash k0 = k).
   apply (tab_inv _ t1 k d H0) with a.
   eapply ListAux.in_dassoc_prop2; eauto.
   apply H.eq_t_spec.
   generalize (H1 k0); rewrite H4; clear H1; rewrite H0; rewrite H2.
   rewrite H3; auto.
   case_eq (dassoc H.eq_t k0 d0); intros.
   assert (H.hash k0 = k).
   apply (tab_inv _ t2 k d0 H2) with a.
   eapply ListAux.in_dassoc_prop2; eauto.
   apply H.eq_t_spec.
   generalize (H1 k0); rewrite H5; clear H1; rewrite H0; rewrite H2.
   rewrite H3; rewrite H4; auto.
   auto.
   generalize (ListAux.for_all_correct  _ (fun p : H.t * A => f (Some (snd p)) None) d);
     destruct (ListAux.for_all  _ (fun p : H.t * A => f (Some (snd p)) None) d); intro; auto.
   elim H3; clear H3; intros.
   destruct a as (k0,a); simpl.
   generalize (H1 k0); clear H1.
   rewrite (tab_inv _ t1 k d H0 _ _ H3).
   rewrite H0; rewrite H2.
   rewrite (ListAux.in_dassoc_prop1 _ _ _ H.eq_t_spec _ _ _ H3); auto.
   generalize (ListAux.for_all_correct  _ (fun p : H.t * A => f None (Some (snd p))) d);
     destruct (ListAux.for_all  _ (fun p : H.t * A => f None (Some (snd p))) d); intro; auto.
   elim H3; clear H3; intros.
   destruct a as (k0,a); simpl.
   generalize (H1 k0); clear H1.
   rewrite (tab_inv _ t2 k d H2 _ _ H3).
   rewrite H0; rewrite H2.
   rewrite (ListAux.in_dassoc_prop1 _ _ _ H.eq_t_spec _ _ _ H3); auto.
   auto.
 Qed.
 

End MapHash_Base.

Module Type PROJ.
  Parameter element:Type.
  Parameter key:Set.
  Parameter proj: element -> key.
End PROJ.

Open Scope type_scope.

Module Type PROJ2.
  Parameter element:Type.
  Parameter key1 key2:Set.
  Parameter proj: element -> key1*key2.
End PROJ2.

Module MapProjPair
   (P:PROJ2)
   (M1:MAP_PROJ  
     with Definition element := P.element
     with Definition key := P.key1
     with Definition proj := fun x:P.element => fst (P.proj x))
   (M2:MAP_PROJ 
     with Definition element := P.key2 * M1.t
     with Definition key := P.key2
     with Definition proj := fun x:P.key2 * M1.t => fst x).

  Definition element := P.element.
  Definition key := P.key1*P.key2.
  Definition proj : element -> key := P.proj.

  Record _t : Type := mkt {
    map :> M2.t;
    inv : forall k k2 m1 v,
      M2.get map k = Some (k2,m1) ->
      In v (M1.elements m1) -> snd (P.proj v) = k2
  }.

  Definition t : Type := _t.

  Definition eq_key : key -> key -> bool :=
   prod_eq _ M1.eq_key _ M2.eq_key.

  Definition eq_key_spec :
      forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2:=
   prod_eq_spec _ _ M1.eq_key_spec _ _ M2.eq_key_spec.
  Definition key_dec : forall k1 k2:key, k1=k2 \/ ~k1=k2 :=
   Aeq_dec _ _ eq_key_spec.

  Definition get (m:t) (k:key) : option element :=
    match M2.get m (snd k) with
      Some (k2,m1) => M1.get m1 (fst k)
    | None => None
    end.

  Definition update_aux (m:t) (v:element) : M2.t :=
    let (k1,k2) := proj v in
    match M2.get m k2 with
      Some (k2,m1) => M2.update m (k2,M1.update m1 v)
    | None => M2.update m (k2,M1.update M1.empty v)
    end.

  Lemma update_inv : 
   forall m v (k : M2.key) (k2 : P.key2) (m1 : M1.t) (v0 : M1.element),
   M2.get (update_aux m v) k = Some (k2, m1) ->
   In v0 (M1.elements m1) -> snd (P.proj v0) = k2.
  Proof.
    unfold update_aux; intros.
    let t:=constr : (proj v) in 
      (generalize (refl_equal t) H; 
       pattern t at -1;
       case t); intros.
    clear H.
    let t:=constr : (M2.get m k1) in 
      (generalize (refl_equal t) H2; 
       pattern t at -1;
       case t); intros; clear H2.
    destruct e as [k2' m1'].
    destruct (M2.key_dec k2' k).
    subst.
    assert (k=M2.proj (k, M1.update m1' v)).
    auto.
    generalize H3; clear H3.
    pattern k at -1; rewrite H2.
    rewrite M2.get_update1.
    intros H3; injection H3; intros. 
    subst.
    clear H3 H2.
    generalize (M1.in_elements_get_some _ _ H0).
    destruct (M1.key_dec (M1.proj v0) (M1.proj v)).
    rewrite H2; rewrite M1.get_update1.
    intros HH; inversion HH; subst; clear HH.
    generalize (M2.get_proj _ _ _ H); simpl; intros; 
    unfold proj in *.
    rewrite H1; auto.
    rewrite M1.get_update2; auto.
    intros.
    apply (inv m _ _ _ v0 H).
    eapply M1.get_some_in_elements; eauto.
    rewrite M2.get_update2 in H3.
    apply (inv m _ _ _ v0 H3); auto.
    intuition.
    destruct (M2.key_dec k k1).
    subst.   
    assert (k1=M2.proj (k1, M1.update M1.empty v)).
    auto.
    generalize H3; clear H3.
    pattern k1 at -1 ; rewrite H2.
    rewrite M2.get_update1.
    intros H3; injection H3; intros; subst. 
    clear H2 H3.
    generalize (M1.in_elements_get_some _ _ H0).
    destruct (M1.key_dec (M1.proj v0) (M1.proj v)).
    rewrite H2; rewrite M1.get_update1.
    intros HH; inversion HH; subst; clear HH.
    unfold proj in H1; rewrite H1; auto.
    rewrite M1.get_update2; auto.
    rewrite M1.get_empty; intros; discriminate.
    rewrite M2.get_update2 in H3.
    apply (inv m _ _ _ v0 H3); auto.
    intuition.
  Qed.  

  Definition update (m:t) (v:element) : t :=
   (mkt (update_aux  m v) (update_inv m v)).

  Lemma get_proj : forall t k v, get t k = Some v -> proj v = k.
  Proof.
    unfold get; intros.
    destruct k as [k1 k2]; simpl in *.
    generalize (inv t0 k2).
    generalize (M2.get_proj t0 k2); destruct (M2.get t0 k2); try discriminate.
    intros H1; generalize (H1 _ (refl_equal _)); clear H1; intros H1.
    destruct e.
    generalize (M1.get_proj t1 k1 _ H); intros.
    generalize (H2 _ _ v (refl_equal _)); intros.
    simpl in H1; subst.
    rewrite <- H3.
    unfold M1.proj.
    unfold proj; destruct (P.proj v); auto.
    eapply M1.get_some_in_elements; eauto.
  Qed.

  Lemma get_update1 : forall t v,  get (update t v) (proj v) = Some v.
  Proof.
    unfold get, update, update_aux; simpl.
    intros m v.
    case_eq (proj v); intros k1 k2 Hp.
    case_eq (M2.get m k2); [intros (k2',m1') Hg|intros Hg]; simpl.
    generalize (M2.get_proj _ _ _ Hg); simpl; intros; subst.
    assert (k2=M2.proj (k2, M1.update m1' v)).
    auto. 
    pattern k2 at 2; rewrite H; clear H.
    rewrite M2.get_update1.
    assert (k1=M1.proj v).
    unfold M1.proj; unfold proj in *; rewrite Hp; trivial.
    rewrite H; rewrite M1.get_update1; auto.
    assert (k2=M2.proj (k2, M1.update M1.empty v)).
    auto. 
    pattern k2 at 2; rewrite H; clear H.
    rewrite M2.get_update1.
    assert (k1=M1.proj v).
    unfold M1.proj; unfold proj in *; rewrite Hp; trivial.
    rewrite H; rewrite M1.get_update1; auto.
  Qed.

  Lemma get_update2 : forall t k v,
     k <> proj v -> get (update t v) k = get t k.
  Proof.
    unfold get, update, update_aux, proj; simpl.
    intros m (k1,k2) v.
    case_eq (P.proj v); intros k1' k2' Hp H.
    case_eq (M2.get m k2'); [intros (k2'',m1') Hg|intros Hg]; simpl.
    generalize (M2.get_proj _ _ _ Hg); simpl; intros; subst.
    destruct (M2.key_dec k2 k2').
    subst.    
    assert (k2'=M2.proj (k2', M1.update m1' v)).
    auto. 
    pattern k2' at 2; rewrite H0; clear H0.
    rewrite M2.get_update1.
    rewrite Hg.
    rewrite M1.get_update2; auto.
    unfold M1.proj; rewrite Hp.
    intro HH; elim H; subst; trivial.
    rewrite M2.get_update2; auto.
    destruct (M2.key_dec k2 k2').
    subst.    
    assert (k2'=M2.proj (k2', M1.update M1.empty v)).
    auto. 
    pattern k2' at 2; rewrite H0; clear H0.
    rewrite M2.get_update1.
    rewrite Hg.
    rewrite M1.get_update2; auto.
    apply M1.get_empty.
    unfold M1.proj; rewrite Hp.
    intro HH; elim H; subst; trivial.
    rewrite M2.get_update2; auto.
  Qed.

  Lemma empty_inv : 
   forall (k : M2.key) (k2 : P.key2) (m1 : M1.t) (v0 : M1.element),
   M2.get M2.empty k = Some (k2, m1) ->
   In v0 (M1.elements m1) -> snd (P.proj v0) = k2.
  Proof.
    intros.
    rewrite M2.get_empty in H; discriminate.
  Qed.

  Definition empty : t := mkt M2.empty empty_inv.

  Lemma get_empty : forall k, get empty k = None.
  Proof.
    unfold empty, get; simpl.
    intros; rewrite M2.get_empty; auto.
  Qed.

  Definition elements_tr : t -> list element -> list element :=
    fun m acc =>
    @fold_left _ _
     (fun l e => M1.elements_tr (snd e) l)
     (M2.elements m) acc.

  Lemma in_elements_tr_aux1 : forall (l:list M2.element) acc v,
    In v 
      (@fold_left _ _
        (fun l e => M1.elements_tr (snd e) l)
        l acc) ->
    (exists m1, In m1 (List.map (@snd _ _) l) /\ 
        exists k, M1.get m1 k = Some v) \/ In v acc.
  Proof.
    induction l; simpl; intros; auto.
    elim IHl with (1:=H); clear IHl H.
    intros (m1,(H1,(k,H2))).
    eauto 20.
    intros.
    elim M1.in_elements_tr with (1:=H); intros; auto; clear H. 
    destruct H0 as [k H0].
    left.
    exists (snd a); eauto.    
  Qed.

  Lemma in_elements_tr : forall t res a,  
    In a (elements_tr t res) -> 
    (exists k, get t k = Some a) \/ In a res.
  Proof.
    unfold elements_tr; intros.
    elim in_elements_tr_aux1 with (1:=H); intros; auto; clear H.
    destruct H0 as [m1 [H0 [k H1]]].
    left.
    elim in_map_inv with (1:=H0); clear H0; intros (k2,m) (H2,H3).
    simpl in H2; subst.
    exists (k,k2).
    unfold get.
    simpl.
    assert (k2=M2.proj (k2,m)).
    auto.
    rewrite H; clear H.
    rewrite M2.in_elements_get_some; auto.
  Qed.

  Lemma get_some_in_elements_tr_aux : forall (l:list M2.element) acc v,
    (exists m1, In m1 (List.map (@snd _ _) l) /\ 
        exists k, M1.get m1 k = Some v) \/ In v acc -> 
    In v (@fold_left _ _
           (fun l e => M1.elements_tr (snd e) l)
            l acc).
  Proof.
    induction l; simpl; intros.
    destruct H; auto.
    destruct H; intuition.
    apply IHl; clear IHl.
    destruct H.
    destruct H as [m1 [H H0]].
    destruct H0 as [k H0].
    destruct H.
    right.
    apply M1.get_some_in_elements_tr; rewrite H; eauto.
    left; exists m1; eauto.
    right.
    apply M1.get_some_in_elements_tr; auto.
  Qed.

  Lemma get_some_in_elements_tr : forall t res a,
    (exists k, get t k = Some a) \/ In a res -> 
    In a (elements_tr t res).
  Proof.
    unfold elements_tr, get; intros.
    apply get_some_in_elements_tr_aux.
    destruct H; auto.
    destruct H as [k H].
    case_eq (M2.get t0 (snd k)); intros.
    rewrite H0 in H.
    destruct e.
    left; exists t1; split; eauto.
    replace t1 with ((snd (A:=P.key2) (B:=M1.t)) (k0,t1)).
    apply in_map.
    eapply M2.get_some_in_elements; eauto.
    auto.
    rewrite H0 in H; discriminate.
  Qed.

  Definition elements : t -> list element := fun m => elements_tr m nil.

  Lemma in_elements_get_some : forall m a,
    In a (elements m) -> get m (proj a) = Some a.
  Proof.
  Proof.
    unfold elements;intros.
    destruct (in_elements_tr _ _ _ H).
    destruct H0 as (k,H0).
    rewrite (get_proj _ _ _ H0); auto.
    elim H0.
   Qed.
 
 Lemma get_some_in_elements : forall m p a,
    get m p = Some a -> In a (elements m).
  Proof.
    unfold get,elements;intros.
    apply get_some_in_elements_tr.
    left;exists p;trivial.
   Qed.

End MapProjPair.


Module MapProj (P:PROJ with Definition key := positive) <: MAP_PROJ.

  Definition element := P.element.
  Definition key := positive.
  Definition proj := P.proj.

  Record mapproj : Type := mkmp {
    tab :> tree (option element);
    tab_inv :> forall k a, apply_tree _ None  tab k = Some a -> proj a = k
  }.
  Definition t := mapproj.
  Definition eq_key := Peq.
  Lemma eq_key_spec :  forall k1 k2, if eq_key k1 k2 then k1 = k2 else k1 <> k2.
  Proof. exact Peq_spec. Qed.
  Lemma key_dec : forall (k1 k2:key), k1 = k2 \/ k1 <> k2.
  Proof. exact (Aeq_dec _ eq_key eq_key_spec). Qed.

  Definition get (m:t) := apply_tree _ None m.(tab).
  Definition update_aux (m:tree (option element)) (a:element) := 
      modify_tree _ None m (proj a) (fun (_:option element) => Some a).

  Lemma update_correct : forall tab,
     (forall k a, apply_tree _ None  tab k = Some a -> proj a = k) -> 
     forall e,
      forall k a, apply_tree _ None  (update_aux tab e) k = Some a -> proj a = k.
  Proof.
    unfold update_aux;intros.
    destruct (key_dec k (proj e)).
    rewrite H1 in H0.
    rewrite apply_modify_tree1 in H0.
    injection H0;intros;subst;trivial.
    rewrite apply_modify_tree2 in H0;auto.
  Qed.
  Definition update (m:t) (a:element) :=
    let (t,proof) := m in
    mkmp (update_aux t a) (update_correct t proof a).

  Lemma get_proj : forall t k v, get t k = Some v -> proj v = k.
  Proof. intros (tab0,proof);auto. Qed.

  Lemma get_update1 : forall t v,
    get (update t v) (proj v) = Some v.
  Proof. 
    intros (tab0, proof);unfold update, update_aux, get;simpl;intros.
    rewrite apply_modify_tree1;trivial.
  Qed.

  Lemma get_update2 : forall t k v,
    k <> proj v ->
    get (update t v) k = get t k.
  Proof.
    intros (tab0, proof);unfold update, update_aux, get;simpl;intros.
    rewrite apply_modify_tree2;trivial.
  Qed.

  Lemma empty_correct : 
      forall k a, apply_tree _ None  (leaf _)  k = Some a -> proj a = k.
  Proof. simpl;intros;discriminate. Qed.

  Definition empty := mkmp (leaf _) empty_correct.

  Lemma get_empty : forall k, get empty k = None.
  Proof. intros; reflexivity. Qed.

  Fixpoint elements_aux (t:tree(option element)) (res:list element){struct t} : list element  :=
    match t with 
    | leaf => res
    | node a t1 t2 => 
       elements_aux t1 (elements_aux t2 (match a with Some e => e::res | None => res end))
    end.
 
 Lemma in_elements_aux : forall t res a,  
    In a (elements_aux t res) -> (exists k, apply_tree _ None t k = Some a) \/ In a res.
  Proof. 
    induction t0;simpl;intros;auto.
    destruct (IHt0_1 _ _ H).
    destruct H0 as (k,HH).
    left;exists (xO k);auto.
    destruct (IHt0_2 _ _ H0).
    destruct H1 as (k,HH).
    left;exists (xI k);auto.
    destruct a;auto.
    destruct H1;auto.
    left;exists xH;subst;auto. 
   Qed.
      
  Definition elements (m:t) := elements_aux m.(tab) nil.

  Lemma in_elements_get_some : forall m a,
    In a (elements m) -> get m (proj a)= Some a. 
  Proof.
    unfold elements;intros.
    destruct (in_elements_aux _ _ _ H).
    destruct H0 as (k,H0).
    destruct m;simpl in *.
    unfold get;simpl;rewrite (tab_inv0 _ _ H0);trivial.
    elim H0.
   Qed.
 
  Lemma get_some_in_elements_aux : forall t res a,
    (exists k, apply_tree _ None t k = Some a) \/ In a res -> In a (elements_aux t res).
 Proof.
   induction t0;simpl;intros.
   destruct H;trivial. inversion H;discriminate.
   destruct H as [(k,H) | H].
   destruct k.
   apply IHt0_1.
   right;apply IHt0_2.
   left;exists k;trivial.
   apply IHt0_1.
   left;exists k;trivial.
   subst;apply IHt0_1.
   right;apply IHt0_2;right;simpl;auto.
   apply IHt0_1. right;apply IHt0_2;right.
   destruct a;simpl;auto.
  Qed.
 
 Lemma get_some_in_elements : forall m p a,
    get m p = Some a -> In a (elements m).
  Proof.
    unfold get,elements;intros (tab0,proof);intros.
    apply get_some_in_elements_aux.
    left;exists p;trivial.
   Qed.

  Definition elements_tr : t -> list element -> list element := 
   fun m => elements_aux m.

  Lemma in_elements_tr : forall t res a,  
    In a (elements_tr t res) -> 
    (exists k, get t k = Some a) \/ In a res.
  Proof.
    intros; unfold get; apply in_elements_aux; auto.
  Qed.

  Lemma get_some_in_elements_tr : forall t res a,
    (exists k, get t k = Some a) \/ In a res -> 
    In a (elements_tr t res).
  Proof.
    intros; unfold elements_tr; apply get_some_in_elements_aux; auto.
  Qed.

End MapProj.




