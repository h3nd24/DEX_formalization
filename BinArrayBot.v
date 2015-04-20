Require Export ZArith.
Require Export MapSignatures.

Section TabTree.

Variable A : Type.
Variable bot : A.

Inductive tree : Type :=
  | leaf : tree
  | node : A -> tree -> tree -> tree.

Fixpoint apply_tree (t : tree) (p : positive) {struct t} : A :=
  match t with
  | leaf => bot
  | node a tO tI =>
      match p with
      | xH => a
      | xO p => apply_tree tO p
      | xI p => apply_tree tI p
      end
  end.

Fixpoint subst_leaf (p : positive) (v : A) {struct p} : tree :=
  match p with
  | xH => node v leaf leaf
  | xO p' => node bot (subst_leaf p' v) leaf
  | xI p' => node bot leaf (subst_leaf p' v)
  end.


Lemma apply_subst_leaf1 :
 forall (p : positive) (v : A), apply_tree (subst_leaf p v) p = v.
Proof.
  induction p; auto.
Qed.

Fixpoint apply_subst_leaf1' 
  (p : positive) (v : A) {struct p} : apply_tree (subst_leaf p v) p = v :=
  match p return apply_tree (subst_leaf p v) p = v with
  | xH => refl_equal _
  | xO p' => (apply_subst_leaf1' p' v)
  | xI p' => (apply_subst_leaf1' p' v)
  end.

Lemma xI_diff : forall p1 p2, xI p1 <> xI p2 -> p1 <> p2.
Proof.
  red; intros.
  elim H; rewrite H0; auto.
Qed.

Lemma xO_diff : forall p1 p2, xO p1 <> xO p2 -> p1 <> p2.
Proof.
  red; intros.
  elim H; rewrite H0; auto.
Qed.

Hint Resolve xI_diff xO_diff.

Lemma apply_subst_leaf2 :
 forall (p1 p2 : positive) (v : A),
 p2 <> p1 -> apply_tree (subst_leaf p1 v) p2 = bot.
Proof.
  induction p1; destruct p2; simpl; auto || intuition.
Qed.

Hint Resolve apply_subst_leaf1 apply_subst_leaf2.

Fixpoint modify_tree (t : tree) (p : positive) 
 (f : A -> A) {struct t} : tree :=
  match t with
  | leaf => subst_leaf p (f bot)
  | node a tO tI =>
      match p with
      | xH => node (f a) tO tI
      | xO p' => node a (modify_tree tO p' f) tI
      | xI p' => node a tO (modify_tree tI p' f)
      end
  end.

Lemma apply_modify_tree1 :
 forall (t : tree) (p : positive) (f : A -> A),
 apply_tree (modify_tree t p f) p = f (apply_tree t p).
Proof.
  induction t; intros; simpl; auto.
  case p; simpl; auto.
Qed.

Lemma apply_modify_tree2 :
 forall (t : tree) (p x : positive) (f : A -> A),
 x <> p -> apply_tree (modify_tree t p f) x = apply_tree t x.
Proof.
  induction t; intros; simpl; auto.
  destruct x; destruct p; simpl; auto || intuition.
Qed.

End TabTree.

Module BinMapBot_Base : MAP_BOT_BASE with Definition key := positive.

  Definition t := tree.
  Definition key := positive.
  Lemma key_dec : forall k1 k2:key, {k1=k2}+{~k1=k2}.
  Proof.
    decide equality.
  Qed.

  Definition get := apply_tree.
  Definition modify := modify_tree.

  Definition get_modify1 : forall A bot t k f,
    get A bot (modify A bot t k f) k = f (get A bot t k) :=
    apply_modify_tree1.
  Lemma get_modify2 : forall A bot t k1 k2 f,
    k1 <> k2 ->
    get A bot (modify A bot t k2 f) k1 = get A bot t k1.
  Proof.
    intros; apply apply_modify_tree2; auto.
  Qed.
 
  Definition init (A:Type)(bot:A) := leaf A.
  Lemma get_init : forall A bot k, get A bot (init A bot) k = bot.
  Proof.
    unfold init, get; simpl; intros; reflexivity.
  Qed.

End BinMapBot_Base.

Module BinMapBot : MAP_BOT  with Definition key := positive := 
  MapBot_Of_MapBotBase BinMapBot_Base.

Module BinNatMapBot_Base : MAP_BOT_BASE with Definition key := N.

  Definition t A := (A*BinMapBot_Base.t A)%type.
  Definition key := N.
  Lemma key_dec : forall k1 k2:key, {k1=k2}+{~k1=k2}.
  Proof.
    decide equality.
    apply BinMapBot_Base.key_dec.
  Qed.

  Definition get (A:Type)(bot:A)(m:t A)(k:key) :=
    match k with
      N0 => fst m
    | Npos p => BinMapBot_Base.get A bot (snd m) p
    end.
  Definition modify (A:Type)(bot:A)(m:t A)(k:key)(f:A->A) := 
    let (v',m') := m in
    match k with
      N0 => (f v',m')
    | Npos p => (v',BinMapBot_Base.modify A bot m' p f)
    end.
  Lemma get_modify1 : forall A bot t k f,
    get A bot (modify A bot t k f) k = f (get A bot t k).
  Proof.
    destruct k; destruct t0; simpl; intros; auto.
    apply BinMapBot_Base.get_modify1.
  Qed.
  Lemma get_modify2 : forall A bot t k1 k2 f,
    k1 <> k2 ->
    get A bot (modify A bot t k2 f) k1 = get A bot t k1.
  Proof.
    destruct k1; destruct k2; destruct t0; simpl; intros; auto.
    elim H; auto.
    apply BinMapBot_Base.get_modify2.
    intro; elim H; subst; auto.
  Qed.

  Definition init (A:Type)(bot:A) := (bot,BinMapBot_Base.init A bot).
  Lemma get_init : forall A bot k, get A bot (init A bot) k = bot.
  Proof.
    unfold init, get; destruct k; intros; simpl.
    reflexivity.
    apply BinMapBot_Base.get_init.
  Qed.

End BinNatMapBot_Base.

Module BinNatMapBot : MAP_BOT  with Definition key := N := 
  MapBot_Of_MapBotBase BinNatMapBot_Base.

Module MapBotPair_Base (M1 M2:MAP_BOT_BASE) : MAP_BOT_BASE
  with Definition key := (M1.key * M2.key)%type.

  Definition t (A:Type) := M1.t (M2.t A).
  Definition key := (M1.key*M2.key)%type.
  Definition get (A:Type)(bot:A)(m:t A)(k:key) := 
    M2.get _ bot (M1.get _ (M2.init _ bot) m (fst k)) (snd k).
  Definition modify  (A:Type)(bot:A)(m:t A)(k:key)(f:A->A) :=
    M1.modify _ (M2.init _ bot) m (fst k) 
     (fun m => M2.modify _ bot m (snd k) f).
  Definition init (A:Type) (bot:A) := M1.init _ (M2.init A bot).

  Lemma get_modify1 : forall A bot t k f,
    get A bot (modify A bot t k f) k = f (get A bot t k).
  Proof.
    intros; unfold get, modify.
    rewrite M1.get_modify1.
    rewrite M2.get_modify1; auto.
  Qed.

  Lemma get_modify2 : forall A bot t k1 k2 f,
    k1 <> k2 ->
    get A bot (modify A bot t k2 f) k1 = get A bot t k1.
  Proof.
    intros; unfold get, modify.
    destruct (M1.key_dec (fst k1) (fst k2)).
    rewrite e.
    rewrite M1.get_modify1; auto.
    rewrite M2.get_modify2; auto.
    intro; elim H.
    destruct k1; destruct k2; simpl in *; congruence.
    rewrite M1.get_modify2; auto.
  Qed.

  Lemma get_init : forall A bot k, get A bot (init A bot) k = bot.
  Proof.
    intros; unfold get, init.
    rewrite M1.get_init.
    rewrite M2.get_init.
    reflexivity.
  Qed.

  Lemma key_dec : forall k1 k2:key, {k1=k2}+{~k1=k2}.
  Proof.
    decide equality.
    apply M2.key_dec.
    apply M1.key_dec.
  Qed.

End MapBotPair_Base.
