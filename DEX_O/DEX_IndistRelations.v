(** * IndistRelations.v: indistinguishability relation for annotated programs *)
Require FFun.
Require Export DEX_BigStepAnnot.
Require Export Annotated.

Open Scope type_scope.

Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Inductive Value_in  (b b':FFun.t DEX_Location) : DEX_value -> DEX_value -> Prop :=
| Value_in_null: Value_in b b' Null Null
| Value_in_num: forall n,
  Value_in b b' (Num n) (Num n)
| Value_in_ref: forall loc loc' n, 
  FFun.lookup b n = Some loc -> 
  FFun.lookup b' n = Some loc' -> 
  Value_in b b' (Ref loc) (Ref loc').

Inductive Value_in_opt (b b':FFun.t DEX_Location) : 
  option DEX_value -> option DEX_value -> Prop :=
| Value_in_opt_some: 
  forall v v',
    Value_in b b' v v' -> 
    Value_in_opt b b' (Some v) (Some v')
| Value_in_opt_none: Value_in_opt b b' None None.

Inductive Reg_in (observable:L.t) (b b':FFun.t DEX_Location) 
  (r r': DEX_Registers.t) (rt rt': TypeRegisters) (rn:DEX_Reg) : Prop :=
| Reg_high_in : forall k k', MapList.get rt rn = Some k -> MapList.get rt' rn = Some k' ->
    ~(L.leql k observable) -> ~(L.leql k' observable) -> 
    Reg_in observable b b' r r' rt rt' rn
| Reg_nhigh_in : Value_in_opt b b' (DEX_Registers.get r rn) (DEX_Registers.get r' rn) 
    -> Reg_in observable b b' r r' rt rt' rn.

Inductive Regs_in (observable:L.t) (b b':FFun.t DEX_Location) 
  (r r': DEX_Registers.t) (rt rt': TypeRegisters) : Prop :=
| Build_Regs_in : eq_set (MapList.dom rt) (MapList.dom rt') ->
  (forall (rn:DEX_Reg), Reg_in observable b b' r r' rt rt' rn) -> 
  Regs_in observable b b' r r' rt rt'.

Definition ffun_heap_compat (b:FFun.t DEX_Location) (h:DEX_Heap.t) : Prop :=
  forall loc, FFun.image b loc -> DEX_Heap.typeof h loc <> None.

Record hp_in (observable:L.t) (ft:DEX_FieldSignature -> L.t)  
    (b b': FFun.t DEX_Location) (h h': DEX_Heap.t) : Prop :=
  make_hp_in {
    object_in : forall n loc loc' f cn cn',
      FFun.lookup b n = Some loc -> 
      FFun.lookup b' n = Some loc' -> 
      DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) ->
      DEX_Heap.typeof h' loc' = Some (DEX_Heap.DEX_LocationObject cn') ->
      L.leql (ft f) observable->
      Value_in_opt b b' 
      (DEX_Heap.get h (DEX_Heap.DEX_DynamicField loc f))
      (DEX_Heap.get h' (DEX_Heap.DEX_DynamicField loc' f));
    class_object_in : forall n loc loc',
      FFun.lookup b n = Some loc -> 
      FFun.lookup b' n = Some loc' -> 
      DEX_Heap.typeof h loc = DEX_Heap.typeof h' loc';
    compat_ffun : FFun.compat b b';
(*     static_heap_in : True; *)
    left_inj : FFun.is_inj b;
    right_inj : FFun.is_inj b';
    left_heap_compat : ffun_heap_compat b h;
    right_heap_compat : ffun_heap_compat b' h'
  }.


Inductive st_in (observable:L.t) (ft:DEX_FieldSignature -> L.t) (b b':FFun.t DEX_Location) 
    (rt rt':TypeRegisters) :   
  DEX_PC * DEX_Heap.t * DEX_Registers.t ->
  DEX_PC * DEX_Heap.t * DEX_Registers.t -> Prop := 
| Build_st_in: forall pc pc' h h' r r',
    Regs_in observable b b' r r' rt rt' ->
    hp_in observable ft b b' h h' ->
    st_in observable ft b b' rt rt' (pc,h,r) (pc',h',r').

Inductive indist_return_value (observable:L.t) (h1 h2:DEX_Heap.t) (s:DEX_sign) : 
    DEX_ReturnVal -> DEX_ReturnVal -> FFun.t DEX_Location -> FFun.t DEX_Location -> Prop :=
| indist_return_val : forall v1 v2 b1 b2 k,
  s.(DEX_resType) = Some k ->
  (L.leql k observable -> Value_in b1 b2 v1 v2) ->
  indist_return_value observable h1 h2 s (Normal (Some v1)) (Normal (Some v2)) b1 b2
| indist_return_void : forall b1 b2, 
  s.(DEX_resType) = None ->
  indist_return_value observable h1 h2 s (Normal None) (Normal None) b1 b2.

Inductive high_result (observable:L.t) (s:DEX_sign) : DEX_ReturnState -> Prop :=
| high_result_void : forall h,
  s.(DEX_resType) = None ->
  high_result observable s (h, Normal None)
| high_result_value : forall h v k,
  s.(DEX_resType) = Some k ->
  ~ L.leql k observable ->
  high_result observable s (h, Normal (Some v)).

Inductive state : Type :=
  intra : DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> state
| ret : DEX_Heap.t -> DEX_ReturnVal -> FFun.t DEX_Location -> state.

Inductive indist (observable:L.t) (p:DEX_ExtendedProgram) (m:DEX_Method) 
  (sgn:DEX_sign) : state -> state -> Prop :=
| indist_intra : forall pc pc' h h' r r' rt rt' b b',
  st_in observable (DEX_ft p) b b' rt rt' (pc,h,r) (pc',h',r') ->
  indist observable p m sgn (intra (pc,(h,r)) rt b) (intra (pc',(h',r')) rt' b')
| indist_return : forall b b' h h' v v',
  indist_return_value observable h h' sgn v v' b b' ->
  indist observable p m sgn (ret h v b) (ret h' v' b').


 (** Indistinguishability relations *)

Section p.
  Variable kobs : L.t.
  Variable p : DEX_ExtendedProgram.
  Notation ft := (DEX_ft p).

 (** Basic results on indistinguishability relations *)

  Lemma Value_in_sym : forall v1 v2 b1 b2,
    Value_in b1 b2 v1 v2 ->
    Value_in b2 b1 v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
    constructor 3 with n; auto.
  Qed.

  Lemma Value_in_opt_sym : forall b1 b2 v1 v2,
    Value_in_opt b1 b2 v1 v2 ->
    Value_in_opt b2 b1 v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
    apply Value_in_sym; auto.
  Qed.

  Lemma Value_in_trans : forall b1 b2 b3 v1 v2 v3,
    FFun.is_inj b2 ->
    Value_in b1 b2 v1 v2 ->
    Value_in b2 b3 v2 v3 ->
    Value_in b1 b3 v1 v3.
  Proof.
    intros.
    inversion_clear H0 in H1; inversion_clear H1; try constructor.
    rewrite <- (H _ _ _ H3 H0) in H4.
    constructor 3 with n; auto.
  Qed.

  Lemma Value_in_opt_trans : forall b1 b2 b3 v1 v2 v3,
    FFun.is_inj b2 ->
    Value_in_opt b1 b2 v1 v2->
    Value_in_opt b2 b3 v2 v3 ->
    Value_in_opt b1 b3 v1 v3.
  Proof.
    intros.
    inversion_clear H0 in H1; inversion_clear H1; try constructor.
    eapply Value_in_trans; eauto.
  Qed. 

  Lemma leql_join1 : forall k1 k2 k3,
    L.leql k2 k3 ->
    L.leql k2 (L.join k1 k3).
  Proof.
    intros.
    apply L.leql_trans with (1:=H).
    apply L.join_right.
  Qed.

  Lemma leql_join2 : forall k1 k2 k3,
    L.leql k2 k1 ->
    L.leql k2 (L.join k1 k3).
  Proof.
    intros.
    apply L.leql_trans with (1:=H).
    apply L.join_left.
  Qed.

  Lemma not_leql_trans : forall k1 k2 k3,
    ~ L.leql k1 k3 ->
    L.leql k1 k2 ->
    ~ L.leql k2 k3.
  Proof.
    red; intros.
    elim H.
    apply L.leql_trans with (1:=H0); auto.
  Qed.

  Lemma not_leql_join1 : forall k1 k2 k3,
    ~ L.leql k1 k3 ->
    ~ L.leql (L.join k1 k2) k3.
  Proof.
    intros; apply not_leql_trans with k1; auto.
    apply L.join_left.
  Qed.

  Lemma not_leql_join2 : forall k1 k2 k3,
    ~ L.leql k2 k3 ->
    ~ L.leql (L.join k1 k2) k3.
  Proof.
    intros; apply not_leql_trans with k2; auto.
    apply L.join_right.
  Qed.

  Lemma leql_join_each: forall k k1 k2, L.leql (L.join k k1) k2 -> L.leql k k2 /\ L.leql k1 k2.
  Proof. intros.
    split. apply L.leql_trans with (l2:=L.join k k1); auto. apply L.join_left.
    apply L.leql_trans with (l2:=L.join k k1); auto. apply L.join_right.
  Qed.

  Lemma Reg_in_sym : forall obs b b' r r' rt rt' rn, 
    Reg_in obs b b' r r' rt rt' rn -> 
    Reg_in obs b' b r' r rt' rt rn.
  Proof.
    intros.
    inversion H.
      constructor 1 with (k:=k') (k':=k); auto.
      constructor 2; auto.
      apply Value_in_opt_sym; auto.
  Qed.  

 Lemma Regs_in_sym : forall b1 b2 r1 r2 rt1 rt2,
    Regs_in kobs b1 b2 r1 r2 rt1 rt2 ->
    Regs_in kobs b2 b1 r2 r1 rt2 rt1.
  Proof.
    induction 1.
    constructor. apply eq_set_sym; auto.
    intros.
    apply Reg_in_sym; auto.
  Qed.

  Lemma hp_in_sym : forall h1 h2 b1 b2,
    hp_in kobs ft b1 b2 h1 h2 -> hp_in kobs ft b2 b1 h2 h1.
  Proof.
    intros.
    destruct H; constructor; auto.
    intros.  
    apply Value_in_opt_sym; auto.
    eapply object_in0; eauto.
    intros.
    rewrite (class_object_in0 n loc' loc); auto.
    intros n; generalize (compat_ffun0 n); intuition.
  Qed.

  Lemma st_in_sym : forall b b' rt rt' r r',
    st_in kobs ft b b' rt rt' r r' ->
    st_in kobs ft b' b rt' rt r' r.
  Proof.
    intros.
    inversion_clear H; constructor.
    apply Regs_in_sym; auto.
    apply hp_in_sym; auto.
  Qed.
  Implicit Arguments st_in_sym.

  Lemma hp_in_trans : forall h1 h2 h3 b1 b2 b3,
    hp_in kobs ft b1 b2 h1 h2 -> 
    hp_in kobs ft b2 b3 h2 h3 ->
    hp_in kobs ft b1 b3 h1 h3.
  Proof.
    intros.
    destruct H; destruct H0.
    constructor; auto.
    intros.
    destruct (compat_ffun1 n).
    caseeq (FFun.lookup b2 n); intros.
    apply Value_in_opt_trans with 
      (v2:=(DEX_Heap.get h2 (DEX_Heap.DEX_DynamicField d f))) (b2:=b2); auto.
    eapply object_in0; eauto.
    rewrite <- (class_object_in0 n loc d); eauto.
    eapply object_in1; eauto.
    rewrite <- (class_object_in0 n loc d); eauto.
    rewrite H4 in H0; auto; discriminate.
    intros.
    destruct (compat_ffun1 n).
    caseeq (FFun.lookup b2 n); intros.
    rewrite (class_object_in0 n loc d); auto.
    rewrite (class_object_in1 n d loc'); auto.
    rewrite H1 in H0; auto; discriminate.  
    intros n.
    generalize (compat_ffun0 n); 
      generalize (compat_ffun1 n); intuition.
  Qed.

  Lemma Value_in_opt_some_aux: forall b b' ov ov' v v', 
    Value_in b b' v v' -> 
    ov=(Some v)  -> 
    ov'= (Some v') -> 
    Value_in_opt b b' ov ov'.
  Proof.
    intros;  subst; constructor; auto.
  Qed.

  Lemma Reg_in_upd_low: 
    forall k (v v' : DEX_value) (r r' : DEX_Registers.t) (rt rt' : TypeRegisters)
      (reg : DEX_Reg) (b b': FFun.t DEX_Location), 
      Reg_in kobs b b' r r' rt rt' reg -> 
      Value_in b b' v v' -> 
      L.leql k kobs ->
      Reg_in kobs b b' (DEX_Registers.update r reg v) (DEX_Registers.update r' reg v')
      (MapList.update rt reg k) (MapList.update rt' reg k) reg.
  Proof.
    intros k v v' r r' rt rt' reg b b' HRegIn HValIn Hleq.
    constructor 2. rewrite ?DEX_Registers.get_update_new.
    constructor; auto.
  Qed.

  Lemma Reg_in_upd_high:
    forall k k' (v v' : DEX_value) (r r' : DEX_Registers.t) (rt rt' : TypeRegisters)
      (reg : DEX_Reg) (b b': FFun.t DEX_Location), 
      Reg_in kobs b b' r r' rt rt' reg ->  
      ~L.leql k kobs ->
      ~L.leql k' kobs ->
      Reg_in kobs b b' (DEX_Registers.update r reg v) (DEX_Registers.update r' reg v')
      (MapList.update rt reg k) (MapList.update rt' reg k') reg.
  Proof.
    intros k k' v v' r r' rt rt' reg b b' HRegIn Hnleq1 Hnleq2.
    constructor 1 with (k:=k) (k':=k'); try (rewrite MapList.get_update1); auto.
  Qed.

  Lemma ffun_extends_val_in: forall b b' v v' loc loc',
    Value_in b b' v v' ->
    Value_in (FFun.extends b loc) (FFun.extends b' loc') 
    v v'.
  Proof.
    intros; inversion_clear H; try constructor.
    constructor 3 with n; auto.
    apply FFun.extends_old; auto.
    apply FFun.extends_old; auto.
  Qed.

  Lemma ffun_extends_val_in_opt: forall b b' v v' loc loc',
    Value_in_opt b b' v v' ->
    Value_in_opt (FFun.extends b loc) (FFun.extends b' loc')
    v v'.
  Proof.
    intros; inversion H; subst; try constructor.
    apply ffun_extends_val_in; auto.
  Qed.

  Lemma Value_in_extends_object : forall b1 b2 loc1 loc2 h1 h2,
    ffun_heap_compat b1 h1 ->
    ffun_heap_compat b2 h2 ->
    DEX_Heap.typeof h1 loc1 = None ->
    DEX_Heap.typeof h2 loc2 = None ->
    FFun.compat b1 b2 ->
    Value_in 
    (FFun.extends b1 loc1) (FFun.extends b2 loc2)
    (Ref loc1) (Ref loc2) .
  Proof.
    intros.
    constructor 3 with (FFun.next b1); auto.
    apply FFun.extends_new.
    rewrite (FFun.compat_implies_next _ b1 b2); auto.
    apply FFun.extends_new.
  Qed.

  Lemma ffun_extends_Regs_in: forall s s' rt rt' b b' loc loc',
    Regs_in kobs b b' s s' rt rt' ->
    Regs_in kobs (FFun.extends b loc) (FFun.extends b' loc') 
    s s' rt rt'.
  Proof.
    intros.
    induction H; intros; auto.
    constructor; auto.
    intros. specialize H0 with rn.
    inversion H0. constructor 1 with (k:=k) (k':=k'); auto. 
    constructor 2. apply ffun_extends_val_in_opt; auto.
  Qed.

  Lemma ffun_heap_compat_update : forall h b am v,
    ffun_heap_compat b h ->
    ffun_heap_compat b (DEX_Heap.update h am v).
  Proof.
    unfold ffun_heap_compat; intros.
    rewrite DEX_Heap.typeof_update_same; auto.
  Qed.

  Lemma ffun_heap_compat_extends : forall h c h' b loc,
    ffun_heap_compat b h ->
    DEX_Heap.new h p c = Some (loc,h') ->
    ffun_heap_compat (FFun.extends b loc) h'.
  Proof.
    unfold ffun_heap_compat; intros.
    destruct (DEX_Location_dec loc loc0).
    subst.
    rewrite (@DEX_Heap.new_typeof h p c loc0 h' H0).
    discriminate.
    rewrite (@DEX_Heap.new_typeof_old h p c loc loc0 h' H0); auto.
    apply H.
    destruct H1.
    elim FFun.extends_case with DEX_Location b x loc loc0; auto; intros.
    exists x; auto.
    elim n; intuition.
  Qed.

  Lemma ffun_heap_compat_new : forall h c h' b loc,
    ffun_heap_compat b h ->
    DEX_Heap.new h p c = Some (loc,h') ->
    ffun_heap_compat b h'.
  Proof.
    unfold ffun_heap_compat; intros.
    destruct (DEX_Location_dec loc loc0).
    subst.
    rewrite (@DEX_Heap.new_typeof h p c loc0 h' H0).
    discriminate.
    rewrite (@DEX_Heap.new_typeof_old h p c loc loc0 h' H0); auto.
  Qed.

  Lemma hp_in_putfield_ffun : forall loc loc' b b' h h' f v v' cn cn',
    hp_in kobs ft b b' h h' ->
    Value_in b b' v v' ->
    Value_in b b' (Ref loc) (Ref loc') ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) ->
    DEX_Heap.typeof h' loc' = Some (DEX_Heap.DEX_LocationObject cn') ->
    hp_in kobs ft b b'
    (DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) v)
    (DEX_Heap.update h' (DEX_Heap.DEX_DynamicField loc' f) v').
  Proof.
    intros; constructor; auto; intros.

    elim (DEX_Location_dec loc loc0);
      elim (eq_excluded_middle _ f f0); intros; subst.
    rewrite DEX_Heap.get_update_same; auto.
    replace loc'0 with loc'.
    rewrite DEX_Heap.get_update_same; auto.
    constructor; auto.
    constructor 1 with cn'; auto.
    inversion_mine H1.
    apply FFun.inv_aux with n0 n b b' loc0 loc0; auto. 
    eapply left_inj; eauto.
    eapply right_inj; eauto.
    constructor 1 with cn; auto.

    rewrite DEX_Heap.get_update_old.
    rewrite DEX_Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ H); eauto.
    rewrite DEX_Heap.typeof_update_same in H7; eauto.
    intros HH; elim H9; congruence.
    intros HH; elim H9; congruence.

    rewrite DEX_Heap.get_update_old.
    rewrite DEX_Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ H); eauto.
    rewrite DEX_Heap.typeof_update_same in H6; eauto.
    rewrite DEX_Heap.typeof_update_same in H7; eauto.
    intros HH; injection HH; intros; subst.
    elim b0.
    inversion_mine H1.
    apply (FFun.inv_aux _ n0 n b' b loc'0 loc loc'0 loc0); auto.
    eapply right_inj; eauto.
    eapply left_inj; eauto.
    intros HH; elim b0; congruence.

    rewrite DEX_Heap.get_update_old.
    rewrite DEX_Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ H); eauto.
    rewrite DEX_Heap.typeof_update_same in H6; eauto.
    rewrite DEX_Heap.typeof_update_same in H7; eauto.
    intros HH; elim b0; congruence.
    intros HH; elim b0; congruence.

    repeat rewrite DEX_Heap.typeof_update_same.
    eapply class_object_in; eauto.
    destruct H; auto.
    destruct H; auto.
    destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.
  Qed.

  Lemma hp_in_putfield_high_update_left : forall loc b b' h h' f v cn,
    hp_in kobs ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) ->
    hp_in kobs ft b b'
    (DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) v) h'.
  Proof.
    intros; constructor; auto; intros.
    assert (f<>f0).
    intro; subst; intuition.
    repeat rewrite DEX_Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ H); eauto.
    rewrite DEX_Heap.typeof_update_same in H4; eauto.
    intros HH; elim H7; congruence.
    rewrite DEX_Heap.typeof_update_same.
    eapply class_object_in; eauto.
    destruct H; auto.
    destruct H; auto.
    destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.
    destruct H; auto.
  Qed.

  Lemma hp_in_putfield_high_update_right : forall loc b b' h h' f v cn,
    hp_in kobs ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    DEX_Heap.typeof h' loc = Some (DEX_Heap.DEX_LocationObject cn) ->
    hp_in kobs ft b b'
    h (DEX_Heap.update h' (DEX_Heap.DEX_DynamicField loc f) v).
  Proof.
    intros.
    apply hp_in_sym.
    eapply hp_in_putfield_high_update_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma hp_in_putfield_high : forall loc loc' b b' h h' f v v' cn cn',
    hp_in kobs ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) ->
    DEX_Heap.typeof h' loc' = Some (DEX_Heap.DEX_LocationObject cn') ->
    hp_in kobs ft b b'
    (DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) v)
    (DEX_Heap.update h' (DEX_Heap.DEX_DynamicField loc' f) v').
  Proof.
    intros.
    apply hp_in_putfield_high_update_left with cn; auto.
    apply hp_in_putfield_high_update_right with cn'; auto.
  Qed.

  Lemma Compat_ex : forall h am, DEX_Heap.Compat h am \/ ~ DEX_Heap.Compat h am.
  Proof.
    intros.
    apply excluded_middle.
  Qed.

  Lemma ffun_extends_hp_in: forall c b b' h h' hn hn' loc loc',
    hp_in kobs ft b b' h h' ->
    DEX_Heap.new h p (DEX_Heap.DEX_LocationObject c) = Some (pair loc hn) ->
    DEX_Heap.new h' p (DEX_Heap.DEX_LocationObject c) = Some (pair loc' hn') ->
    hp_in kobs ft (FFun.extends b loc) (FFun.extends b' loc') hn hn'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.
    elim FFun.extends_case with DEX_Location b n loc loc0; intros; Cleanand; auto.
    assert (Haux:=FFun.compat_extends _ _ _ _ _ _ _ compat_ffun0 H6 H2).
    apply ffun_extends_val_in_opt.
    rewrite (@DEX_Heap.new_object_no_change h p c loc hn); auto.
    rewrite (@DEX_Heap.new_object_no_change h' p c loc' hn'); auto.

    assert (Hclass:=class_object_in0 _ _ _ H6 Haux).
    elim Compat_ex with h (@DEX_Heap.DEX_DynamicField loc0 f); intros Hcomp.
    inversion_clear Hcomp. 
    generalize H7; rewrite Hclass; intros.
    apply object_in0 with n cn0 cn0; auto.
    rewrite (@DEX_Heap.get_uncompat h); auto.
    rewrite (@DEX_Heap.get_uncompat h').
    constructor.
    intros HH; inversion_clear HH.
    elim Hcomp; constructor 1 with cn0.
    rewrite Hclass; auto.
    intros fs Hi; injection Hi; intros; subst.
    elim right_heap_compat0 with loc'.
    exists n; auto.
    apply DEX_Heap.new_fresh_location with (1:=H1).
    intros fs Hi; injection Hi; intros; subst.
    elim left_heap_compat0 with loc.
    exists n; auto.
    apply DEX_Heap.new_fresh_location with (1:=H0).

  (***)

    subst. 
    rewrite (FFun.compat_implies_next _ _ _ compat_ffun0) in H2.
    rewrite FFun.extends_new in H2.
    injection H2; clear H2; intros; subst.
    destruct (excluded_middle (defined_field p c f)) as [d|d].
    inversion_clear d.
    rewrite (@DEX_Heap.new_defined_object_field h p c f x loc0 hn); auto.
    rewrite (@DEX_Heap.new_defined_object_field h' p c f x loc'0 hn'); auto.
    constructor.
    unfold init_field_value.
    destruct (DEX_FIELD.initValue x); try constructor.
    unfold init_value. 
    destruct DEX_FIELDSIGNATURE.type; constructor.
    rewrite (@DEX_Heap.new_undefined_object_field h p c f loc0 hn); auto.
    rewrite (@DEX_Heap.new_undefined_object_field h' p c f loc'0 hn'); auto.
    constructor.

    elim FFun.extends_case with (1:= H); intros.
    assert (FFun.lookup b' n = Some loc'0). 
    apply FFun.compat_extends with b loc0 loc'; auto.
    destruct (DEX_Location_dec loc loc0); destruct (DEX_Location_dec loc' loc'0); subst.
    rewrite (@DEX_Heap.new_typeof h p (DEX_Heap.DEX_LocationObject c) loc0 hn); auto.
    rewrite (@DEX_Heap.new_typeof h' p (DEX_Heap.DEX_LocationObject c) loc'0 hn'); auto.
    assert (T:=@DEX_Heap.new_fresh_location h p (DEX_Heap.DEX_LocationObject c) loc0 hn H0).
    elim (left_heap_compat0 loc0); auto.
    exists n; auto.
    assert (T:=@DEX_Heap.new_fresh_location h' p (DEX_Heap.DEX_LocationObject c) loc'0 hn' H1).
    elim (right_heap_compat0 loc'0); auto.
    exists n; auto.
    rewrite (@DEX_Heap.new_typeof_old h p (DEX_Heap.DEX_LocationObject c) loc loc0 hn); auto.
    rewrite (@DEX_Heap.new_typeof_old h' p (DEX_Heap.DEX_LocationObject c) loc' loc'0 hn'); auto.
    eapply class_object_in0; eauto.
    destruct H3; subst.
    rewrite (@DEX_Heap.new_typeof h p (DEX_Heap.DEX_LocationObject c) loc0 hn); auto.
    rewrite (FFun.compat_implies_next _ _ _ compat_ffun0) in H2.
    rewrite (FFun.extends_new _ b' loc') in H2.
    injection H2; intros; subst.
    rewrite (@DEX_Heap.new_typeof h' p (DEX_Heap.DEX_LocationObject c) loc'0 hn'); auto.
    apply FFun.compat_preserved_by_extends; auto.
    apply FFun.extends_inj; auto.
    intro.
    elim (left_heap_compat0 _ H).
    eapply DEX_Heap.new_fresh_location; eauto.
    apply FFun.extends_inj; auto.
    intro.
    elim (right_heap_compat0 _ H).
    eapply DEX_Heap.new_fresh_location; eauto.
    apply ffun_heap_compat_extends with (2:=H0); auto.
    apply ffun_heap_compat_extends with (2:=H1); auto.
  Qed.

  Lemma ffun_extends_hp_in_new_left: forall c b b' h h' hn loc,
    hp_in kobs ft b b' h h' ->
    DEX_Heap.new h p (DEX_Heap.DEX_LocationObject c) = Some (pair loc hn) ->
    hp_in kobs ft b b' hn h'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.
    rewrite (@DEX_Heap.new_object_no_change h p c loc hn); auto.
    assert (Hclass:=class_object_in0 _ _ _ H H1).
    elim Compat_ex with h (DEX_Heap.DEX_DynamicField loc0 f); intros Hcomp.
    inversion_clear Hcomp. 
    generalize H5; rewrite Hclass; intros.
    apply object_in0 with n cn0 cn0; auto.
    rewrite (@DEX_Heap.get_uncompat h); auto.
    rewrite (@DEX_Heap.get_uncompat h').
    constructor.
    intros HH; inversion_clear HH.
    elim Hcomp; constructor 1 with cn0.
    rewrite Hclass; auto.
    intros fs Hi; injection Hi; intros; subst.
    elim left_heap_compat0 with loc.
    exists n; auto.
    apply DEX_Heap.new_fresh_location with (1:=H0).

    
    destruct (DEX_Location_dec loc0 loc); subst.
    rewrite (@DEX_Heap.new_typeof h p (DEX_Heap.DEX_LocationObject c) loc hn); auto.
    elim left_heap_compat0 with loc.
    exists n; auto.
    eapply DEX_Heap.new_fresh_location; eauto.
    rewrite (@DEX_Heap.new_typeof_old h p (DEX_Heap.DEX_LocationObject c) loc loc0 hn); auto.
    eauto.
    
    repeat intro.
    elim left_heap_compat0 with loc0; auto.
    destruct (DEX_Location_dec loc0 loc); subst.
    rewrite (@DEX_Heap.new_typeof h p (DEX_Heap.DEX_LocationObject c) loc hn) in H1; auto; discriminate.
    rewrite (@DEX_Heap.new_typeof_old h p (DEX_Heap.DEX_LocationObject c) loc loc0 hn) in H1; auto.
  Qed.

  Lemma ffun_extends_hp_in_new_right: forall c b b' h h' hn' loc,
    hp_in kobs ft b b' h h' ->
    DEX_Heap.new h' p (DEX_Heap.DEX_LocationObject c) = Some (pair loc hn') ->
    hp_in kobs ft b b' h hn'.
  Proof.
    intros.
    apply hp_in_sym; eapply ffun_extends_hp_in_new_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma ffun_extends_hp_in_simpl: forall c c' b b' h h' hn hn' loc loc',
    hp_in kobs ft b b' h h' ->
    DEX_Heap.new h p (DEX_Heap.DEX_LocationObject c) = Some (pair loc hn) ->
    DEX_Heap.new h' p (DEX_Heap.DEX_LocationObject c') = Some (pair loc' hn') ->
    hp_in kobs ft b b' hn hn'.
  Proof.
    intros.
    eapply ffun_extends_hp_in_new_left; eauto.
    eapply ffun_extends_hp_in_new_right; eauto.
  Qed.

  Lemma indist_same_class : forall h1 h2 loc1 loc2 b1 b2,
    hp_in kobs ft b1 b2 h1 h2 ->
    Value_in b1 b2 (Ref loc1) (Ref loc2) ->
    DEX_Heap.typeof h1 loc1 = DEX_Heap.typeof h2 loc2.
  Proof.
    intros.
    inversion_clear H0.
    apply (class_object_in _ _ _ _ _ _ H n) ;auto.
  Qed.

  Lemma ex_comp_Z : forall x y z:Z,
    (x <= y < z \/ ~ x <= y < z)%Z.
  Proof.
    intros.
    destruct (Z_le_dec x y).
    destruct (Z_lt_dec y z); intuition.
    intuition.
  Qed.

  Lemma nth_error_none_length : forall (A:Set) (l:list A) i,
    nth_error l i = None -> (length l <= i)%nat.
  Proof.
    induction l; destruct i; simpl; intros; try omega. 
    discriminate.
    generalize (IHl _ H); omega.
  Qed.

  Lemma nth_error_some_length : forall (A:Set) (l:list A) i a,
    nth_error l i = Some a -> (length l > i)%nat.
  Proof.
    induction l; destruct i; simpl; intros; try discriminate; try omega. 
    generalize (IHl _ _ H); omega.
  Qed.

  Definition beta_pre_order (b1 b2:FFun.t DEX_Location) : Prop :=
    forall loc n, FFun.lookup b1 n = Some loc -> FFun.lookup b2 n = Some loc. 

  Lemma beta_pre_order_value_in: forall v v' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    Value_in b1 b1' v v'->
    Value_in b2 b2' v v'.
  Proof.
    intros.
    inversion_clear H1; try constructor.
    constructor 3 with n; auto.
  Qed.

  Lemma beta_pre_order_value_in_opt:  forall v v' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    Value_in_opt b1 b1' v v' ->
    Value_in_opt b2 b2' v v'.
  Proof.
    intros.
    inversion_clear H1; constructor.
    eapply beta_pre_order_value_in; eauto.
  Qed.

  Lemma beta_pre_order_Regs_in:  forall s s' rt rt' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    Regs_in kobs b1 b1' s s' rt rt' ->
    Regs_in kobs b2 b2' s s' rt rt' .
  Proof.
    induction 3.
    constructor; auto.
    intros; specialize H2 with rn.
    inversion H2.
    constructor 1 with k k'; auto.
    constructor 2; auto.
    eapply beta_pre_order_value_in_opt; eauto.
  Qed.

  Lemma hp_in_getfield : forall b2 b2' v v0 h2 h2' loc loc0 cn cn0 f,
    DEX_Heap.typeof h2 loc = Some (DEX_Heap.DEX_LocationObject cn) ->
    DEX_Heap.get h2 (DEX_Heap.DEX_DynamicField loc f) = Some v ->
    DEX_Heap.typeof h2' loc0 = Some (DEX_Heap.DEX_LocationObject cn0) ->
    DEX_Heap.get h2' (DEX_Heap.DEX_DynamicField loc0 f) = Some v0 ->
    hp_in kobs ft b2 b2' h2 h2' ->
    L.leql (ft f) kobs ->
    Value_in b2 b2' (Ref loc) (Ref loc0) ->
    Value_in b2 b2' v v0.
  Proof.
    intros.
    inversion_clear H5.
    assert (HH:=object_in _ _ _ _ _ _ H3 _ _ _ f cn cn0 H6 H7 H H1 H4).
    rewrite H0 in HH; rewrite H2 in HH.
    inversion_clear HH; auto.
  Qed.

  Lemma Value_in_assign_compatible : forall h1 h2 loc1 loc2 t b1 b2,
    Value_in b1 b2 (Ref loc1) (Ref loc2) ->
    hp_in kobs ft b1 b2 h1 h2 ->
    assign_compatible p h1 (Ref loc1) (DEX_ReferenceType t) ->
    assign_compatible p h2 (Ref loc2) (DEX_ReferenceType t).
  Proof.
    intros.
    generalize (indist_same_class _ _ _ _ _ _ H0 H); intros.
    inversion_mine H1.
    constructor 2 with cn; auto; congruence.
  Qed.

  Lemma Value_in_assign_compatible' : forall h1 h2 v1 v2 t b1 b2,
    Value_in b1 b2 v1 v2 ->
    hp_in kobs ft b1 b2 h1 h2 ->
    assign_compatible p h1 v1 t ->
    assign_compatible p h2 v2 t.
  Proof.
    intros.
    destruct t. 
    destruct v1; destruct v2; try (inversion_mine H; inversion_mine H1; fail).
    eapply Value_in_assign_compatible; eauto.
    constructor.
    inversion_mine H; inversion_mine H1; constructor; auto.
  Qed.

  Lemma Value_in_extends : forall b1 b2 loc1 loc2 h1 h2,
    hp_in kobs ft b1 b2 h1 h2 ->
    DEX_Heap.typeof h1 loc1 = None ->
    DEX_Heap.typeof h2 loc2 = None ->
    Value_in 
    (FFun.extends b1 loc1) (FFun.extends b2 loc2)
    (Ref loc1) (Ref loc2) .
  Proof.
    intros.
    destruct H.
    eapply Value_in_extends_object; eauto.
  Qed.

(*  Lemma SemCompRef_Value_in : forall cmp v1 v2 v0 v3 b2 b2' h1 h2 ft,
    hp_in kobs ft b2 b2' h1 h2 ->
    DEX_SemCompRef cmp v1 v2 ->
    Value_in b2 b2' v2 v0 ->
    Value_in b2 b2' v1 v3 ->
    SemCompRef cmp v3 v0.
  Proof.
    intros.
    assert (Il:=left_inj _ _ _ _ _ _ _ H).
    assert (Ir:=right_inj _ _ _ _ _ _ _ H).
    inversion_mine H0;
    inversion_mine H1; inversion_mine H2; econstructor; auto;
      try constructor; try discriminate.
    rewrite (FFun.inv_aux Location n n0 b2 b2' loc loc' loc loc'0); auto.
    intro HH; elim H5; inversion_mine HH.
    rewrite (FFun.inv_aux Location n n0 b2' b2 loc' loc loc' loc0); auto.
  Qed. *)

End p.

  Hint Resolve 
    not_leql_join1 not_leql_join2 not_leql_trans 
    L.join_left L.join_right
    L.leql_trans : lattice.