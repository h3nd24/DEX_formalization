Require Export DEX_typing_rules.
Require Export DEX_BigStepWithTypes.
Import  DEX_BigStep.DEX_BigStep DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_Dom DEX_Prog.

Section p.
  Variable p : DEX_ExtendedProgram.

Hint Resolve L.join_least L.join_right L.join_left L.leql_trans L.leql_refl : lat.

Lemma join_sym : forall a b, L.join a b = L.join b a. intros. destruct a, b; auto. Qed.

Definition border (b1 b2:FFun.t DEX_Location) : Prop :=
  forall loc n, FFun.lookup b1 n = Some loc -> FFun.lookup b2 n = Some loc.

Lemma border_refl : forall b, border b b.
Proof.
  repeat intro; auto.
Qed.

Lemma border_trans : forall b1 b2 b3, border b1 b2 -> border b2 b3 -> border b1 b3.
Proof.
  unfold border; intros.
  firstorder.
Qed.

Lemma border_extends : forall b loc, border b (FFun.extends b loc).
Proof.
  repeat intro.
  apply FFun.extends_old; auto.
Qed.

Hint Resolve border_refl border_extends.

Lemma well_types_imply_exec_return : forall se region m sgn i s1 rt1 b1 rv2 ,
     DEX_BigStepAnnot.DEX_exec_return p m s1 rv2 -> 
     instructionAt m (fst s1) = Some i ->
     DEX_typing_rules.texec p sgn region se (fst s1) i rt1 None ->
     exists b2, exec_return p se m sgn i s1 rt1 b1 rv2 b2 /\ border b1 b2.
Proof.
  intros se region m sgn i s1 rt1 b1 rv2 He.
  inversion_clear He; intros.
  exists b1. split.
  constructor.
  inversion_mine H; simpl in H0; DiscrimateEq; inversion_mine H1.
  constructor; auto. 
  constructor 2 with t k_r kv; auto.
  simpl in H11. 
  rewrite join_sym in H13; auto.
  auto.
Qed.

Lemma well_types_imply_NormalStep : forall kobs se region m sgn i s1 rt1 b1 s2 rt2,
     DEX_BigStep.DEX_NormalStep p m s1 s2  ->
     instructionAt m (fst s1) = Some i ->
     texec p sgn region se (fst s1) i rt1 (Some rt2) ->
     exists b2, NormalStep kobs p se region m sgn i s1 rt1 b1 s2 rt2 b2 
        /\ border b1 b2.
Proof.
  intros kobs se region m sgn i s1 rt1 b1 s2 t2 H.
  inversion_clear H; simpl; intros Hi Ht;
  DiscrimateEq; 
  unfold NormalStep;
  inversion_mine Ht;
    try (try (exists b1; split; auto);
    try (econstructor;eauto); try (rewrite join_sym; auto); fail). 
  (* Ibinop *) 
  exists b1; split; auto.
    assert (forall a b c, L.join (L.join a b) (c) = L.join a (L.join b c)).
      intros; destruct a,b,c; auto.
    rewrite H; econstructor; eauto.
  (* New *)
  exists (newb kobs (se pc) b1 loc). split; auto.
  econstructor; eauto. 
  unfold newb. destruct (L.leql_dec (se pc) kobs); auto.
  (* Iput *)
  exists b1; split; auto.
  econstructor; eauto. 
  assert (forall a b c, L.join (L.join a b) (c) = L.join a (L.join b c)).
      intros; destruct a,b,c; auto.
  rewrite join_sym; rewrite H. 
  assert (L.join (DEX_ft p f) ko = L.join ko (DEX_ft p f)); rewrite join_sym; auto.
  rewrite join_sym.
  rewrite H8; auto.
Qed.

Lemma well_types_imply_exec_intra : forall kobs se region m sgn i s1 rt1 b1 s2 rt2,
     DEX_BigStepAnnot.DEX_exec_intra p m s1 s2  -> 
     instructionAt m (fst s1) = Some i ->
     texec p sgn region se (fst s1) i rt1 (Some rt2) ->
     exists b2, exec_intra kobs p se region m sgn i s1 rt1 b1 s2 rt2 b2 /\ border b1 b2.
Proof.
  intros kobs se region m sgn i s1 rt1 b1 s2 rt2 He.
  inversion_clear He; intros. 
  elim well_types_imply_NormalStep with (1:=H) (3:=H1) (kobs:=kobs) (b1:=b1); eauto.
  intros b [T1 T2].
  exists b; split; auto.
  constructor; auto.
Qed.

End p.