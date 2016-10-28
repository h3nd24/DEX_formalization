Require Export DEX_typing_rules.
Require Export DEX_BigStepWithTypes.
Import  DEX_BigStep.DEX_BigStep DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_Dom DEX_Prog.

Section p.
  Variable p : DEX_ExtendedProgram.

Hint Resolve L.join_least L.join_right L.join_left L.leql_trans L.leql_refl : lat.

Lemma join_sym : forall a b, L.join a b = L.join b a. intros. destruct a, b; auto. Qed.

Lemma well_types_imply_exec_return : forall se region m sgn i s1 rt1 rv2 ,
     DEX_BigStepAnnot.DEX_exec_return p m s1 rv2 -> 
     instructionAt m (fst s1) = Some i ->
     DEX_typing_rules.texec sgn region se (fst s1) i rt1 None ->
      exec_return p se m sgn i s1 rt1 rv2.
Proof.
  intros se region m sgn i s1 rt1 rv2 He.
  inversion_clear He; intros. 
  constructor.
  inversion_mine H; simpl in H0; DiscrimateEq; inversion_mine H1.
  constructor; auto. 
  constructor 2 with t k_r kv; auto.
  simpl in H11. 
  rewrite join_sym in H13; auto.
Qed.

Lemma well_types_imply_NormalStep : forall se region m sgn i s1 rt1 s2 rt2,
     DEX_BigStep.DEX_NormalStep p m s1 s2  ->
     instructionAt m (fst s1) = Some i ->
     texec sgn region se (fst s1) i rt1 (Some rt2) ->
       NormalStep se region m sgn i s1 rt1 s2 rt2.
Proof.
  intros se region m sgn i s1 rt1 s2 t2 H.
  inversion_clear H; simpl; intros Hi Ht; 
  DiscrimateEq; 
  unfold NormalStep;
  inversion_mine Ht;
    try (econstructor;eauto); try (rewrite join_sym; auto). 
  (* Ibinop *) 
    assert (forall a b c, L.join (L.join a b) (c) = L.join a (L.join b c)).
      intros; destruct a,b,c; auto.
    rewrite join_sym. rewrite H; auto.
Qed.

Lemma well_types_imply_exec_intra : forall se region m sgn i s1 rt1 s2 rt2,
     DEX_BigStepAnnot.DEX_exec_intra p m s1 s2  -> 
     instructionAt m (fst s1) = Some i ->
     texec sgn region se (fst s1) i rt1 (Some rt2) ->
       exec_intra se region m sgn i s1 rt1 s2 rt2.
Proof.
  intros se region m sgn i s1 rt1 s2 rt2 He.
  inversion_clear He; intros. 
  constructor; auto.
  apply well_types_imply_NormalStep; auto.
Qed.

End p.