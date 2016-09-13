Require Export DEX_typing_rules.
(* Require Export DEX_compat. *)
Require Export DEX_BigStepWithTypes.
Import  DEX_BigStep.DEX_BigStep DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_Dom DEX_Prog.

(* Ltac inv_compat H :=
destruct H as [_ [Hcompat_l Hcompat_os]]; simpl in Hcompat_os;
repeat match goal with
         [ id : compat_value _ _ (Ref _) _ /\ _  |-_ ] => 
         let h := fresh in (
           destruct id as [h id];
           inversion_mine h; DiscrimateEq)
       | [ id : compat_value _ _ _ _ /\ _  |-_ ] => destruct id as [_ id]
       end.
 *)

Section p.
  Variable p : DEX_ExtendedProgram.

(* Lemma findMethod_signature : forall p mid m,
  findMethod p mid = Some m -> 
  snd mid = METHOD.signature m.
Proof.
  unfold findMethod; intros until m.
  destruct mid.
  destruct PROG.class; intros; try discriminate.
  apply CLASS.method_signature_prop with c0; assumption.
Qed.

Lemma lookup_signature : forall p cl mid cnm,
  lookup p cl mid cnm -> mid = METHOD.signature (snd cnm). 
Proof.
  induction 1.
  inversion_clear H; simpl.
  unfold findMethod in H0.
  destruct (PROG.class p0); try discriminate.
  eapply CLASS.method_signature_prop; eauto.
  auto.
Qed.

Lemma well_types_imply_CalledSign_return : forall (sub_dec:ClassName->ClassName->bool) se region m sgn 
  i s1 st1 tau s0  m2 r r2,
  @BigStepAnnot.exec_call (throwableBy p) p.(prog) m tau s1 r m2 s0 (inr _ r2) ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i tau st1 None ->
  exists sgn2, CalledSignature p i st1 sgn2.
Proof.
  intros.
  inversion_mine H.
  inversion_mine H3; simpl in H0; DiscrimateEq; inversion_mine H1.
  exists (static_signature p (snd mid)); constructor 1; auto.
  exists (virtual_signature p mid k1); constructor 2 with (mid:=(cn0,mid)); auto.
Qed.

Lemma well_types_imply_CalledSign_normal : forall (sub_dec:ClassName->ClassName->bool) se region m sgn
  i s1 st1 tau s0 m2 r s2 st2,
  @BigStepAnnot.exec_call (throwableBy p) p.(prog) m tau s1 r m2 s0 (inl _ s2) ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i tau st1 (Some st2) ->
  exists sgn2, CalledSignature p i st1 sgn2.
Proof.
  intros.
  inversion_mine H;
  inversion_mine H3; simpl in H0; DiscrimateEq; inversion_mine H1.
  exists (static_signature p (snd mid)); constructor; auto.
  exists (virtual_signature p mid k1); constructor 2 with (mid:=(cn,mid)); auto.
  exists (static_signature p (snd mid)); constructor; auto.
  exists (virtual_signature p mid k1); constructor 2 with (mid:=(cn0,mid)); auto.
Qed.


Lemma well_types_imply_CallStep_return : forall kobs  (sub_dec:ClassName->ClassName->bool) se region m sgn
  i s1 st1 b1 tau s0 m2 br r r2 sgn2,
  BigStepAnnot.exec_call (throwableBy p) p.(prog) m tau s1 r m2 s0 (inr _ r2) ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i tau st1 None ->
  CalledSignature p i st1 sgn2 ->
  exists b3,
  BigStepWithTypes.exec_call kobs p se region m sgn i s1 st1 b1 r br m2 sgn2 s0 nil b1 (inr _ r2) b3 tau
  /\ (b3 = b1 \/ b3 = br).
Proof.
  intros.
  inversion_mine H; inversion_mine H4; simpl in H0; DiscrimateEq.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros ;subst.
  exists (chooseb kobs (se pc1) br b1).
  split.
  assert (HH:=findMethod_signature _ _ _ H16).
  generalize (BigStepWithTypes.exec_call_uncaught kobs p se region m sgn (Invokestatic mid) m2 pc1 
                    h1 (args++os) l1 os
                    (stack2localvar (args ++ os) (length args)) h2 loc bM 
                    (st0++st2) st2 b1 br (chooseb kobs (se pc1) br b1)
                    (static_signature p (snd mid))
                    cn None (se pc1)).
  rewrite <- HH.
  intros T; apply T; clear T; auto.
  constructor 1 with bM; auto.
  rewrite <- HH in H13; auto.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros; subst.
  inversion_mine H11; clear H0.
  exists (chooseb kobs k1 br b1); split.
  assert (HH:= lookup_signature _ _ _ _ H16).
  generalize (exec_call_uncaught kobs p se region m sgn (Invokevirtual (cn0,mid)) m2 pc1 
                    h1  (args++Ref loc0::os) l1 os
                    (stack2localvar (args ++ Ref loc0:: os) (S(length args))) h2 loc bM 
                    (st0++L.Simple k1::st2) st2 b1 br (chooseb kobs k1 br b1)
                    (virtual_signature p mid k1)
                    cn (Some k1) k1).
  simpl in HH; rewrite <- HH.
  intros T; apply T; clear T; auto.
  replace (virtual_signature p mid) with (virtual_signature p (snd (cn0,mid))).
  replace (S (length args)) with (1+(length args))%nat.
  constructor 2 with cn0 cl bM; auto.
  auto.
  auto.
  rewrite <- HH in H13; auto.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
Qed.

Notation throwableBy := (throwableBy p).

Lemma well_types_imply_CallStep_normal : forall kobs (sub_dec:ClassName->ClassName->bool) se region m sgn
  i s1 st1 b1 tau s2 s0 m2 br r st2 sgn2,
  BigStepAnnot.exec_call throwableBy p m tau s1 r m2 s0 (inl _ s2) ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i tau st1 (Some st2) ->
  CalledSignature p i st1 sgn2 ->
  exists b3,
  exec_call kobs p se region m sgn i s1 st1 b1 r br m2 sgn2 s0 nil b1 (inl _ (s2,st2)) b3 tau
  /\ (b3 = b1 \/ b3 = br).
Proof.
  intros.
  inversion_mine H; inversion_mine H4; simpl in H0; DiscrimateEq.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros ;subst.
      exists (chooseb kobs (se pc1) br b1); split.
  assert (HH:=findMethod_signature _ _ _ H15).
  generalize (exec_call_normal kobs p se region m sgn (Invokestatic mid) m2 pc1 pc1' 
                    h1 (args++os) l1 os
                    (stack2localvar (args ++ os) (length args)) h2 bM ov
                    (st0++st3) st3 b1 br (chooseb kobs (se pc1) br b1)
                    (static_signature p (snd mid))
                    None (se pc1)).
  rewrite <- HH.
  intros T; apply T; clear T; auto.
  constructor 1 with bM; auto.
  rewrite <- HH in H12.
  inversion_clear H10 in H12; inversion H12; try constructor.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros; subst.
  inversion_mine H9; clear H0.  
  exists (chooseb kobs k1 br b1); split.
  assert (HH:= lookup_signature _ _ _ _ H15).
  generalize (exec_call_normal kobs p se region m sgn (Invokevirtual (cn,mid)) m2 pc1 pc1' 
                    h1 (args++Ref loc::os) l1 os
                    (stack2localvar (args ++ Ref loc :: os) (S (length args))) h2 bM ov
                    (st0++L.Simple k1::st3) st3 b1 br (chooseb kobs k1 br b1)
                    (virtual_signature p mid k1)
                    (Some k1) k1).
  simpl in HH; simpl; rewrite <- HH.
  intros T; apply T; clear T; auto.
  replace (virtual_signature p mid) with (virtual_signature p (snd (cn,mid))).
  replace (S (length args)) with (1+(length args))%nat.
  constructor 2 with cn cl bM; auto.
  auto.
  auto.
  rewrite <- HH in H12.
  inversion_clear H10 in H12; inversion H12; try constructor.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros ;subst.
      exists (chooseb kobs (se pc1) br b1); split.
  assert (HH:=findMethod_signature _ _ _ H16).
  generalize (exec_call_caught kobs p se region m sgn (Invokestatic mid) m2 pc1 pc1' 
                    h1 (args++os) l1 os
                    (stack2localvar (args ++ os) (length args)) h2 loc bM 
                    (st0++st3) st3 b1 br (chooseb kobs (se pc1) br b1)
                    (static_signature p (snd mid))
                    cn None (se pc1)).
  rewrite <- HH.
  intros T; apply T; clear T; auto.
  constructor 1 with bM; auto.
  rewrite <- HH in H13; auto.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
  (**)
  inversion_mine H1.
  inversion H2; subst.
  elim (app_inj L.t') with (2:=H0); intros; subst.
  inversion_mine H3; clear H0.  
  exists (chooseb kobs k1 br b1); split.
  assert (HH:= lookup_signature _ _ _ _ H16).
  generalize (exec_call_caught kobs p se region m sgn (Invokevirtual (cn0,mid)) m2 pc1 pc1' 
                    h1 (args++Ref loc0::os) l1 os
                    (stack2localvar (args ++ Ref loc0:: os) (S(length args))) h2 loc bM 
                    (st0++L.Simple k1::st3) st3 b1 br (chooseb kobs k1 br b1)
                    (virtual_signature p mid k1)
                    cn (Some k1) k1).
  simpl in HH; rewrite <- HH.
  intros T; apply T; clear T; auto.
  replace (virtual_signature p mid) with (virtual_signature p (snd (cn0,mid))).
  replace (S (length args)) with (1+(length args))%nat.
  constructor 2 with cn0 cl bM; auto.
  auto.
  auto.
  rewrite <- HH in H13; auto.
  unfold chooseb; destruct L.leql_dec; auto.
  congruence.
Qed.

Lemma well_types_imply_JVMExceptionStep : forall (sub_dec:ClassName->ClassName->bool) se region m sgn i s1 st1 k2 e,
  BigStep.JVMExceptionStep p m s1 e ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i (Some (javaLang,e)) st1 (Some (k2::nil)) ->
  compat_state p sgn s1 st1 ->
  JVMExceptionStep p m sgn i s1 st1 k2 e.
Proof.
  intros sub_dec se region m sgn i s1 st1 k2 e H.
  inversion_clear H; simpl; intros Hi Ht; DiscrimateEq;
  inversion_mine Ht; simpl;
  try (constructor; auto).
  inv_compat H4.
  eapply vaload_ArrayIndexOutOfBoundsException; eauto.
  inv_compat H5.
  eapply vastore_ArrayIndexOutOfBoundsException; eauto.
  inv_compat H6.
  eapply vastore_ArrayStoreException; eauto.
Qed.

Definition border (b1 b2:FFun.t Location) : Prop :=
  forall loc n, b1 n = Some loc -> b2 n = Some loc.

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

Lemma well_types_imply_ExceptionStep : forall (sub_dec:ClassName->ClassName->bool) kobs se region m sgn i s1 st1 b1 k2 e loc h,
  BigStepAnnot.ExceptionStep throwableAt p m s1 (h,loc) ->
  Heap.typeof h loc = Some (Heap.LocationObject e) ->
  instructionAt m (fst s1) = Some i ->
  texec p sub_dec m sgn region se (fst s1) i (Some e) st1 (Some (k2::nil)) ->
  compat_state p sgn s1 st1 ->
  exists b2, 
    ExceptionStep kobs p m sgn i s1 st1 b1 (h,loc) k2 b2 e /\
    border b1 b2.
Proof.
  intros sub_dec kobs se region m sgn i s1 st1 b1 k2 e loc h H.
  inversion_clear H; simpl; intros Hh Hi Ht; DiscrimateEq.
  exists b1; split; auto.
  inversion_mine Ht; subst; simpl;
  try (constructor; auto).
  intros [T1 T2].
  generalize (@Heap.new_typeof _ _ _ _ _ H1); intros; DiscrimateEq.
  exists (newb kobs k2 b1 loc); split.
  constructor; auto.
  eapply well_types_imply_JVMExceptionStep; eauto.
  constructor; auto.
  unfold newb; destruct L.leql_dec; auto.
Qed.
 *)
Hint Resolve L.join_least L.join_right L.join_left L.leql_trans L.leql_refl : lat.

Lemma join_sym : forall a b, L.join a b = L.join b a. intros. destruct a, b; auto. Qed.

Lemma well_types_imply_exec_return : forall (*sub_dec:ClassName->ClassName->bool*) se region m sgn i s1 rt1 rv2 (* tau *),
     DEX_BigStepAnnot.DEX_exec_return (* throwableAt *) p m (* tau *) s1 rv2 -> 
     instructionAt m (fst s1) = Some i ->
     DEX_typing_rules.texec (* p (* sub_dec *) m *) sgn region se (fst s1) i (* tau *) rt1 None ->
(*      compat_state p sgn s1 st1 -> *)
(*      exists b2, *)
     exec_return p se (* region *) m sgn i (* tau *) s1 rt1 rv2
(*      /\ border b1 b2. *).
Proof.
  intros (* sub_dec *) se region m sgn i s1 rt1 rv2 (* tau *) He.
  inversion_clear He; intros. 
  constructor.
  inversion_mine H; simpl in H0; DiscrimateEq; inversion_mine H1.
  constructor; auto. 
  constructor 2 with t k_r kv; auto.
  simpl in H11. 
(*   assert (forall a b, L.join a b = L.join b a); intros. destruct a, b; auto. *)
  rewrite join_sym in H13; auto.
  (* (* exceptions *)
  simpl in *.
  inversion_mine H; DiscrimateEq.
  exists b1; split; auto.
  inversion_mine H3.
  constructor 2 with k; auto.
  constructor; auto.
  generalize (@Heap.new_typeof _ _ _ _ _ H13); intros; DiscrimateEq.
  inversion_mine H9; DiscrimateEq; inversion_mine H3; DiscrimateEq;
  try (exists (newb kobs (L.head k) b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with (L.head k); auto; constructor; auto; constructor; auto).
  (exists (newb kobs k b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k; auto; constructor; auto; constructor; auto).
  (exists (newb kobs k b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k; auto; constructor; auto; constructor; auto).
  (exists (newb kobs k1 b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k1; auto; constructor; auto; constructor; auto).
  (exists (newb kobs (L.join k1 (L.join k1 (resExceptionType (virtual_signature p (snd mid) k1) np))) b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with (L.join k1 (L.join k1 (resExceptionType (virtual_signature p (snd mid) k1) np))); auto).
  constructor; auto.
  constructor; auto.
  intros.
  assert (HH:=H9 _ H).
  eauto with lat.
  eauto with lat.
  (exists (newb kobs k b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k; auto; constructor; auto; constructor; auto).
  (exists (newb kobs k2 b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k2; auto; constructor; auto; constructor; auto).
  (exists (newb kobs k2 b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with k2; auto; constructor; auto; constructor; auto).
  (exists (newb kobs (L.join k1 k2) b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with (L.join k1 k2); auto; constructor; auto).
  inv_compat H4.
  unfold JVMExceptionStep.
  constructor 2 with length0 tp; auto.
  (exists (newb kobs ka b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with ka; auto; constructor; auto; constructor; auto).
  inv_compat H4.
  (exists (newb kobs (L.join ki ka) b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with (L.join ki ka); auto; try constructor; auto).
  econstructor 2; eauto.
  inv_compat H4.
  (exists (newb kobs (L.join kv (L.join ki ka)) b1 loc2); split;   
    [idtac|unfold newb; destruct L.leql_dec; auto];
    constructor 2 with (L.join kv (L.join ki ka)); auto; try constructor; auto).
  constructor 3 with tp length0; auto. *)
Qed.

Lemma well_types_imply_NormalStep : forall (* sub_dec *) (* kobs *) se region m sgn i s1 rt1 s2 rt2,
     DEX_BigStep.DEX_NormalStep p m s1 s2  ->
     instructionAt m (fst s1) = Some i ->
     texec (*p sub_dec m*) sgn region se (fst s1) i (* None *) rt1 (Some rt2) ->
(*      compat_state p sgn s1 st1 -> *)
(*      exists b2, *)
       NormalStep (* kobs *) (* p *) se region m sgn i s1 rt1 s2 rt2 
(*        /\ border b1 b2. *).
Proof.
  intros (* sub_dec kobs *) se region m sgn i s1 rt1 s2 t2 H.
  inversion_clear H; simpl; intros Hi Ht; 
  DiscrimateEq; 
  unfold NormalStep;
  inversion_mine Ht; (*  ; subst; *)
    try (constructor;auto). 
  (* Move *) constructor 1 with (val := v) (k:=k_rs); auto. rewrite join_sym; auto.
  (* Ifcmp *) 
  constructor 1 with (i1:=va) (i2:=vb) (k1:=ka) (k2:=kb); auto. 
  constructor 2 with (i1:=va) (i2:=vb) (k1:=ka) (k2:=kb); auto.
  (* Ifz *)
  constructor 1 with (i:=v) (k:=k); auto. 
  constructor 2 with (i:=v) (k:=k); auto.
  (* Ineg *) constructor 1 with (v:=v) (k:=ks); auto. rewrite join_sym; auto.
  (* Inot *) constructor 1 with (v:=v) (k:=ks); auto. rewrite join_sym; auto.
  (* I2b *) constructor 1 with (v:=v) (k:=ks); auto. rewrite join_sym; auto.
  (* I2s *) constructor 1 with (v:=v) (k:=ks); auto. rewrite join_sym; auto.
  (* Ibinop *) constructor 1 with (i1:=va) (i2:=vb) (k1:=ka) (k2:=kb); auto. 
    assert (forall a b c, L.join (L.join a b) (c) = L.join a (L.join b c)).
      intros; destruct a,b,c; auto.
    rewrite H; auto.
  (* IbinopConst *) constructor 1 with (i:=va) (k:=ks); auto.
  (* (exists b1; split; [idtac|apply border_refl]).
  eapply arraylength; eauto.
  (exists b1; split; [idtac|apply border_refl]).
  eapply getfield; eauto.
  (exists b1; split; [idtac|apply border_refl]).
  eapply lookupswitch1; eauto.
  exists (newb kobs (se pc) b1 loc); split.
  eapply new; eauto.
  unfold newb; destruct L.leql_dec; auto.
  exists (newb kobs k b1 loc); split.
  eapply newarray; eauto.
  unfold newb; destruct L.leql_dec; auto.
  (exists b1; split; [idtac|apply border_refl]).
  apply (putfield p se region f m sgn h pc pc' s l loc cn v k1 k2 st b1); eauto.
  (exists b1; split; [idtac|apply border_refl]).
  eapply tableswitch2; eauto.
  (exists b1; split; [idtac|apply border_refl]).
  inv_compat H7; try assumption.
  eapply vaload; eauto; DiscrimateEq.
  (exists b1; split; [idtac|apply border_refl]).
  inv_compat H7; try assumption.
  apply (vastore p se region k m sgn h pc pc' s l loc val i0 length0 tp kv ki ka mpc b1 st); DiscrimateEq; eauto. *)
Qed.

Lemma well_types_imply_exec_intra : forall (* (sub_dec:ClassName->ClassName->bool) kobs *) se region m sgn i s1 rt1 s2 rt2 (* tau *),
     DEX_BigStepAnnot.DEX_exec_intra (* throwableAt *) p m (* tau *) s1 s2  -> 
     instructionAt m (fst s1) = Some i ->
     texec (* p sub_dec m *) sgn region se (fst s1) i (* tau *) rt1 (Some rt2) ->
(*      compat_state p sgn s1 rt1 -> *)
(*      exists b2, *)
       exec_intra (* kobs p *) se region m sgn i (* tau *) s1 rt1 s2 rt2.
(*        /\ border b1 b2. *)
Proof.
  intros (* sub_dec kobs *) se region m sgn i s1 rt1 s2 rt2 (* tau *) He.
  inversion_clear He; intros. 
  constructor; auto.
  apply well_types_imply_NormalStep; auto.
(* 
  elim well_types_imply_NormalStep with (1:=H) (3:=H1) ; eauto.
  intros b2 [T1 T2].
  exists b2; split; auto.
  constructor; auto.
  cut (exists k2, st2 = L.Simple k2::nil).
  intros [k2 Hk2]; subst.
  elim (well_types_imply_ExceptionStep 
   sub_dec kobs se region m sgn i (pc1, (h1, s0, l1)) st1 b1 (L.Simple k2) e loc2 h2);
  auto.
  intros b2 [T1 T2].
  exists b2; split; auto. 
  constructor; auto.
  inversion_mine H3; auto.
  inversion_mine H; simpl in *; DiscrimateEq.
  inversion_mine H11; simpl in *; DiscrimateEq.
  simpl in *; intros.
  apply L.join_least.
  apply L.leql_trans with (L.join (resExceptionType (virtual_signature p (snd mid) k1) e) k1); auto.
  apply L.join_right.
  apply L.join_least.
  apply L.leql_trans with (L.join (resExceptionType (virtual_signature p (snd mid) k1) e) k1); auto.
  apply L.join_right.
  apply L.leql_trans with (L.join (resExceptionType (virtual_signature p (snd mid) k1) e) k1); auto.
  apply L.join_left.
  simpl in *.
  inversion_mine H; DiscrimateEq; try assumption.
  generalize (@Heap.new_typeof _ _ _ _ _ H13); intros; DiscrimateEq; assumption.
  simpl in H2.
  inversion_mine H3; eauto. *)
Qed.

End p.

