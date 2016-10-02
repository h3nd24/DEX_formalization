Require Export DEX_Framework.
Require Export DEX_ProofBigStepWithType.
Require Export DEX_ElemLemmas.
Require Export DEX_ElemLemmaIntra.
Require Export DEX_ElemLemmaReturn.
(* Require Export ElemLemmaCall1.
Require Export ElemLemmaSideEffect. *)
Require DEX_compat. 
Require Export DEX_step.
Require Export DEX_typing_rules.

Import DEX_BigStepWithTypes DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Definition ValidMethod (p:DEX_Program) (m:DEX_Method) : Prop :=
  exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

Definition step (p:DEX_Program) (* subclass_test *) : DEX_Method -> DEX_PC (* -> option DEX_ClassName *) -> option DEX_PC -> Prop := 
fun m pc (* tau *) opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ DEX_step (*p subclass_test *) m pc i (* None *) opc.

Section hyps.
  Variable kobs: L.t.
  Variable p : DEX_ExtendedProgram.
  (* Variable subclass_test : ClassName -> ClassName -> bool.
  Variable subclass_test_correct : forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2. *)

  Definition PC := DEX_PC.
  Definition Method := DEX_Method.
  Definition Kind := option DEX_ClassName.
  Definition Sign : Set :=  DEX_sign.

  Definition PM := ValidMethod.

  Inductive P : SignedMethod Method Sign -> Prop :=
    P_def : forall (m:DEX_Method) sgn,
      ValidMethod p m ->
      (DEX_METHOD.isStatic m = true -> sgn = DEX_static_signature p (DEX_METHOD.signature m)) ->
      (DEX_METHOD.isStatic m = false -> exists k, sgn = DEX_virtual_signature p (DEX_METHOD.signature m) k) ->
      P (SM _ _ m sgn).

  Section for_all.
    Variable test : DEX_METHOD.t -> Sign -> bool.
    
    Definition for_all_P : bool :=
      for_all_methods p 
      (fun m => 
        if DEX_METHOD.isStatic m then test m (DEX_static_signature p (DEX_METHOD.signature m))
          else for_all _ (fun k => test m (DEX_virtual_signature p (DEX_METHOD.signature m) k)) L.all).

    Lemma for_all_P_true : for_all_P = true ->
      forall m sgn, P (SM _ _ m sgn) -> test m sgn = true.
    Proof.
      unfold for_all_P; intros.
      inversion_mine H0.
      generalize (for_all_methods_true _ _ H _ H3).
      caseeq (DEX_METHOD.isStatic m); intros.
      rewrite <- H4 in H1; auto.
      generalize (for_all_true _ _ _ H1); intros.
      elim H5; auto.
      intros k Hk.
      rewrite Hk; apply H2.
      apply L.all_in_all.
    Qed.
  
  End for_all.

  Lemma PM_P : forall m, P m -> PM p (unSign _ _ m).
  Proof.
    intros.
    inversion_clear H; auto.
  Qed.

  Notation step := (step p (* subclass_test *)).
  Variable cdr : forall m, PM p m -> CDR (step m).

  Definition istate : Type := DEX_IntraNormalState.
  Definition rstate : Type := DEX_ReturnState.
  Inductive exec : Method -> (*nat -> Kind ->*) istate -> istate + rstate -> Prop :=
  | exec_intra : forall (m:Method) (* tau *) s1 s2,
    DEX_BigStepAnnot.DEX_exec_intra p m s1 s2 -> 
    exec m (* tau *) s1 (inl _ s2)
  | exec_return : forall (m:Method) (* tau *) s ret,
    DEX_BigStepAnnot.DEX_exec_return p m s ret ->
    exec m (* tau *) s (inr _ ret).
  (* | exec_call : forall (m:Method) n tau s1 ret' (m':Method) s' r,
    BigStepAnnot.exec_call (throwableBy p) p m tau s1 ret' m' s' r ->
    evalsto m' n s' ret' ->
    exec m (S n) tau s1 r *)

  Inductive evalsto : Method -> (* nat -> *) istate -> rstate -> Prop :=
  | evalsto_return : forall (m:Method) (* tau *) s r,
    exec m (* tau *) s (inr _ r) ->
    evalsto m (* 1 *) s r
  | evalsto_intra : forall (m:Method) (*n n1 n2 tau *) s1 s2 r,
    exec m (* tau *) s1 (inl _ s2) ->
    evalsto m (* n *) s2 r ->
    evalsto m (* (S (n)) *) s1 r. 

  Definition pc : istate -> PC := @fst _ _.

  Definition registertypes : Type := TypeRegisters.
  (* Definition pbij : Set := FFun.t Location. *)

  Definition texec : forall m, PM p m -> Sign -> (PC -> L.t) ->
    PC -> (* Kind -> *) registertypes -> option registertypes -> Prop :=
    fun m H sgn se pc (* tau *) rt ort =>
      exists i, texec (*p subclass_test m*) sgn (region (cdr m H)) se pc i (* None *) rt ort
        /\ instructionAt m pc = Some i.

  Definition compat : Sign -> istate -> registertypes -> Prop := 
    DEX_compat.compat_state.
  Definition compat_res : Sign -> rstate -> Prop :=
    DEX_compat.compat_res.

  Inductive indist : Sign -> registertypes ->
    registertypes -> (* pbij -> pbij ->*) istate -> istate -> Prop :=
    indist_def :forall sgn rt1 rt2 (* b1 b2 *) r1 r2 pc1 pc2 (* h1 h2  l1 l2*),
      st_in kobs (* (newArT p) (ft p) sgn.(lvt) b1 b2 *) rt1 rt2 (pc1,r1) (pc2,r2) ->
      indist sgn rt1 rt2 (pc1,r1) (pc2,r2).

(*   Inductive irindist : Sign -> stacktype -> pbij -> pbij -> istate -> rstate -> Prop :=
  | irindist_def : forall sgn b1 b2 s1 st1 v2 h2,
    indist_intra_return kobs p sgn s1 st1 b1 h2 v2 b2 ->
    irindist sgn st1 b1 b2 s1 (h2,v2). *)

  Inductive rindist : Sign -> (* pbij -> pbij ->*) rstate -> rstate -> Prop :=
  | rindist_def : forall sgn (* b1 b2 h1 h2 *) r1 r2,
(*     hp_in kobs (newArT p) (ft p) b1 b2 h1 h2 -> *)
    indist_return_value kobs sgn (* h1 h2 *) r1 r2 (* b1 b2 *) ->
    rindist sgn (* b1 b2 *) (* (h1, *) r1 (* ) (h2, *) r2(* ) *).

(*   Lemma lookup_findMethod : forall p c msig cm,
    lookup p c msig cm ->
    findMethod p (fst cm,msig) = Some (snd cm).
  Proof.
    induction 1; auto.
    inversion_mine H; auto.
  Qed.

  Lemma findMethod_P : forall m mid,
    findMethod p mid = Some m -> ValidMethod p m.
  Proof.
    destruct mid as [cn mid]; simpl.
    caseeq (PROG.class p.(prog) cn).
    intros cl T1 T2.
    exists cl.
    unfold PROG.defined_Class.
    rewrite <- (PROG.name_class_invariant1  _ _ _ T1); auto.
    unfold CLASS.defined_Method.
    rewrite <- (CLASS.method_signature_prop _ _ _ T2); auto.
    intros; discriminate.
  Qed.


  Lemma P_CallStep : forall se (m:P.Method) sgn i s1 st1 m2 os l2 sgn2 st' ok k b1' br b3,
    BigStepWithTypes.CallStep kobs p se m sgn i s1 st1 (m2, (os, l2)) sgn2 st' ok k b1' br b3 ->
    P (SM _ _ m sgn) -> P (SM _ _ m2 sgn2).
  Proof.
    intros.
    inversion_mine H; inversion_mine H0.
    constructor.
    eapply findMethod_P; eauto.
    rewrite (findMethod_signature _ _ _ H4); auto.
    intros; DiscrimateEq.
    generalize (lookup_findMethod _ _ _ _ H4); intros.
    constructor.
    eapply findMethod_P; eauto.
    intros; DiscrimateEq.
    intros; exists k.
    rewrite (lookup_signature _ _ _ _ H4); auto.
  Qed.

  Lemma P_exec_call : forall se region m sgn i s1 st1 r br b1' m2 sgn2 s0 st0 b1 s2 b3 tau,
    BigStepWithTypes.exec_call kobs p se region m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b1' s2 b3 tau ->
    P (SM _ _ m sgn) -> P (SM _ _ m2 sgn2).
  Proof.
    intros.
    inversion_mine H; eapply P_CallStep; eauto.
  Qed. *)

  Definition default_level := L.High.

  Inductive init_pc (m:Method) : PC -> Prop :=
    init_pc_def : forall bm,
      DEX_METHOD.body m = Some bm ->
      init_pc m (DEX_BYTECODEMETHOD.firstAddress bm).

(*   Lemma init_pc_exec_call : forall se region m sgn i s1 st1 r br b1' m2 sgn2 s0 st0 b1 s2 b3 tau,
    BigStepWithTypes.exec_call kobs p se region m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b1' s2 b3 tau ->
    init_pc m2 (pc s0).
  Proof.
    intros.
    inversion_mine H; simpl; constructor; auto.
  Qed. *)

(*   Inductive high_opstack : stacktype -> istate -> Prop :=
    high_opstack_def : forall pc s l h st,
      high_st kobs s st ->
      high_opstack st (pc,(h,s,l)). *)

  (* Definition s0 : stacktype := nil. *)
  Inductive rt0 (m:Method) (sgn:Sign): registertypes -> Prop := 
    rt0_def : forall bm, 
      DEX_METHOD.body m = Some bm ->
      P (SM _ _ m sgn) ->
      rt0 m sgn (Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level)).

 (*  Definition rt0 (m:Method) : registertypes := 
    Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level). *)


  Definition ni := ni _ _ _ _ _ exec pc registertypes indist rindist compat rt0 init_pc P.

  Open Scope nat_scope.

(*   Definition side_effect (sgn:Sign) (is:istate) (os:istate+rstate) : Prop :=
    match is with
      (pc,(h,s,l)) =>
      match os with
        | inl (pc',(h',s',l')) => side_effect (newArT p) (ft p) sgn.(heapEffect) h h'
        | inr (h',_) => side_effect (newArT p) (ft p) sgn.(heapEffect) h h'
      end
    end.

  Definition ses : nat -> Prop :=
    ses _ _ _ _ _ _ exec pc _ compat s0 init_pc side_effect P. *)

  Lemma evalsto_Tevalsto : forall m s r,
    evalsto m s r ->
    exists p, DEX_Framework.evalsto Method istate rstate exec m p s r.
  Proof.
(*     intros m n; pattern n; apply lt_wf_ind; clear n; intros. *)
    intros.
    induction H.
    exists 1; constructor 1; auto.
    inversion IHevalsto.
    exists (S x). constructor 2 with (s2:=s2); auto.
  Qed.

  Lemma tcc0 : forall m s s',
    PM p m -> exec m s (inl rstate s') -> step m (pc s) (Some (pc s')).
  Proof.
    intros m s s' HP H.
    split.
    auto.
    inversion_clear H.
    inversion_clear H0.
    inversion_clear H;
      match goal with
        | [ id : instructionAt _ _ = Some ?i |- _] =>
          exists i; simpl; split; [assumption|idtac]; constructor; 
            simpl; auto
      end.
  Qed.

  Lemma tcc1 : forall m s s',
    PM p m -> exec m s (inr istate s') -> step m (pc s) None.
  Proof.
    intros m s s' HM H.
    split; auto.
    inversion_clear H.
    inversion_clear H0.
    inversion_clear H.
    exists DEX_Return; simpl; split; auto; constructor.
    exists (DEX_VReturn k rs); simpl; split; auto; constructor.
  Qed.

(*   Lemma side_effect_trans : forall (m : Sign) (s1 s2 : istate) (s3 : istate + rstate),
    side_effect m s1 (inl rstate s2) ->
    side_effect m s2 s3 -> side_effect m s1 s3.
  Proof.
    unfold side_effect; intros sgn [pc1 [[h1 s1] l1]] [pc2 [[h2 s2] l2]].
    destruct s3 as [[pc3 [[h3 s3] l3]]|[h3 v3]].
    apply side_effect_trans.
    apply side_effect_trans.
  Qed. *)

  Lemma tcc6 : forall sgn m se s s' rt rt',
    ((* forall k : nat, (k < n)%nat -> *)
      cmp _ _ _ _ _ exec pc registertypes compat compat_res rt0 init_pc P) ->
    forall H0:P (SM Method Sign m sgn),
      exec m s (inl rstate s') ->
      texec m (PM_P _ H0) sgn se (pc s) rt (Some rt') ->
      compat sgn s rt -> 
      compat sgn s' rt'.
  Proof.
    intros.
    destruct H2 as [i [H2 Hi]].
    inversion_mine H1.
    (* eelim well_types_imply_exec_intra with (1:=H7) (2:=Hi) (3:=H2); eauto. *)
    assert (DEX_BigStepWithTypes.NormalStep se (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
        m sgn i s rt s' rt').
      elim well_types_imply_exec_intra with (1:=H7) (2:=Hi) (3:=H2); eauto.
    eapply DEX_compat.compat_intra; eauto.
    econstructor; eauto.
  Qed.

  Lemma tcc7 : forall sgn m se s r rt,
    ((* forall k : nat,
      (k < n)%nat -> *)
      cmp _ _ _ _ _ exec pc registertypes compat compat_res rt0 init_pc P) ->
    forall H0:P (SM Method Sign m sgn),
      exec m s (inr istate r) ->
      texec m (PM_P _ H0) sgn se (pc s) rt None ->
      compat sgn s rt -> compat_res sgn r.
  Proof.
    intros.
    destruct H2 as [i [H2 Hi]].
    inversion_mine H1.
    destruct r.
    assert (DEX_BigStepWithTypes.ReturnStep p se m sgn i s rt (Normal o)).
      elim well_types_imply_exec_return with (1:=H7) (2:=Hi) (3:=H2); eauto.
    eapply DEX_compat.compat_return; eauto. econstructor; eauto.
  Qed.

  (* Inductive sub : stacktype -> stacktype -> Prop :=
  | sub_nil : sub nil nil
  | sub_cons : forall x1 x2 st1 st2,
    L.leql' x1 x2 -> sub st1 st2 -> sub (x1::st1) (x2::st2). *)
  Inductive sub : registertypes -> registertypes -> Prop :=
  | forall_sub : forall rt1 rt2, eq_set (VarMap.dom _ rt1) (VarMap.dom _ rt2) ->
      (forall r k1 k2, Some k1 = VarMap.get _ rt1 r -> Some k2 = VarMap.get _ rt2 r -> L.leql k1 k2) 
      -> sub rt1 rt2
  | nil_sub : sub (VarMap.empty _) (VarMap.empty _). 

  Lemma sub_forall : forall rt rt', sub rt rt' -> 
    (forall r k1 k2, 
      Some k1 = VarMap.get _ rt r /\ Some k2 = VarMap.get _ rt' r -> 
    L.leql k1 k2).
  Proof. intros. inversion H0; auto.
    inversion H; subst. apply H4 with (r:=r); auto.
    rewrite VarMap.get_empty in H1. inversion H1.
  Qed.

  Lemma compat_register_sub : forall (rt1 rt2 : registertypes),
    sub rt1 rt2 -> forall r,
      DEX_compat.compat_registers r rt1 ->
      DEX_compat.compat_registers r rt2.
  Proof.
    induction 1; simpl; intuition.
    unfold DEX_compat.compat_registers in H0.
    unfold DEX_compat.compat_registers. 
    intros. destruct v; constructor; auto. 
  Qed.

  Lemma compat_sub : forall (sgn : Sign) (s : istate) (rt1 rt2 : registertypes),
    sub rt1 rt2 -> compat sgn s rt1 -> compat sgn s rt2.
  Proof.
    intros.
    destruct s.
    apply compat_register_sub with (r:=t) in H; auto.
  Qed.

  Lemma indist_morphism_proof : forall (y : Sign) (x y0 : registertypes),
    eq_rt x y0 ->
    forall x0 y1 : registertypes,
    eq_rt x0 y1 -> forall y2 y3 : istate, indist y x x0 y2 y3 <-> indist y y0 y1 y2 y3.
  Proof.
    split; intros.
    (* -> *)
    inversion_mine H1.
    constructor.
    inversion_mine H2.
    inversion_mine H3.
    constructor; constructor; intros.
      (* same domain *)
      inversion H; inversion H0.
      rewrite <- H3; rewrite <- H5; auto.
      (* indistinguishable contents *)
      assert (H':=H); assert (H0':=H0).
      inversion_mine H; inversion_mine H0.
      apply H2 with (rn:=rn) (v:=v) (v':=v') (k:=k) (k':=k'); auto.
      rewrite H9; auto.
      rewrite H; auto.
      rewrite eq_rt_get with (rt1:=x) (rt2:=y0); auto. rewrite H9; auto.
      rewrite eq_rt_get with (rt1:=x0) (rt2:=y1); auto. rewrite H; auto.
    (* -> *)
    inversion_mine H1.
    constructor.
    inversion_mine H2.
    inversion_mine H3.
    constructor; constructor; intros.
      (* same domain *)
      inversion H; inversion H0.
      rewrite H3; rewrite H5; auto.
      (* indistinguishable contents *)
      assert (H':=H); assert (H0':=H0).
      inversion_mine H; inversion_mine H0.
      apply H2 with (rn:=rn) (v:=v) (v':=v') (k:=k) (k':=k'); auto.
      rewrite <- H9; auto.
      rewrite <- H; auto.
      rewrite eq_rt_get with (rt1:=y0) (rt2:=x); auto. apply eq_rt_sym; auto. rewrite <- H9; auto.
      rewrite eq_rt_get with (rt1:=y1) (rt2:=x0); auto. apply eq_rt_sym; auto. rewrite <- H; auto.
  Qed.

  Lemma compat_morphism_proof : forall (y : Sign) (y0 : istate) (x y1 : registertypes),
    eq_rt x y1 -> compat y y0 x <-> compat y y0 y1.
  Proof.
    split; intros.
    (* -> *)
    unfold compat in H0; unfold DEX_compat.compat_state in H0; unfold DEX_compat.compat_registers in H0.
    unfold compat; unfold DEX_compat.compat_state; unfold DEX_compat.compat_registers.
    destruct y0.
    intros.
    assert (VarMap.get L.t y1 x0 <> None). unfold not; intros. rewrite H3 in H2; inversion H2.
    rewrite eq_rt_get with (rt2:=x) in H2.
      apply H0 with (x0:=x0) (v:=v) (k:=k) (1:=H1) (2:=H2). 
      apply eq_rt_sym; auto.
      apply VarMap.get_some_in_dom in H3; auto.
      apply VarMap.get_some_in_dom in H3. 
      inversion H. rewrite H4; auto.
    (* <- *)
    unfold compat in H0; unfold DEX_compat.compat_state in H0; unfold DEX_compat.compat_registers in H0.
    unfold compat; unfold DEX_compat.compat_state; unfold DEX_compat.compat_registers.
    destruct y0.
    intros.
    assert (VarMap.get L.t x x0 <> None). unfold not; intros. rewrite H3 in H2; inversion H2.
    rewrite eq_rt_get with (rt2:=y1) in H2; auto.
      apply H0 with (x:=x0) (v:=v) (k:=k) (1:=H1) (2:=H2). 
      apply VarMap.get_some_in_dom in H3; auto.
      apply VarMap.get_some_in_dom in H3; auto. 
      inversion H. rewrite <- H4; auto.
  Qed.

  Definition TypableProg := TypableProg PC Method step (PM p) Sign registertypes texec rt0 init_pc P PM_P sub eq_rt.

  Section TypableProg.

    Variable se : Method -> Sign -> PC -> L.t.
    Variable RT : Method -> Sign -> PC -> registertypes.
    Variable typable_hyp : TypableProg se RT.

    Lemma indist2_intra : forall m sgn se rt ut ut' s s' u u',
(*       (forall k, (k<N)%nat -> ni k) -> *)
      forall H0:P (SM _ _ m sgn),
        indist sgn rt rt (* b b' *) s s' ->
        pc s = pc s' ->
        exec m s (inl _ u) ->
        exec m s' (inl _ u') ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
        compat sgn s rt ->
        compat sgn s' rt ->
(*         exists bu, exists bu',
          border b bu /\
          border b' bu' /\ *)
          indist sgn ut ut' (* bu bu'  *) u u'.
    Proof.
      unfold pc; intros.
      inversion_mine H2. inversion_mine H3.
  (**)
      elim DEX_BigStepWithTypes.exec_intra_instructionAt with (1:=H11); intros i Hi.
      destruct H4 as [i' [Ti Ti']]; DiscrimateEq.
      
(*       elim well_types_imply_exec_intra with (1:=H11) (3:=Ti); auto. *)
      assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) m sgn i s rt u ut).
        elim well_types_imply_exec_intra with (1:=H11) (3:=Ti); eauto. 
(*       intros b2 [T1 T2]. *)
      destruct H5 as [i' [Ui Ui']]; DiscrimateEq.
      rewrite H1 in Ui.
(*       elim well_types_imply_exec_intra with (1:=H10) (3:=Ui); auto. *)
      assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) m sgn i s' rt u' ut').
        elim well_types_imply_exec_intra with (1:=H10) (3:=Ui); eauto.
      rewrite H1 in Ui'; auto. 
      inversion_mine H.
      destruct u as [pu ru].
      destruct u' as [pu' ru'].
      constructor.
      eapply indist2_intra; eauto. 
      constructor; eauto.
      rewrite H1; constructor; eauto.
      simpl. simpl in H1.
      rewrite <- H1 in H4; auto.
    Qed.

(*     Lemma tcc2 : forall m  rt1 rt2 rt3 s1 s2 s3,
      indist m rt1 rt2 s1 s2 ->
      indist m rt2 rt3 s2 s3 -> indist m rt1 rt3 s1 s3.
    Proof.
      intros.
      inversion_mine H; inversion_mine H0.
      inversion_mine H1; inversion_mine H7; do 2 constructor.
(*       apply localvar_in_trans with (2:=H3); auto. *)
(*       inversion_clear H10; auto. *)
      apply reg_in_trans with (1:=H0); auto.
      inversion_clear H10; auto.
      apply hp_in_trans with (1:=H10); auto.
    Qed. *)
    
    Lemma tcc3 : forall m rt1 rt2 s1 s2,
      indist m rt1 rt2 s1 s2 -> indist m rt2 rt1 s2 s1.
    Proof.
      intros.
      inversion_clear H; constructor.
      apply st_in_sym; auto.
    Qed.

    Lemma tcc4 : forall m s1 s2,
      rindist m s1 s2 -> rindist m s2 s1.
    Proof.
      intros. 
      inversion_clear H; constructor.
      inversion H0.
      constructor 1 with k; auto. intros; apply Value_in_sym; auto.
      constructor 2; auto.
    Qed.

(*     Lemma tcc5 : forall m st st' b b' br br' s s' res res',
      indist m st st' b b' s s' ->
      irindist m st b br s res ->
      irindist m st' b' br' s' res' -> rindist m br br' res res'.
    Proof.
      intros.
      inversion_mine H; inversion_mine H0; inversion_mine H1; constructor.
      inversion_mine H2; inversion_mine H; inversion_mine H0.
      apply hp_in_trans with (2:=H10).
      apply hp_in_trans with (2:=H12).
      apply hp_in_sym; auto.
      inversion_mine H2; inversion_mine H; inversion_mine H0.
      inversion_mine H14; inversion_mine H16; DiscrimateEq.
      constructor; auto.
      constructor 5 with cn; auto.
      constructor 1 with k0; intuition.
      constructor 5 with cn; auto.
      constructor 4 with cn; auto.
      constructor 4 with cn; auto.
      constructor 6 with cn cn0; auto.
    Qed.

    Definition border : pbij -> pbij -> Prop := beta_pre_order.

    Lemma tcc8 : forall b1 b2 b3 : pbij, border b1 b2 -> border b2 b3 -> border b1 b3.
    Proof.
      unfold border, beta_pre_order; intros.
      firstorder.
    Qed. *)


    Lemma indist_return_value_sym : forall sgn vu' vu,
(*       hp_in kobs (newArT p) (ft p) b b2' hu hu' -> *)
      indist_return_value kobs sgn vu' vu ->
      indist_return_value kobs sgn vu vu'.
    Proof.
      intros.
      inversion_clear H.
      constructor 1 with k; auto; intros.
      apply Value_in_sym; auto.
      constructor; auto.
      (* constructor 3 with cn; auto.
      rewrite <- H1.
      eapply indist_same_class; eauto.
      apply Value_in_sym; auto.
      apply Value_in_sym; auto.
      constructor 5 with cn; auto.
      constructor 4 with cn; auto.
      constructor 6 with cn2 cn1; auto. *)
    Qed.

    Lemma indist2_return : forall (m : Method) (sgn : Sign) (se : PC -> L.t) 
      (rt : registertypes) (*b b' : pbij*) (s s' : istate) 
      (u u' : rstate) (*N n n' : nat*) (*kd kd' : Kind*),
      (* (forall k : nat,
        k < N ->
        Framework.ni PC Method Kind Sign istate rstate exec pc stacktype pbij indist
        rindist compat s0 init_pc P border k) -> *)
      forall H:P (SM Method Sign m sgn),
        indist sgn rt rt s s' ->
        pc s = pc s' ->
        exec m s (inr istate u) ->
(*         n <= N -> *)
        exec m s' (inr istate u') ->
(*         n' <= N -> *)
        texec m (PM_P _ H) sgn se (pc s) rt None ->
        texec m (PM_P _ H) sgn se (pc s) rt None ->
        compat sgn s rt ->
        compat sgn s' rt ->
        (* exists bu : pbij,
          (exists bu' : pbij,
            border b bu /\ border b' bu' /\  *)rindist sgn (* bu bu' *) u u'.
    Proof.
      unfold pc; intros.
      destruct H4 as [i' [Ti Ti']].
      destruct H5 as [i [Ui Ui']]; DiscrimateEq.
      destruct s as [pp regs].
      destruct s' as [pp' regs'].
      simpl in H1; subst; simpl in *.
      destruct u as [vu].
      destruct u' as [vu'].
      inversion_mine H0;
      inversion_mine H2; inversion_mine H3.
  (**)
      (* elim well_types_imply_exec_return with (1:=H5) (3:=Ti); auto.
      intros. (*  [T1 T2]. *) *)
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs) rt (Normal vu)).
        elim well_types_imply_exec_return with (1:=H5) (3:=Ti); auto.
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs') rt (Normal vu')).
        elim well_types_imply_exec_return with (1:=H4) (3:=Ui); auto.
      apply DEX_BigStepWithTypes.exec_return_normal in H0.
      apply DEX_BigStepWithTypes.exec_return_normal in H1.
      constructor. 
      apply indist2_return with (1:=H0) (2:=H1) (3:=H9). 
    Qed.

(*     Lemma opstack1: forall m sgn se st st' n k s s' (H:P (SM _ _ m sgn)),
      ~ L.leql (se (pc s)) kobs ->
      high_opstack st s ->
      exec m n k s (inl _ s') -> 
      texec m (PM_P _ H) sgn se (pc s) k st (Some st') ->
      compat sgn s st ->
      high_opstack st' s'.
    Proof.
      intros.
      destruct H3  as [i [H3 Hi]].
      destruct s as [pp [[h s]l]].
      destruct s' as [pp' [[h' s']l']].
      simpl in *; constructor.
      inversion_mine H2.
      elim well_types_imply_exec_intra with (1:=H10) (3:=H3) (b1:=FFun.empty Location) (kobs:=kobs); auto.
      intros b2 [T1 T2].
      eapply opstack1_intra; eauto.
      inversion_mine H1; auto.
  (**)
      elim well_types_imply_CalledSign_normal with (1:=H5) (3:=H3); auto.
      intros sgn' Hs'.  
      elim well_types_imply_CallStep_normal with (sgn2:=sgn') (1:=H5) (3:=H3) (b1:=FFun.empty Location) (br:=FFun.empty Location) (kobs:=kobs); auto.
      intros b2' [T1' T2'].
      eapply opstack1_exec_call with (3:=T1'); eauto.
      inversion_mine H1; auto.
    Qed. *)

    Section well_formed_lookupswitch.

      (* Variable hyp : forall m sgn, P (SM _ _ m sgn) -> well_formed_lookupswitch m. *)

      Lemma soap2_basic_intra : forall m sgn se rt ut ut' s s' u u',
(*         (forall k, k<N -> ni k) -> *)
        forall H0:P (SM _ _ m sgn),
          indist sgn rt rt s s' -> 
          pc s = pc s' ->
          exec m s (inl _ u) ->
          exec m s' (inl _ u') -> 
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
          compat sgn s rt ->
          compat sgn s' rt ->
          pc u <> pc u' -> 
(*           high_opstack ut u /\ *)
          forall j:PC, region (cdr m (PM_P _ H0)) (pc s) j -> ~ L.leql (se j) kobs.
      Proof.
        intros.
        destruct H4 as [i' [Ti Ui]].
        destruct H5 as [i [Ti' Ui']]. DiscrimateEq.
        inversion_mine H.
        destruct u as [ppu regs].
        destruct u' as [ppu' regs'].
        inversion_mine H3; inversion_mine H2; simpl in *; subst.
  (**)
        assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,r1) rt (ppu,regs) ut).
             elim well_types_imply_exec_intra with (1:=H10) (3:=Ti); auto.
        assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,r2) rt (ppu',regs') ut').
             elim well_types_imply_exec_intra with (1:=H11) (3:=Ti'); auto.
        apply DEX_BigStepWithTypes.exec_intra_normal in H;
        apply DEX_BigStepWithTypes.exec_intra_normal in H1.
        apply soap2_intra with (4:=H1) (3:=H) (6:= H4); auto.
      Qed.

(*       Lemma soap2_basic_return : forall m sgn se rt ut s s' u u',
(*         (forall k, k<N -> ni k) -> *)
        forall H0:P (SM _ _ m sgn),
          indist sgn rt rt s s' -> 
          pc s = pc s' ->
          exec m s (inl _ u) -> 
          exec m s' (inr _ u') -> 
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
          texec m (PM_P _ H0) sgn se (pc s) rt None ->
          compat sgn s rt ->
          compat sgn s' rt ->
          forall j:PC, region (cdr m (PM_P _ H0)) (pc s) j -> ~ L.leql (se j) kobs.
      Proof.
        intros.
        destruct H4 as [i' [Ti Ui]];
        destruct H5 as [i [Ti' Ui']]; DiscrimateEq.
        inversion_mine H.
        destruct u as [ppu regs].
        destruct u' as [vu'].
        inversion_mine H3; inversion_mine H2; simpl in *; subst.
  (**)
        assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2, r1) rt (ppu, regs) ut).
          elim well_types_imply_exec_intra with (1:=H9) (3:=Ti); auto.
        assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pc2, r2) rt (Normal vu')).
          elim well_types_imply_exec_return with (1:=H10) (3:=Ti'); auto.
        apply soap2_basic_intra with (
        elim indist2_intra_return_exception with (1:=T1) (2:=T1') (3:= H7)(kobs:=kobs) ; auto.
        intros; split; auto.
        inversion_mine H1; constructor; auto.
      Qed. *)


(*       Lemma os_insub_high_opstack : forall st1 s,
        high_st kobs s st1 -> forall st2, sub st1 st2 -> high_st kobs s st2.
      Proof.
        induction 1; intros.
        inversion_mine H; constructor; auto.
        inversion_mine H1; constructor; auto.
        intro; elim H; eapply L.leql_trans; eauto.
        apply leql'_leql; auto.
      Qed.

      Lemma sub_high_opstack : forall st1 st2 s,
        high_opstack st1 s -> sub st1 st2 -> high_opstack st2 s.
      Proof.
        intros.
        inversion_mine H; constructor.
        eapply os_insub_high_opstack; eauto.
      Qed. *)

(*       Lemma os_in_sub_double : forall st1 st2 s1 s2 b1 b2,
        os_in kobs b1 b2 s1 s2 st1 st2 -> forall st,
          sub st1 st -> sub st2 st ->
          os_in kobs b1 b2 s1 s2 st st.
      Proof.
        induction 1; intros.
        constructor 1; eapply os_insub_high_opstack; eauto.
        inversion_mine H2; inversion_mine H3; constructor 2; auto.
        intro; elim H; eapply L.leql_trans; eauto.
        apply leql'_leql; auto.
        intro; elim H; eapply L.leql_trans; eauto.
        apply leql'_leql; auto.
        inversion_mine H1; inversion_mine H2; constructor 3; auto.
      Qed.

      Lemma sub_double : forall sgn st1 st2 st s1 s2 b1 b2,
        indist sgn st1 st2 b1 b2 s1 s2 ->
        sub st1 st -> sub st2 st ->
        indist sgn st st b1 b2 s1 s2.
      Proof.
        intros.
        inversion_mine H; constructor.
        inversion_mine H2; constructor; auto; eapply os_in_sub_double; eauto.
      Qed. *)

      Lemma not_none_some : forall (A:Type) (a:option A) (b:A),
        a <> None -> exists b, a = Some b.
      Proof.
        intros. destruct a. exists a; auto.
          apply False_ind; auto.
      Qed.

      Lemma Regs_in_sub_simple : forall rt rt0 s s0,
        Regs_in kobs s0 s rt0 rt -> forall rt',
          sub rt rt' -> 
          Regs_in kobs s0 s rt0 rt'.
      Proof.
        intros.
        constructor 1; auto.
        inversion H.
        inversion H0; subst.
        rewrite <- H1 in H3; auto. auto.
        intros.
        inversion H; inversion H0; subst.
        assert (exists k'', Some k'' = VarMap.get L.t rt rn).
          rewrite H7 in H1; apply VarMap.in_dom_get_some in H1. 
          assert (exists b, Some b = VarMap.get L.t rt rn). 
            intros; destruct (VarMap.get L.t rt rn). exists t; auto.
            apply False_ind; auto. 
          auto.
        destruct H11 as [k''].
        specialize H8 with (rn:=rn).
        apply H8 with (v:=v) (v':=v') (k:=k) (k':=k'') in H1; auto.
        inversion H1. 
          (* case where both are high *)
          constructor 1; auto.
          apply H10 with (k1:=k'') (k2:=k') in H11; auto.
          apply not_leql_trans with (k1:=k''); auto.
          (* case where both are low *)
          constructor 2; auto.
        rewrite H9; auto.
        inversion H2.
      Qed.

      Lemma sub_simple : forall sgn rt rt' rt0 s s0,
        indist sgn rt0 rt s0 s ->
        sub rt rt' -> (* high_opstack st s -> *)
        indist sgn rt0 rt' s0 s.
      Proof.
        intros.
        inversion_mine H; inversion_mine H1; constructor.
        constructor. eapply Regs_in_sub_simple; eauto.
      Qed.

    End well_formed_lookupswitch.

  End TypableProg.

End hyps.

Require check_cdr.
Module MapKind' := MapOption_Base Map2P(*ClassName*).
  Module MapKind <: MAP with Definition key := Kind := Map_Of_MapBase MapKind'.
  Module CheckCdr := check_cdr.Make MapN(*PC*) (* MapKind *).

  Fixpoint map_from_list (l:list PC) : MapN.t bool :=
    match l with
      | nil => MapN.empty _
      | cons i l => MapN.update _ (map_from_list l) i true
    end.

  Definition upd_reg : 
    PC -> list PC -> MapN.t (MapN.t bool) -> MapN.t (MapN.t bool) :=
    fun i l reg =>
      MapN.update _ reg (i) (map_from_list l).

  Definition empty_reg : MapN.t (MapN.t bool) := MapN.empty _.

  Definition upd_jun : 
    PC -> PC -> MapN.t CheckCdr.PC -> MapN.t CheckCdr.PC :=
    fun i j jun =>     MapN.update _ jun (i) j.

  Definition empty_jun : MapN.t (CheckCdr.PC) := MapN.empty _.


  Section check.
    Variable p : DEX_Program.
(*     Variable subclass_test : ClassName -> ClassName -> bool. *)
    Variable m : DEX_Method.
    Definition for_all_steps : (PC -> option PC -> bool) -> bool :=
      fun test => for_all_steps_m (* p subclass_test *) m (fun pc i => test pc).
    Definition test_all_steps : (PC -> option PC -> bool) -> list (PC*bool) :=
      fun test => test_all_steps_m (* p subclass_test *) m (fun pc i => test pc).

    Lemma for_all_steps_true : forall test,
      for_all_steps test = true ->
      forall (i : PC) (*tau : Kind*) (oj : option PC),
        step p (* subclass_test *) m i (* tau *) oj -> test i (* tau *) oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_steps_m_true (* p subclass_test *) m (fun p i => test p)); eauto.
    Qed.

    Definition for_all_succs : PC -> ((* Kind -> *) option PC -> bool) -> bool :=
      for_all_succs_m (* p subclass_test *) m.

    Lemma for_all_succs_true : forall i test,
      for_all_succs i test = true ->
      forall (* tau *) oj, step p (* subclass_test *) m i (* tau *) oj -> test (* tau *) oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_succs_m_true (* p subclass_test *) m); eauto.
    Qed.

    Definition check_cdr : forall
      (reg : MapN.t (MapN.t bool))
      (jun : MapN.t (CheckCdr.PC)), bool :=
      fun reg jun => CheckCdr.check_soaps for_all_steps for_all_succs reg jun.

    Definition check_cdr' 
      (reg : MapN.t (MapN.t bool))
      (jun : MapN.t (CheckCdr.PC)) :=
      CheckCdr.check_soaps' for_all_steps for_all_succs reg jun.

    Definition check_soap1' 
      (reg : MapN.t (MapN.t bool))
      (jun : MapN.t (CheckCdr.PC)) :=
      CheckCdr.check_soap1' for_all_steps test_all_steps reg jun.

    Definition test_soap2
      (reg : MapN.t (MapN.t bool))
      (jun : MapN.t (CheckCdr.PC)) :=
      CheckCdr.test_soap2 for_all_succs reg jun.

    Lemma check_cdr_prop : forall 
      (reg : MapN.t (MapN.t bool))
      (jun : MapN.t (CheckCdr.PC)),
      check_cdr reg jun = true ->
      { cdr : CDR (step p (* subclass_test *) m) |
        forall i j,
          region cdr i j -> CheckCdr.region reg i j}.
    Proof
    (CheckCdr.check_soap_true (step p (* subclass_test *) m) for_all_steps (*fun _ => nil*)
      for_all_steps_true
      for_all_succs for_all_succs_true).

  End check.


  Section CDR_dummy.

    Variable PC: Set.
    Variable step : PC -> option PC -> Prop.

    Definition dummy_cdr : CDR step.
    refine (make_CDR step (fun _ _ => True) (fun _ _ => False) _ _ _ _); auto.
    intuition.
  Qed.

End CDR_dummy.



Section CheckTypable.

  Variable p : DEX_ExtendedProgram.
  Variable se : DEX_Method -> DEX_sign -> PC -> L.t.
  Variable RT :  DEX_Method -> DEX_sign -> PC -> VarMap.t L.t.
(*   Variable subclass_test : ClassName -> ClassName -> bool. *)
  Variable reg : Method -> MapN.t (MapN.t bool).
  Variable jun : Method -> MapN.t (CheckCdr.PC).
  Variable cdr_checked : forall m,
    PM p m ->  check_cdr (* p subclass_test *) m (reg m) (jun m) = true.

  Definition cdr_local : forall m, 
    PM p m -> CDR (step p (* subclass_test *) m) :=
    fun m H => let (cdr_local,_) := 
      check_cdr_prop p (* subclass_test *) m (reg m) (jun m)
      (cdr_checked m H) in cdr_local.

  Lemma cdr_prop : forall m (h:PM p m),
    forall i j,
      region (cdr_local m h) i j -> CheckCdr.region (reg m) i j.
  Proof.
    intros m h; unfold cdr_local.
    destruct check_cdr_prop.
    auto.
  Qed.

  Definition for_all_region : Method -> PC -> (PC->bool) -> bool :=
    fun m => CheckCdr.for_all_region2 (reg m).

  Lemma for_all_region_correct : forall m i test,
    for_all_region m i test = true ->
    forall j, CheckCdr.region (reg m) i j -> test j = true.
  Proof.
    unfold for_all_region; intros.
    eapply CheckCdr.for_all_region2_true; eauto.
  Qed.

   Definition selift m sgn i (*tau:tag*) k :=
    for_all_region m i (* tau *) (fun j => L.leql_t k (se m sgn j)). 

  Fixpoint check_rt0_rec rt sgn p valid_reg default {struct valid_reg}: bool :=
    match valid_reg with 
    | h :: t => 
        (if In_test h p then
          match VarMap.get _ rt h with
          | None => false
          | Some k => (L.eq_t k (DEX_lvt sgn h))
          end
        else
          match VarMap.get _ rt h with
          | None => false
          | Some k => (L.eq_t k default) 
        end)
        && check_rt0_rec rt sgn p t default
    | nil => true
    end.

   Definition check_rt0 m sgn : bool :=
    match DEX_METHOD.body m with
      | None => false
      | Some bm => let rt := RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm) in
(*                    if eq_set_test (VarMap.dom L.t rt) (DEX_BYTECODEMETHOD.regs bm) then *)
                     eq_set_test (VarMap.dom L.t rt) (DEX_BYTECODEMETHOD.regs bm) &&
                     check_rt0_rec rt sgn (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level)
                  (*  else
                     false *)
    end.

(*   Lemma not_valid_regs_check_rt0_false : forall sgn rt locR l r default_level, 
    ~In r l -> 
    l <> nil ->
    check_rt0_rec (rt) sgn (locR) (l) (default_level) = false. 
  Proof.
    (* apply not_In_In_test in H0. *)
    induction (l); intros.
    apply False_ind; auto.
    apply not_in_cons in H. inversion H.
    apply IHl0 with (default_level:=default_level0) in H2; auto.
    unfold check_rt0_rec.
    apply 
    unfold check_rt0_rec.   *)
    
(*   Lemma check_rt0_dom : forall m sgn bm default_level, check_rt0 m sgn = true ->
    DEX_METHOD.body m = Some bm ->
    eq_set (VarMap.dom L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm))) 
      (VarMap.dom L.t (make_rt_from_lvt_rec sgn (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) default_level)).
  Proof.
    unfold check_rt0. 
    intros. rewrite H0 in H. unfold check_rt0_rec in H.
    induction (DEX_BYTECODEMETHOD.regs bm). 
    constructor; auto. *)

  Lemma check_rt0_rec_true : forall m sgn bm default_level,
    check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn 
      (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) default_level = true ->
    DEX_METHOD.body m = Some bm -> 
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)).
  Proof.
    intros. (* right. *)
    split; intros.
    (* case where the register is in the domain *)
      induction (DEX_BYTECODEMETHOD.regs bm). inversion H1.
      unfold check_rt0_rec in H. 
      assert ((if In_test a (DEX_BYTECODEMETHOD.locR bm) then
      match VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k (DEX_lvt sgn a) 
      | None => false
      end
     else
      match VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k default_level0 
      | None => false
      end) &&
      check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn (DEX_BYTECODEMETHOD.locR bm) l default_level0
        = true). auto. clear H.
      inversion H1.
      subst.
      apply In_In_test in H2; rewrite H2 in H4.
      rewrite <- H3 in H4. flatten_bool.
      generalize (L.eq_t_spec k (DEX_lvt sgn r)); intros Heq; rewrite H in Heq; auto.
      destruct (In_test a (DEX_BYTECODEMETHOD.locR bm)).
      destruct (VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a). 
      flatten_bool. apply IHl; subst; auto.
      inversion H4. 
      destruct (VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a). 
      flatten_bool; apply IHl; subst; auto.
      inversion H4. 
    (* case where the register is not in the domain *)
    induction (DEX_BYTECODEMETHOD.regs bm). inversion H1.
    assert ((if In_test a (DEX_BYTECODEMETHOD.locR bm)
     then
      match VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k (DEX_lvt sgn a) 
      | None => false
      end
     else
      match VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k default_level0
      | None => false
      end) &&
      check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn (DEX_BYTECODEMETHOD.locR bm) l default_level0 = true). auto.
    clear H.
    inversion H1.
    apply not_In_In_test in H2.
    rewrite <- H in H2; rewrite H2 in H3. subst.
    destruct (VarMap.get L.t (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r).
    flatten_bool; auto.
    generalize (L.eq_t_spec t default_level0); intros Heq; rewrite H in Heq; rewrite Heq; auto.
    inversion H3.
    (* induction case *)
    flatten_bool. apply IHl; subst; auto.
  Qed.

  Lemma check_rt0_true : forall m sgn bm, check_rt0 m sgn = true ->
    DEX_METHOD.body m = Some bm ->
    (* DEX_BYTECODEMETHOD.regs bm = nil \/  *)
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)).
  Proof.
    intros. unfold check_rt0 in H.
    rewrite H0 in H. flatten_bool. apply check_rt0_rec_true; auto.  
  Qed.

  Definition check : bool := for_all_P p
    (fun m sgn =>
      (check_rt0 m sgn) &&
      for_all_steps_m (*p subclass_test *) m
      (fun i ins oj => 
        DEX_tcheck (*p subclass_test*) m sgn (se m sgn) (selift m sgn) (RT m sgn) i ins)
    ).

  Lemma PC_eq_dec' : forall x y : PC, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

  (* Lemma make_rt_lvt_prop : forall m sgn bm, check_rt0 m sgn = true ->
    DEX_METHOD.body m = Some bm ->
    (* DEX_BYTECODEMETHOD.regs bm = nil \/  *)
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)). *)

   Parameter valid_regs_prop : forall m bm r rt, DEX_METHOD.body m = Some bm -> 
    ~ In r (DEX_BYTECODEMETHOD.regs bm) -> VarMap.get L.t rt r = None. 

  Lemma check_correct1_aux : forall m bm sgn, DEX_METHOD.body m = Some bm -> check_rt0 m sgn = true ->
    eq_rt (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) 
      (make_rt_from_lvt_rec sgn (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) default_level).
  Proof.
    constructor.
      unfold check_rt0 in H0; rewrite H in H0.
      flatten_bool.
      apply eq_set_test_prop in H1; auto.
      generalize make_rt_from_lvt_prop3; intros.
      specialize H0 with (s:=sgn) (p:=DEX_BYTECODEMETHOD.locR bm) (v:=DEX_BYTECODEMETHOD.regs bm) (d:=default_level)
        (1:=DEX_BYTECODEMETHOD.noDup_regs bm).
      rewrite H1. rewrite H0. reflexivity.
    intros.
    destruct (in_dec PC_eq_dec' r (DEX_BYTECODEMETHOD.regs bm)).
    apply check_rt0_true with (bm:=bm) (r:=r) in H0; auto.
    inversion_mine H0. 
      (* rewrite H5 in i; inversion i. 
     apply H5 in i; auto.  *)
    destruct (in_dec PC_eq_dec' r (DEX_BYTECODEMETHOD.locR bm)).
    assert (i0':=i0).
    apply H5 with (k:=k1) in i0; auto. 
    apply make_rt_from_lvt_prop1 with (k:=k2) (s:=sgn) (v:=DEX_BYTECODEMETHOD.regs bm) (p:=DEX_BYTECODEMETHOD.locR bm) (d:=default_level) in i0'; congruence.
    assert (n':=n).
    apply H6 in n; auto. rewrite <- n in H3; inversion H3; subst.
    apply make_rt_from_lvt_prop2 with (s:=sgn) (v:=DEX_BYTECODEMETHOD.regs bm) (p:=DEX_BYTECODEMETHOD.locR bm) (d:=default_level) in n'; auto.
    rewrite <- n' in H4; auto. congruence.
    apply valid_regs_prop with (m:=m) (rt:=RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) in n; auto.
    rewrite n in H3; inversion H3.
  Qed.

  Lemma check_correct1 : check = true ->
    forall m sgn, P p (SM _ _ m sgn) ->
      forall i rt, init_pc m i -> rt0 p m sgn rt -> eq_rt (RT m sgn i) (rt).
  Proof.
    unfold check; intros.
    inversion_mine H1.
    inversion H2.
      rewrite H3 in H1; inversion H1; subst. (* symmetry in H1. rewrite <- H7 in H5; clear H7.   *)
    assert (T:=for_all_P_true _ _ H _ _ H0).
    destruct (andb_prop _ _ T) as [TT _].
    apply check_correct1_aux with (m:=m) (bm:=bm0) (sgn:=sgn); auto.
  Qed. 

  Lemma check_correct2 : check = true ->
    forall m sgn (h:P p (SM _ _ m sgn)),
      forall i,
        step p (* subclass_test *) m i None ->
        texec p (*subclass_test *) cdr_local m (PM_P _ _ h) sgn (se m sgn) i (RT m sgn i) None.
  Proof.
    unfold check; intros.
    assert (T:=for_all_P_true _ _ H _ _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    exists ins; split; [idtac|assumption].
    assert (T':=for_all_steps_m_true _ _ TT _ _ _ H2 H3).
    apply tcheck_correct1 with (selift:=selift m sgn) (m:=m); auto.
    (* unfold selift; intros.
    generalize (for_all_region_correct _ _ _ _ H1 _ (cdr_prop _ _ _ _ _ H4)).
    intros C; generalize (L.leql_t_spec k (se m sgn j)); rewrite C; auto. *)
  Qed.

  Lemma tsub_sub : forall rt1 rt2,
    tsub_rt rt1 rt2 = true -> sub rt1 rt2.
  Proof.
    (* induction st1; destruct st2; simpl; *) intros. (* ; try discriminate. *)
    unfold tsub_rt in H. destruct (andb_prop _ _ H).
    apply eq_set_test_prop in H0. 
    constructor; auto.
    intros.
    apply tsub_rec_leq with (r:=r) (k1:=k1) (k2:=k2) in H1; auto.
    assert (VarMap.get L.t rt2 r <> None). unfold not; intros. 
      rewrite H4 in H3; inversion H3.
    apply VarMap.get_some_in_dom in H4; auto.
  Qed.

  Lemma check_correct3 : check = true ->
    forall m sgn (h:P p (SM _ _ m sgn)),
      forall i j,
        step p (* subclass_test *) m i (Some j) ->
        exists rt,
          texec p (* subclass_test *) cdr_local m (PM_P _ _ h) sgn (se m sgn) i (RT m sgn i) (Some rt) 
          /\ sub rt (RT m sgn j).
  Proof.
    unfold check; intros.
    assert (T:=for_all_P_true _ _ H _ _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    assert (T':=for_all_steps_m_true _ _ TT _ _ _ H2 H3).
    elim (tcheck_correct2 (* p subclass_test *) m sgn (region (cdr_local _ (PM_P _ _ h)))  (se m sgn)
      (selift m sgn) (RT m sgn)) with (2:=T') (3:=H3).
    intros rt [T1 T2].
    exists rt; split.
    exists ins; split; auto.
    apply tsub_sub; auto.
    unfold selift; intros.
    assert (T2:=for_all_region_correct _ _ _ H1 _ (cdr_prop _ _ _ _ H4)).
    generalize (L.leql_t_spec k (se m sgn j0)).
    rewrite T2; auto.
  Qed.

  Lemma check_correct : 
    check = true ->
    TypableProg p (* subclass_test *) cdr_local se RT.
  Proof.
    intros H m sgn H1.
    constructor.
    apply check_correct1; auto.
    split.
    apply check_correct2; auto.
    apply check_correct3; auto.
  Qed.

End CheckTypable.

Check check.

Section well_formed_lookupswitch.

  Fixpoint check_not_in_snd (i:Z) (o:DEX_OFFSET.t) (l:list (Z*DEX_OFFSET.t)) {struct l} : bool :=
    match l with
      | nil => true
      | (j,o')::l => 
        if Zeq_bool i j 
          then (Zeq_bool o o') && check_not_in_snd i o l
          else check_not_in_snd i o l
    end.
  
  Lemma check_not_in_snd_correct : forall i o l,
    check_not_in_snd i o l = true ->
    forall o', In (i,o') l -> o=o'.
  Proof.
    induction l; simpl; intuition.
    subst.
    generalize (Zeq_spec i i); destruct (Zeq_bool i i).
    elim andb_prop with (1:=H); intros.
    generalize (Zeq_spec o o'); rewrite H0; auto.
    intuition.
    apply IHl; auto.
    destruct a.
    destruct (Zeq_bool i z); auto.
    elim andb_prop with (1:=H); auto.
  Qed.

  Fixpoint check_functionnal_list (l:list (Z*DEX_OFFSET.t)) : bool :=
    match l with
      | nil => true
      | (i,o)::l => (check_not_in_snd i o l) && check_functionnal_list l
    end.

  Lemma check_functionnal_list_correct : forall l,
    check_functionnal_list l = true ->
    forall i o1 o2,
      In (i, o1) l -> In (i, o2) l -> o1=o2.
  Proof.
    induction l; simpl; intuition.
    congruence.
    subst.
    elim andb_prop with (1:=H); clear H; intros.
    eapply check_not_in_snd_correct; eauto.
    subst.
    elim andb_prop with (1:=H); clear H; intros.
    apply sym_eq; eapply check_not_in_snd_correct; eauto.
    destruct a.
    elim andb_prop with (1:=H); clear H; intros.
    eauto.
  Qed.

End  well_formed_lookupswitch.

Lemma evalsto_path : forall m sgn n s i res,
    region (cdr m (PM_P _ H)) s (fst i) ->
    evalsto m n i res ->
    (exists j, junc (cdr m (PM_P _ H)) s (fst j) /\ path m (fst i) (fst j) /\ 
    (exists n', evalsto m n' j res /\ n' < n)) \/
    (forall jun, ~junc (cdr m (PM_P _ H)) s jun).
  Proof.
    intros m sgn n. pattern n. apply lt_wf_ind.
    clear n. intros n IH.
    intros s i res H Hreg Hevalsto.
    inversion Hevalsto.
    (* the case where i is immediately a return point *)
    apply exec_step_none with (1:=PM_P _ H) in H0.
    right. intros. apply soap3 with (j:=pc i); auto.
    (* inductive case *)
    elim soap2 with PC (step m) (cdr m (PM_P _ H)) s (pc i) (pc s2); intros; auto.
    (* path stays in region *)
    elim IH with (H:=H) (s:=s) (m0:=n0) (i:=s2) (res:=res); simpl; intros; auto.
    Cleanexand.
    left.
    exists x. repeat (split; auto).
    constructor 2 with (k:=pc s2); auto.
    apply exec_step_some with (1:=PM_P _ H); auto.
    exists x0. split; auto.
    omega.
    (* path is the junction *) 
    left. exists s2. repeat (split; auto). 
    constructor 2 with (k:=pc s2); auto. constructor; auto.
    apply exec_step_some with (1:=PM_P _ H); auto.
    exists n0; repeat (split; auto).
    apply exec_step_some with (1:=PM_P _ H); auto.
  Qed.

(* Theorem ni_safe : forall (kobs:L.t) (p:DEX_ExtendedProgram) (*subclass_test : ClassName -> ClassName -> bool*),
  (*(forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2) ->*)
  forall cdr : forall m, PM p m -> CDR (step p (* subclass_test *) m),
    (exists se, exists RT, TypableProg p (* subclass_test *) cdr se RT) ->
(*     (forall m sgn, P p (SM _ _ m sgn) -> well_formed_lookupswitch m) -> *)
    forall m sgn i r1 r2,
      P p (SM _ _ m sgn) ->
      init_pc m i -> 
      compat sgn (i,nil) nil ->
      compat sgn (i,nil) nil ->
      evalsto p m (i,nil) (r1) -> 
      evalsto p m (i,nil) (r2) -> 
        indist_return_value kobs sgn r1 r2.
Proof.
  intros kobs p sub_test Hst cdr [se [S HT]] Hwf m sgn i h1 h2 l1 l2 hr1 hr2 r1 r2 n1 n2 b1 b2 H H0 H1 H2 H3 H4 H5 H6.
  assert (Hni:=safe_ni _ _ _ _ _ _ cdr _ _ _ (exec p) pc
    (tcc0 p _ Hst) (tcc1 p _ Hst) _ pbij (texec p sub_test cdr)
    (indist kobs p) (irindist kobs p) (rindist kobs p)
    (tcc2 kobs p) (tcc3 kobs p) (tcc4 kobs p) (tcc5 kobs p)
    (compat p) (compat_res p) s0 init_pc (high_opstack kobs) (P p) (PM_P p)
    (tcc6 kobs p sub_test cdr) (tcc7 kobs p sub_test cdr)
    border tcc8
    (indist2_intra kobs p _ Hst cdr _ _ HT)
    (indist2_return kobs p _ Hst cdr _ _ HT) 
    (indist2_intra_return kobs p _ Hst cdr _ _ HT)
    (indist1_intra kobs p _ Hst cdr _ _ HT)
    (indist1_intra_return kobs p _ Hst cdr _ _ HT)
    (indist1_return_intra kobs p _ Hst cdr _ _ HT) 
    (indist1_return kobs p _ Hst cdr _ _ HT)
    (opstack1 kobs p _ cdr)
    (soap2_basic_intra kobs p sub_test cdr Hwf) 
    (soap2_basic_return kobs p sub_test cdr)
    _ (sub_high_opstack kobs) (sub_double kobs p) (sub_simple kobs p) (indist_high_opstack kobs p) 
    (sub_irindist kobs p) (compat_sub p) _ _ HT).
  elim evalsto_Tevalsto with (1:=H3); intros p1 He1.
  elim evalsto_Tevalsto with (1:=H4); intros p2 He2.
  elim Hni with (8:=He1) (9:=He2) (sgn:=sgn) (b:=b1) (b':=b2); auto.
  intros br1 [br2 [T1 [T2 T3]]].
  inversion_clear T3; exists br1; exists br2; Splitand; try assumption.
  do 2 constructor; try assumption.
  repeat constructor.
Qed. *)

Definition check_all_cdr 
  (p:DEX_Program) (*subclass_test : ClassName -> ClassName -> bool*)
  (reg : Method -> MapN.t (MapN.t bool))
  (jun : Method -> MapN.t (CheckCdr.PC)) : bool :=
  for_all_methods p (fun m => check_cdr (* p subclass_test *) m (reg m) (jun m)).

Lemma check_all_cdr_correct : forall p (* subclass_test *) reg jun,
  check_all_cdr p (* subclass_test *) reg jun = true ->
  forall m, PM p m -> check_cdr (* p subclass_test *) m (reg m) (jun m) = true.
Proof.
  unfold check_all_cdr; intros.
  apply (for_all_methods_true p (fun m => check_cdr (*p subclass_test0 *) m (reg m) (jun m))); auto.
Qed.

Lemma IntraStep_evalsto_aux : forall p m s r,
  DEX_BigStepAnnot.DEX_IntraStepStar (* P.throwableAt (throwableBy p.(prog)) *) p.(DEX_prog) m s r ->
  match r with
    | inl _ => True
    | inr r => evalsto p m s r
  end.
Proof.
  intros p; apply DEX_BigStepAnnot.DEX_IntraStepStar_ind; intros; auto.
  constructor 1.
  constructor 2; auto.
  destruct r; auto.
  constructor 2 with (s2:=s'); auto.
  constructor; auto.
Qed.

Lemma BigStep_evalsto : forall p m s r,
  DEX_BigStepAnnot.DEX_BigStep (* P.throwableAt (throwableBy p.(prog)) *) p.(DEX_prog) m s r ->
  evalsto p m s r.
Proof.
  intros.
  apply IntraStep_evalsto_aux with (1:=H).
Qed.
(* 
Theorem correctness : forall
  (p:ExtendedProgram)
  (subclass_test : ClassName -> ClassName -> bool),
  (forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2) ->
  check_well_formed_lookupswitch p =true ->
  forall 
    (kobs:L.t)
    (reg : Method -> CheckCdr.M.t (MapN.t bool))
    (jun : Method -> MapN.t (MapKind.t CheckCdr.PC)),
    check_all_cdr p subclass_test reg jun = true ->
    forall 
      (se : Method -> sign -> PC -> L.t) 
      (S :  Method -> sign -> PC -> list L.t'),
      check p se S subclass_test reg = true ->
      forall m sgn i h1 h2 l1 l2 hr1 hr2 r1 r2 n1 n2 b1 b2,
        P p (SM _ _ m sgn) ->
        init_pc m i -> 
        compat p sgn (i,(h1,nil,l1)) nil ->
        compat p sgn (i,(h2,nil,l2)) nil ->
        evalsto p m n1 (i,(h1,nil,l1)) (hr1,r1) -> 
        evalsto p m n2 (i,(h2,nil,l2)) (hr2,r2) -> 
        localvar_in kobs sgn.(lvt) b1 b2 l1 l2 ->
          indist_return_value kobs sgn r1 r2.
Proof.
  intros p stest Hsubclass Hwf kobs reg jun Hcheck se S.
  intros Hc.
  intros m sgn i h1 h2 l1 l2 hr1 hr2 r1 r2 n1 n2 b1 b2 H H0 H1 H2 H3 H4 H5 H6.
  assert (T:=check_all_cdr_correct _ _ _ _ Hcheck).
  assert (TT:=check_correct _ _ _ _ _ _ T Hc).
  eapply ni_safe with (8:=H3) (9:=H4); eauto.
  apply (check_well_formed_lookupswitch_correct p); auto.
Qed. *)



Definition m_reg_empty := DEX_MapShortMethSign.empty (MapN.t (MapN.t bool)).

Definition m_reg_add (m:Method) (reg:(MapN.t (MapN.t bool))) map :=
  DEX_MapShortMethSign.update _ map m.(DEX_METHOD.signature) reg.

Definition m_reg_get map : Method -> MapN.t (MapN.t bool) :=
  fun m =>   
    match DEX_MapShortMethSign.get _ map m.(DEX_METHOD.signature) with
      | None => empty_reg
      | Some r => r
    end.

Definition m_jun_empty := DEX_MapShortMethSign.empty (MapN.t (CheckCdr.PC)).

Definition m_jun_add (m:Method) (jun:(MapN.t (CheckCdr.PC))) map :=
  DEX_MapShortMethSign.update _ map m.(DEX_METHOD.signature) jun.

Definition m_jun_get map : DEX_Method -> MapN.t (CheckCdr.PC) :=
  fun m =>   
    match DEX_MapShortMethSign.get _ map m.(DEX_METHOD.signature) with
      | None => empty_jun
      | Some r => r
    end.

Definition se_empty := MapN.empty L.t.
Definition se_add (i:PC) (l:L.t) se := MapN.update _ se i l.

Definition m_se_empty := DEX_MapShortMethSign.empty (MapN.t L.t).
Definition m_se_add (m:Method) (se:MapN.t L.t) m_se :=
  DEX_MapShortMethSign.update _ m_se m.(DEX_METHOD.signature) se.
Definition se_get se : PC -> L.t := fun i =>
  match MapN.get _ se i with
    | None => L.bot
    | Some l => l
  end.
Definition m_se_get map : Method -> DEX_sign -> PC -> L.t :=
  fun m sgn => match DEX_MapShortMethSign.get _ map m.(DEX_METHOD.signature) with
                 | None => fun _ => L.bot
                 | Some m => fun i => se_get m i
               end.

Definition RT_empty := MapN.empty (VarMap.t L.t).
Definition RT_add (i:PC) (rt:VarMap.t L.t) RT := MapN.update _ RT i rt.

Definition m_RT_empty := DEX_MapShortMethSign.empty (MapN.t (VarMap.t L.t)).
Definition m_RT_add (m:Method) (RT:MapN.t (VarMap.t L.t)) m_RT :=
  DEX_MapShortMethSign.update _ m_RT m.(DEX_METHOD.signature) RT.
Definition RT_get RT : PC -> (VarMap.t L.t) := fun i =>
  match MapN.get _ RT i with
    | None => VarMap.empty L.t
    | Some rt => rt
  end.
Definition m_RT_get map : Method -> DEX_sign -> PC -> (VarMap.t L.t) :=
  fun m sgn => match DEX_MapShortMethSign.get _ map m.(DEX_METHOD.signature) with
                 | None => fun _ => VarMap.empty L.t
                 | Some m => RT_get m
               end.

Definition ms_eq : DEX_ShortMethodSignature -> DEX_ShortMethodSignature -> bool := DEX_METHODSIGNATURE.eq_t.

Definition selift_m reg se i k :=
  CheckCdr.for_all_region2 reg i (fun j => L.leql_t k (se_get se j)).

Definition check_m (p:DEX_ExtendedProgram) m sgn reg se RT i : bool :=
  match subclass_test p with
    | None => false
    | Some subclass_test =>
      match instructionAt m i with
        | None => false
        | Some ins =>
          DEX_tcheck m sgn (se_get se) (selift_m reg se) (RT_get RT) i ins
      end
  end.

Definition check_ni (p:DEX_ExtendedProgram) reg jun se RT : bool :=
  match subclass_test p.(DEX_prog) with
    | None => false
    | Some subclass =>
      (* check_well_formed_lookupswitch p && *)
      check_all_cdr p reg jun &&
      check p se RT reg
  end.

Definition NI (p:DEX_ExtendedProgram) : Prop :=
  forall kobs m sgn i r1 r2,
    P p (SM _ _ m sgn) ->
    init_pc m i -> 
    BigStepAnnot.BigStep p.(DEX_prog) m (i,(h1,nil,l1)) (r1) -> 
    BigStepAnnot.BigStep p.(DEX_prog) m (i,(h2,nil,l2)) (r2) -> 
      indist_return_value kobs sgn r1 r2.

Theorem check_ni_correct : forall p reg jun se S,
  check_ni p reg jun se S = true ->
  NI p.
Proof.
  unfold check_ni, NI; intros.
  generalize (subclass_test_prop p.(prog)).
  destruct (subclass_test p.(prog)).
  destruct (andb_prop _ _ H).
  destruct (andb_prop _ _ H10).
  intros T; generalize (T _ (refl_equal _)); intros.
  destruct (BigStep_evalsto _ _ _ _ H6) as [n1 T6].
  destruct (BigStep_evalsto _ _ _ _ H7) as [n2 T7].
  eapply correctness with (9:=T6) (10:=T7); eauto.
  constructor; auto.
  split; auto; constructor.
  constructor; auto.
  split; auto; constructor.
  discriminate.
Qed.



