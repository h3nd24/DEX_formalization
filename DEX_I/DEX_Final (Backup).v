Require Export DEX_Framework.
Require Export DEX_ProofBigStepWithType.
Require Export DEX_ElemLemmas.
Require Export DEX_ElemLemmaIntra.
Require Export DEX_ElemLemmaReturn.
Require Export DEX_step.
Require Export DEX_typing_rules.

Import DEX_BigStepWithTypes DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Ltac assert_some_not_none rt rn H := 
    assert (VarMap.get L.t rt rn <> None) by solve [
    destruct (VarMap.get L.t rt rn) as [a | ]; 
      try (intros Hf; inversion Hf);
      try (inversion H)].

Ltac assert_not_none_some rt rn k t:= 
   assert (exists k, Some k = VarMap.get L.t rt rn) by solve [
    destruct (VarMap.get L.t rt rn) as [t | ] eqn:Hget; 
      try (exists t; auto); 
      try (apply False_ind; auto)].

Definition ValidMethod (p:DEX_Program) (m:DEX_Method) : Prop :=
  exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

Definition step (p:DEX_Program) : DEX_Method -> DEX_PC -> option DEX_PC -> Prop := 
fun m pc (* tau *) opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ DEX_step m pc i opc.

Variable RT_domain_same : forall rt1 rt2 r, In r (VarMap.dom L.t rt1) -> In r (VarMap.dom L.t rt2).
Variable valid_regs_prop : forall m bm r rt, DEX_METHOD.body m = Some bm -> 
    ~ In r (DEX_BYTECODEMETHOD.regs bm) -> VarMap.get L.t rt r = None.
Variable RT_domain_length_same : forall rt1 rt2, length (VarMap.dom L.t rt1) = length (VarMap.dom L.t rt2). 

Section hyps.
  Variable kobs: L.t.
  Variable p : DEX_ExtendedProgram.
  Definition Reg := DEX_Reg.
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

  Notation step := (step p).
  Variable cdr : forall m, PM p m -> CDR (step m).

  Definition istate : Type := DEX_IntraNormalState.
  Definition rstate : Type := DEX_ReturnState.
  Inductive exec : Method -> istate -> istate + rstate -> Prop :=
  | exec_intra : forall (m:Method) s1 s2,
    DEX_BigStepAnnot.DEX_exec_intra p m s1 s2 -> 
    exec m s1 (inl _ s2)
  | exec_return : forall (m:Method) s ret,
    DEX_BigStepAnnot.DEX_exec_return p m s ret ->
    exec m s (inr _ ret).

  Inductive evalsto : Method -> istate -> rstate -> Prop :=
  | evalsto_return : forall (m:Method) s r,
    exec m s (inr _ r) ->
    evalsto m s r
  | evalsto_intra : forall (m:Method) s1 s2 r,
    exec m s1 (inl _ s2) ->
    evalsto m s2 r ->
    evalsto m s1 r. 

  Definition pc : istate -> PC := @fst _ _.

  Definition registertypes : Type := TypeRegisters.

  Definition texec : forall m, PM p m -> Sign -> (PC -> L.t) ->
    PC -> registertypes -> option registertypes -> Prop :=
    fun m H sgn se pc rt ort =>
      exists i, texec sgn (region (cdr m H)) se pc i rt ort
        /\ instructionAt m pc = Some i.

  Inductive indist : Sign -> registertypes ->
    registertypes -> istate -> istate -> Prop :=
    indist_def :forall sgn rt1 rt2 r1 r2 pc1 pc2,
      st_in kobs rt1 rt2 (pc1,r1) (pc2,r2) ->
      indist sgn rt1 rt2 (pc1,r1) (pc2,r2).

  Inductive rindist : Sign -> rstate -> rstate -> Prop :=
  | rindist_def : forall sgn r1 r2,
    indist_return_value kobs sgn r1 r2 -> rindist sgn r1 r2.

  Definition default_level := L.High.

  Inductive init_pc (m:Method) : PC -> Prop :=
    init_pc_def : forall bm,
      DEX_METHOD.body m = Some bm ->
      init_pc m (DEX_BYTECODEMETHOD.firstAddress bm).

  Definition rt0 (m:Method) (sgn:Sign): registertypes := 
  match DEX_METHOD.body m with
  | Some bm => (Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level))
  | None => VarMap.empty L.t
  end.

  Definition ni := ni _ _ _ _ _ exec pc registertypes indist rindist rt0 init_pc P.

  Open Scope nat_scope.

  Lemma evalsto_Tevalsto : forall m s r,
    evalsto m s r ->
    exists p, DEX_Framework.evalsto Method istate rstate exec m p s r.
  Proof.
    intros.
    induction H.
    exists 1; constructor 1; auto.
    inversion IHevalsto.
    exists (S x). constructor 2 with (s2:=s2); auto.
  Qed.

  Lemma evalsto_Tevalsto2 : forall m s r p,
    DEX_Framework.evalsto Method istate rstate exec m p s r ->
    evalsto m s r.
  Proof.
    intros.
    induction H.
    constructor 1; auto.
    constructor 2 with (s2:=s2); auto.
  Qed.

  Lemma in_snd : forall (A B:Type) (a:A) (b:B) l, In (a, b) l -> In b (map snd l).
  Proof.
    induction l; intros.
      inversion H.
      inversion H. left. rewrite H0; auto.
      right; apply IHl; auto.
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
      try (match goal with
        | [ id : instructionAt _ _ = Some ?i |- _] =>
          exists i; simpl; split; [assumption|idtac]; constructor; 
            simpl; auto; fail
      end).
      exists (DEX_PackedSwitch r firstKey size list_offset); simpl; split; auto.
      constructor 16. apply nth_error_In with (n:=n); auto.
      exists (DEX_SparseSwitch r size listkey); simpl; split; auto.
      constructor 18. apply in_snd with (a:=v'); auto.
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
      specialize H2 with rn.
      inversion H2. 
      assert_some_not_none x rn H0.
      assert_some_not_none x0 rn H6.
      apply VarMap.get_some_in_dom in H9.
      apply VarMap.get_some_in_dom in H10.      
      constructor 1 with (k:=k) (k':=k'); auto.
      rewrite eq_rt_get with (rt1:=y0) (rt2:=x); auto. apply eq_rt_sym; auto.
      rewrite <- H3; auto.
      rewrite eq_rt_get with (rt1:=y1) (rt2:=x0); auto. apply eq_rt_sym; auto.
      rewrite H in H10; auto.
      constructor 2. auto.
    (* <- *)
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
      specialize H2 with rn.
      inversion H2. 
      assert_some_not_none y0 rn H0.
      assert_some_not_none y1 rn H6.
      apply VarMap.get_some_in_dom in H9.
      apply VarMap.get_some_in_dom in H10.      
      constructor 1 with (k:=k) (k':=k'); auto.
      rewrite eq_rt_get with (rt1:=x) (rt2:=y0); auto. rewrite H3; auto.
      rewrite eq_rt_get with (rt1:=x0) (rt2:=y1); auto. rewrite H; auto. 
      constructor 2. auto.
  Qed.

  Definition TypableProg := TypableProg PC Method step (PM p) Sign (* istate pc *) registertypes 
    texec rt0 init_pc P PM_P sub eq_rt.

  Section TypableProg.

    Variable se : Method -> Sign -> PC -> L.t.
    Variable RT : Method -> Sign -> PC -> registertypes.
    Variable typable_hyp : TypableProg se RT.

    Definition high_reg (rt:registertypes) (r:Reg) : Prop :=
      match VarMap.get _ rt r with
      | None => False
      | Some k => ~L.leql k kobs
      end.

    Variable not_high_reg : forall rt r, ~high_reg rt r -> (exists k, VarMap.get L.t rt r = Some k /\ L.leql k kobs).

    Definition indist_reg_val (s1 s2: istate) (r: Reg) : Prop :=
      let rho1 := snd s1 in
      let rho2 := snd s2 in
        match DEX_Registers.get rho1 r, DEX_Registers.get rho2 r with
        | Some v1, Some v2 => v1 = v2
        | None, None => True
        | _, _ => False
        end.

    Lemma indist_reg_val_trans : forall s1 s2 s3 r, 
      indist_reg_val s1 s2 r -> indist_reg_val s2 s3 r -> indist_reg_val s1 s3 r.
    Proof.
      intros.
      unfold indist_reg_val in *.
      destruct (DEX_Registers.get (snd s1) r);
      destruct (DEX_Registers.get (snd s2) r);
      destruct (DEX_Registers.get (snd s3) r); auto.
      rewrite H; auto. inversion H.
    Qed.

    Lemma indist_reg_val_sym : forall s1 s2 r, 
      indist_reg_val s1 s2 r -> indist_reg_val s2 s1 r.
    Proof.
      unfold indist_reg_val in *.
      intros.
      destruct (DEX_Registers.get (snd s1) r);
      destruct (DEX_Registers.get (snd s2) r); auto.
    Qed.

    Definition indist_reg := DEX_Framework.indist_reg Reg istate registertypes high_reg indist_reg_val.

    Lemma indist_from_reg : forall sgn rt1 rt2 s1 s2, 
      (forall r, indist_reg rt1 rt2 s1 s2 r) -> indist sgn rt1 rt2 s1 s2.
    Proof.
      intros.
      destruct s1; destruct s2.
      constructor.
      constructor.
      constructor.
      constructor.
        apply RT_domain_length_same.
        split; eapply RT_domain_same; eauto.
      intros.
      specialize H with rn. 
      inversion H.
      unfold high_reg in *. 
      destruct (VarMap.get L.t rt1 rn) eqn:Hget1; destruct (VarMap.get L.t rt2 rn) eqn:Hget2; try (contradiction).
      constructor 1 with (k:=t1) (k':=t2); auto. 
      constructor 2. subst. unfold indist_reg_val in H0.
      simpl in H0. destruct (DEX_Registers.get t rn); destruct (DEX_Registers.get t0 rn); subst; try contradiction.
      destruct d2; repeat constructor.
      constructor.
    Qed.

    Lemma indist_reg_from_indist : forall sgn rt1 rt2 s1 s2,
      indist sgn rt1 rt2 s1 s2 -> 
      forall r, 
        (high_reg rt1 r -> high_reg rt2 r -> indist_reg rt1 rt2 s1 s2 r) /\ 
        ((~high_reg rt1 r /\ ~high_reg rt2 r) \/
          (high_reg rt1 r /\ ~high_reg rt2 r) \/
          (~high_reg rt1 r /\ high_reg rt2 r) ->
        indist_reg_val s1 s2 r).
    Proof.
      intros sgn rt1 rt2 s1 s2 Hindist r.
      inversion Hindist. inversion H. inversion H6. subst. 
      specialize H11 with (rn:=r).
      inversion H11.
      split; intros.
      constructor; auto.
      inversion H4. inversion H5.
      unfold high_reg in H7, H8.
      rewrite H0 in H7; rewrite H1 in H8. contradiction.
      inversion H5. inversion H7. 
      unfold high_reg in H8, H9.
      rewrite H0 in H8; rewrite H1 in H9. contradiction.
      inversion H7.
      unfold high_reg in H8, H9.
      rewrite H0 in H8; rewrite H1 in H9. contradiction.
      split; intros. constructor; auto.
      unfold indist_reg_val. simpl.
      destruct (DEX_Registers.get r1 r); destruct (DEX_Registers.get r2 r); subst; auto.
      inversion H0. inversion H4. auto.
      inversion H0. inversion H0.
    Qed.

    Definition high_result := high_result kobs.

    Lemma tevalsto_high_result : forall m sgn (H:PM p m) se s RT res,
      ~L.leql (se m sgn (pc s)) kobs ->
      exec m s (inr res) ->
      texec m H sgn (se m sgn) (pc s) (RT m sgn (pc s)) None -> high_result sgn res.
    Proof.
      intros.
      inversion_mine H2. 
      inversion_mine H1. Cleanexand.
      inversion_mine H6. inversion_mine H3. 
      inversion_mine H1. constructor 1. auto. 
      simpl in H2. rewrite H2 in H5. inversion H5.
      inversion_mine H1. simpl in H2. rewrite H2 in H5. inversion H5. 
      constructor 2 with (k:=kv); auto.
      simpl in H0, H11.
      apply leql_join_each in H11. Cleanexand.
      apply not_leql_trans with (k1:=se0 m sgn pc0); auto.
    Qed.

    (* this is only applicable to exception instructions, so normal instructions 
      only need to be proved via contradiction *)
    Lemma tevalsto_diff_high_result : forall m sgn se RT s s' s1' rt res res' (H:PM p m),
      pc s = pc s' ->
      exec m s (inr res) ->
      texec m H sgn (se m sgn) (pc s) (RT m sgn (pc s)) None ->
      exec m s' (inl s1') ->
      texec m H sgn (se m sgn) (pc s') (RT m sgn (pc s')) (Some rt) ->
      evalsto m s' res' -> 
      high_result sgn res /\ high_result sgn res'.
    Proof.
      intros.
      inversion_mine H1; inversion_mine H2; inversion_mine H3; inversion_mine H4.
      Cleanexand.
      inversion_mine H1;
      inversion_mine H2;
      match goal with
        | [ H0 : pc s = pc s', H : instructionAt m (pc s) = ?P, H' : instructionAt m (pc s') = ?Q |- _ ] => 
          rewrite <- H0 in H'; rewrite H' in H; inversion H
      end.
    Qed.

    Lemma tevalsto_diff_high_result' : forall m sgn s s' p0 res res' (H:PM p m),
      pc s = pc s' -> 1 < p0 ->
      DEX_Framework.tevalsto PC Method (PM p) Sign istate rstate exec (pc) (registertypes) texec
        sub m H sgn (se m sgn) (RT m sgn) 1 s res -> 
      DEX_Framework.tevalsto PC Method (PM p) Sign istate rstate exec (pc) (registertypes) texec
        sub m H sgn (se m sgn) (RT m sgn) p0 s' res' -> 
      high_result sgn res /\ high_result sgn res'. 
    Proof.
      intros.
      inversion_mine H3. omega.
      inversion_mine H4.
      apply tevalsto_diff_high_result with (m:=m) (se:=se) (RT:=RT) (s:=s) (s':=s') (s1':=s2) (rt:=rt') (H:=H); auto.
      inversion_mine H2; auto.
      inversion H3; auto.
      inversion H8.
      inversion_mine H2; auto. inversion_mine H3; auto.
      inversion H8.
      apply DEX_Framework.tevalsto_evalsto in H5; auto.
      apply evalsto_Tevalsto2 with (p:=S n).
      constructor 2 with (s2:=s2); auto.
    Qed.

    Lemma high_result_indist : forall sgn res res0,
      high_result sgn res -> high_result sgn res0 -> rindist sgn res res0.
    Proof.
      intros.
      constructor.
      destruct sgn. destruct DEX_resType eqn:Hres.
      destruct res. destruct res0.
      destruct o. destruct o0.
      constructor 1 with (k:=t); auto.
      intros. inversion H0. simpl in H3. inversion H3. subst. contradiction.
      inversion H0. simpl in H1. inversion H1.
      destruct o0.
      inversion H. simpl in H1. inversion H1.
      inversion H0. simpl in H1. inversion H1.
      inversion H. inversion H0. subst. constructor 2; auto.
      simpl in H3. inversion H3.
      simpl in H1; inversion H1.
    Qed.

    Lemma high_reg_dec : forall rt r, high_reg rt r \/ ~high_reg rt r.
    Proof.
      intros.
      apply excluded_middle with (P:=high_reg rt r).
    Qed.

    Definition path := DEX_Framework.path Method istate rstate exec.

    Definition path_in_region := DEX_Framework.path_in_region PC Method step istate rstate exec pc.

    Inductive changed_at (m:Method) (i:istate) (r:Reg) : Prop :=
      | const_change : forall k v, instructionAt m (pc i) = Some (DEX_Const k r v) -> changed_at m i r
      | move_change : forall k rs, instructionAt m (pc i) = Some (DEX_Move k r rs) -> changed_at m i r
      | ineg_change : forall rs, instructionAt m (pc i) = Some (DEX_Ineg r rs) -> changed_at m i r
      | inot_change : forall rs, instructionAt m (pc i) = Some (DEX_Inot r rs) -> changed_at m i r
      | i2b_change : forall rs, instructionAt m (pc i) = Some (DEX_I2b r rs) -> changed_at m i r
      | i2s_change : forall rs, instructionAt m (pc i) = Some (DEX_I2s r rs) -> changed_at m i r
      | ibinop_change : forall op ra rb, instructionAt m (pc i) = Some (DEX_Ibinop op r ra rb) -> changed_at m i r
      | ibinopConst_change : forall op rs v, instructionAt m (pc i) = Some (DEX_IbinopConst op r rs v) -> changed_at m i r.

    Definition changed_at_t (m:Method) (i:istate) (r:Reg) : bool :=
      match instructionAt m (pc i) with
        | Some (DEX_Const k r' v) => Reg_eq r r'
        | Some (DEX_Move _ r' _) => Reg_eq r r'
        | Some (DEX_Ineg r' _) => Reg_eq r r'
        | Some (DEX_Inot r' _) => Reg_eq r r'
        | Some (DEX_I2b r' _) => Reg_eq r r'
        | Some (DEX_I2s r' _) => Reg_eq r r'
        | Some (DEX_Ibinop _ r' _ _) => Reg_eq r r'
        | Some (DEX_IbinopConst _ r' _ _) => Reg_eq r r'
        | _ => false
      end.

    Ltac inconsistent_ins :=
      match goal with | [H:instructionAt ?m ?i = Some ?P, H':instructionAt ?m ?i = Some ?Q |- _] => 
          rewrite H' in H; inversion H end.
    Ltac not_changed_auto := unfold not; intros HnotChangedAuto; inversion HnotChangedAuto; inconsistent_ins.

    Lemma changed_at_spec : forall m i r, if changed_at_t m i r then changed_at m i r else ~changed_at m i r.
    Proof.
      intros.
      unfold changed_at_t.
      destruct (instructionAt m (pc i)) eqn:Hins.
      unfold Reg_eq.
      destruct d; try (not_changed_auto; fail);
      try (destruct (Neq r rt) eqn:Heq; generalize (Neq_spec r rt); rewrite Heq; intros);
      try (constructor; subst; auto);
      try (not_changed_auto; contradiction).
      constructor 2 with (k:=k) (rs:=rs); subst; auto.
      constructor 1 with (k:=k) (v:=v); subst; auto.
      constructor 3 with (rs:=rs); subst; auto.
      constructor 4 with (rs:=rs); subst; auto.
      constructor 5 with (rs:=rs); subst; auto.
      constructor 6 with (rs:=rs); subst; auto.
      constructor 7 with (ra:=ra) (rb:=rb) (op:=op); subst; auto.
      constructor 8 with (rs:=r0) (v:=v) (op:=op); subst; auto.
      (* the case where the instructionAt is none *)
      unfold not; intros H; inversion H;
      match goal with 
        | [H:instructionAt m (pc i) = None, H':instructionAt m (pc i) = Some _ |- _] => rewrite H' in H; inversion H
      end.
    Qed.

    Inductive changed (m:Method) (i j: istate) : (path m i j) -> Reg -> Prop :=
      | changed_onestep : forall r (p:path m i j), changed_at m i r -> changed m i j p r
      | changed_path : forall k r (p:path m k j) (H:exec m i (inl k)), 
          changed m k j p r -> changed m i j (path_step Method istate rstate exec m i j k p H) r.

    Lemma changed_dec : forall m i j r (p:path m i j), 
      changed m i j (p) r \/ ~changed m i j (p) r. 
    Proof.
      intros.
      apply excluded_middle with (P:=changed m i j p0 r). 
    Qed.

    Lemma changed_high_onestep : forall m sgn s i j r (H: P (SM _ _ m sgn)),
      (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) kobs) ->
      region (cdr m (PM_P _ H)) s (pc i) ->
      exec m i (inl j) ->
      changed_at m i r -> high_reg (RT m sgn (pc j)) r.
    Proof.
      intros m sgn s i j r H Hhighreg Hreg Hexec Hchanged_at.
      assert (Hexec':=Hexec).
      apply tcc0 with (1:=PM_P _ H) in Hexec'.
      destruct (typable_hyp m sgn H) as [T1 [T2 T3]]. 
      specialize T3 with (i:=pc i) (j:=pc j) (1:=Hexec'). 
      destruct T3 as [rt [Htexec Hsub]].
      specialize Hhighreg with (pc i). apply Hhighreg in Hreg. 
      inversion Htexec as [x [Htexec' Hins]].
      inversion_mine Hchanged_at;
      try (rewrite H0 in Hins; injection Hins; intros; subst; 
      inversion_mine Htexec';
      unfold high_reg;
      generalize sub_forall; intros Hsub_forall;
      specialize Hsub_forall with (1:=Hsub) (r:=r);
      destruct (VarMap.get _ (RT m sgn (pc j)) r) eqn:Hval);
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (pc j)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end).
      (* Const *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (se m sgn (pc i))) r = Some k) as Hget. 
      exists (se m sgn (pc i)). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
      (* Move *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) k_rs)) r = Some k) as Hget. 
      exists ((L.join (se m sgn (pc i)) k_rs)). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
      apply leql_join_each in Hleql; destruct Hleql; auto.
      (* Ineg *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* Inot *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.  
      (* I2b *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* I2s *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* Ibinop *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join (L.join ka kb) (se m sgn (pc i)))) r = Some k) as Hget. 
      exists (L.join (L.join ka kb) (se m sgn (pc i))). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* IbinopConst *)
      assert (exists k, VarMap.get L.t (VarMap.update L.t (RT m sgn (pc i)) r (L.join ks (se m sgn (pc i)))) r = Some k) as Hget. 
      exists (L.join ks (se m sgn (pc i))). rewrite VarMap.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite VarMap.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
    Defined.

    Ltac clear_other_ins ins :=
      match goal with 
      | [H:instructionAt ?m ?pc0 = Some ?ins, Hins:instructionAt ?m ?pc = Some ins |- _] =>
        try (simpl in Hins; rewrite H in Hins; inversion Hins)
      end.

    Ltac not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r:=
      simpl; subst;
      destruct (typable_hyp m sgn HPM) as [T1 [T2 T3]];
      assert (Hexec':=Hexec); apply tcc0 with (1:=PM_P _ HPM) in Hexec';
      specialize T3 with (i:=pc0) (j:=pc') (1:=Hexec');
      destruct T3 as [rt' [Htexec Hsub]];
      inversion Htexec as [ins [Htexec' Hins']];
      rewrite H in Hins'; inversion Hins'; subst; inversion Htexec'; subst;
      unfold high_reg; intros;
      destruct (VarMap.get L.t (RT m sgn pc0) r) eqn:Hrt0.

    Lemma not_changed_same_onestep : forall m sgn i j r (HPM: P (SM _ _ m sgn)),
      ~changed_at m i r -> 
      exec m i (inl j) ->
      (indist_reg_val i j r) /\ (high_reg (RT m sgn (pc i)) r -> high_reg (RT m sgn (pc j)) r). 
    Proof.
      intros m sgn i j r HPM Hnchanged_at Hexec.
      generalize (changed_at_spec m i r); intros Hchanged_at_dec.
      destruct (changed_at_t m i r) eqn:Hchanged_at.
      contradiction.
      unfold changed_at_t in Hchanged_at.
      destruct (instructionAt m (pc i)) eqn:Hins. 
      destruct d eqn:Hins'. 
      (* const *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Nop).
      split.
      unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* move *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Move k rt rs).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Return *)
      inversion Hexec. inversion H2. inversion_mine H3; clear_other_ins (DEX_Return).
      (* VReturn *)
      inversion Hexec. inversion H2. inversion_mine H3; clear_other_ins (DEX_VReturn k rt).
      (* Const *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Const k rt v).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* goto *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Goto o).
      split.
      unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (VarMap.get L.t (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* PackedSwitch *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_PackedSwitch rt firstKey size l).
      (* the case where the successor is the next instruction *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (VarMap.get L.t (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the targets *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* SparseSwitch *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_SparseSwitch rt size l).
      (* the case where the successor is the next instruction *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (VarMap.get L.t (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the targets *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ifeq *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ifcmp cmp ra rb o).
      (* the case where the successor is the target *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (VarMap.get L.t (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the next instruction *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ifz *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ifz cmp r0 o).
      (* the case where the successor is the target *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (VarMap.get L.t (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the next instruction *)
      split. unfold indist_reg_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ineg *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ineg rt rs).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction. 
      (* Inot *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Inot rt rs).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* I2b *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_I2b rt rs).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.  
      (* I2s *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_I2s rt rs).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.  
      (* Ibinop *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ibinop op rt ra rb).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* IbinopConst *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_IbinopConst op rt r0 v).
      split.
      unfold indist_reg_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (VarMap.get L.t (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite VarMap.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (VarMap.get L.t (RT m sgn pc0) r <> None) as Hget.
      destruct (VarMap.get L.t (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply VarMap.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply VarMap.in_dom_get_some in H; contradiction
      end). 
      contradiction. 
      (* the case where there is no instruction *)
      inversion Hexec. inversion_mine H2. apply False_ind. inversion_mine H3; 
      match goal with 
        | [H:instructionAt m ?pc0 = Some ?ins, Hins:instructionAt m ?pc = None |- _] =>
          simpl in Hins; rewrite H in Hins; inversion Hins
      end.  
    Qed.

    Lemma not_changed_inv1 : forall m i j r (Hpath: path m i j),
      ~ changed m i j Hpath r -> ~changed_at m i r.
    Proof.
      intros. unfold not in *; intro Hgoal; apply H; constructor 1; auto.
    Qed.

    Lemma not_changed_inv2 : forall m i j k r (Hpath: path m k j) (e:exec m i (inl k)),
      ~ changed m i j (path_step Method istate rstate exec m i j k Hpath e) r -> ~changed m k j Hpath r.
    Proof.
      intros. unfold not in *; intro Hgoal; apply H; constructor 2; auto.
    Qed.

    Lemma not_changed_same : forall m sgn i j (Hpath: path m i j) r (H: P (SM _ _ m sgn)) ,
      ~changed m i j Hpath r -> 
      (indist_reg_val i j r) /\ (high_reg (RT m sgn (pc i)) r -> high_reg (RT m sgn (pc j)) r). 
    Proof.
      intros m sgn i j Hpath r H H0.
      induction Hpath; intros.
      (* base case *)
      apply not_changed_inv1 in H0.
      apply not_changed_same_onestep with (1:=H); auto. 
      (* induction step *)
      assert (H0':=H0).
      apply not_changed_inv2 in H0.
      apply IHHpath in H0.
      assert (~ changed m i j (path_step Method istate rstate exec m i j k Hpath e) r -> ~ changed_at m i r).
      unfold not; intros. apply H1.
      constructor 1. auto. apply H1 in H0'.
      elim not_changed_same_onestep with (m:=m) (sgn:=sgn) (i:=i) (j:=k) (1:=H) (2:=H0') (3:=e); intros.
      inversion H0.
      split; auto.
      unfold indist_reg_val in *.
      destruct (DEX_Registers.get (snd i) r);
      destruct (DEX_Registers.get (snd k) r);
      destruct (DEX_Registers.get (snd j) r); try (congruence); try (contradiction). 
    Qed.

    Lemma changed_high : forall m sgn s i j r (H:P (SM _ _ m sgn)) (Hpath: path m (* sgn (PM_P _ H) *) i j), 
      (forall k:PC, region (cdr m (PM_P _ H)) s (* kd *) k -> ~ L.leql (se m sgn k) kobs) ->
      path_in_region m (cdr m (PM_P _ H)) s i j Hpath ->
      region (cdr m (PM_P _ H)) s (pc i) ->
      junc (cdr m (PM_P _ H)) s (pc j) ->
      changed m i j Hpath r -> high_reg (RT m sgn (pc j)) r.
    Proof.
      intros.
      induction Hpath.
      (* base case *)
      inversion_mine H4; apply changed_high_onestep with (s:=s) (i:=i) (H:=H); auto.

      (* induction case *)
      inversion H4.
      (* the case where the change is happening at the current step *)
      generalize changed_high_onestep; intros.
      specialize H8 with (m:=m) (sgn:=sgn) (s:=s) (i:=i) (j:=k) (r:=r) (H:=H) (1:=H0) (2:=H2) (3:=e) (4:=H5).
      elim (changed_dec m k j r Hpath); intros.
      apply IHHpath; auto. inversion H1; auto.
      assert ((existT (fun k : istate => path m k j) k p2) = (existT (fun k : istate => path m k j) k Hpath)).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H11); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      assert (p2 = Hpath).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H14); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      subst; auto.
      inversion H1. inversion H13; auto.
      apply not_changed_same with (sgn:=sgn) in H9; auto.
      inversion H9; auto.
      (* the case where the change is happening in the chain *)
      assert ((existT (fun k : istate => path m k j) k p1) = (existT (fun k : istate => path m k j) k Hpath)).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H9); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      assert (p1 = Hpath).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H5); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      rewrite H11 in H10. inversion H1. 
      assert ((existT (fun k : istate => path m k j) k p2) = (existT (fun k : istate => path m k j) k Hpath)).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H13); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      assert (p2 = Hpath).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H16); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      apply IHHpath; subst; auto. inversion H15; auto. 
    Qed.

    Lemma indist2_intra : forall m sgn se rt ut ut' s s' u u',
      forall H0:P (SM _ _ m sgn),
        indist sgn rt rt  s s' ->
        pc s = pc s' ->
        exec m s (inl _ u) ->
        exec m s' (inl _ u') ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
          indist sgn ut ut' u u'.
    Proof.
      unfold pc; intros m sgn se0 rt ut ut' s s' u u' H Hindist Hpc Hexec Hexec' Htexec Htexec'.
      inversion_mine Hexec. inversion_mine Hexec'.
  
      elim DEX_BigStepWithTypes.exec_intra_instructionAt with (1:=H3); intros i Hi.
      destruct Htexec as [i' [Ti Ti']]; DiscrimateEq.
      
      assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i s rt u ut).
        elim well_types_imply_exec_intra with (1:=H3) (3:=Ti); eauto. 
      destruct Htexec' as [i' [Ui Ui']]; DiscrimateEq.
      rewrite Hpc in Ui.
      assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i s' rt u' ut').
        elim well_types_imply_exec_intra with (1:=H4) (3:=Ui); eauto.
      rewrite Hpc in Ui'; auto. 
      inversion_mine Hindist.
      destruct u as [pu ru].
      destruct u' as [pu' ru'].
      constructor.
      eapply indist2_intra; eauto. 
      constructor; eauto.
      rewrite Hpc; constructor; eauto.
      simpl. simpl in Hpc.
      rewrite <- Hpc in H2; auto.
    Qed.
    
    Lemma tcc3 : forall m rt1 rt2 s1 s2,
      indist m rt1 rt2 s1 s2 -> indist m rt2 rt1 s2 s1.
    Proof.
      intros.
      inversion_clear H; constructor.
      apply st_in_sym; auto.
    Qed.

    Lemma indist_return_value_sym : forall sgn vu' vu,
      indist_return_value kobs sgn vu' vu ->
      indist_return_value kobs sgn vu vu'.
    Proof.
      intros.
      inversion_clear H.
      constructor 1 with k; auto; intros.
      apply Value_in_sym; auto.
      constructor; auto.
    Qed.

    Lemma indist2_return : forall (m : Method) (sgn : Sign) (se : PC -> L.t) 
      (rt : registertypes) (s s' : istate) (u u' : rstate) ,
      forall H:P (SM Method Sign m sgn),
        indist sgn rt rt s s' ->
        pc s = pc s' ->
        exec m s (inr istate u) ->
        exec m s' (inr istate u') ->
        texec m (PM_P _ H) sgn se (pc s) rt None ->
        texec m (PM_P _ H) sgn se (pc s) rt None ->
          rindist sgn u u'.
    Proof.
      unfold pc; intros m sgn se0 rt s s' u u' H Hindist Hpc Hexec Hexec' Htexec Htexec'.
      destruct Htexec as [i' [Ti Ti']].
      destruct Htexec' as [i [Ui Ui']]; DiscrimateEq.
      destruct s as [pp regs].
      destruct s' as [pp' regs'].
      simpl in Hpc; subst; simpl in *.
      destruct u as [vu].
      destruct u' as [vu'].
      inversion_mine Hindist;
      inversion_mine Hexec; inversion_mine Hexec'.
  (**)
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs) rt (Normal vu)).
        elim well_types_imply_exec_return with (1:=H3) (3:=Ti); auto.
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs') rt (Normal vu')).
        elim well_types_imply_exec_return with (1:=H5) (3:=Ui); auto.
      apply DEX_BigStepWithTypes.exec_return_normal in H0.
      apply DEX_BigStepWithTypes.exec_return_normal in H1.
      constructor. 
      apply indist2_return with (1:=H0) (2:=H1) (3:=H4). 
    Qed.

    Section well_formed_lookupswitch.

      Variable hyp : forall m sgn, P (SM _ _ m sgn) -> well_formed_lookupswitch m.

      Lemma soap2_basic_intra : forall m sgn se rt ut ut' s s' u u',
        forall H0:P (SM _ _ m sgn),
          indist sgn rt rt s s' -> 
          pc s = pc s' ->
          exec m s (inl _ u) ->
          exec m s' (inl _ u') -> 
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
          pc u <> pc u' -> 
          forall j:PC, region (cdr m (PM_P _ H0)) (pc s) j -> ~ L.leql (se j) kobs.
      Proof.
        intros m sgn se0 rt ut ut' s s' u u' H0 Hindist Hpcs Hexec Hexec' Htexec Htexec' Hpcu.
        intros j Hreg.
        destruct Htexec as [i' [Ti Ui]].
        destruct Htexec' as [i [Ti' Ui']]. DiscrimateEq.
        inversion_mine Hindist.
        destruct u as [ppu regs].
        destruct u' as [ppu' regs'].
        inversion_mine Hexec'; inversion_mine Hexec; simpl in *; subst.
  (**)
        assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,r1) rt (ppu,regs) ut).
             elim well_types_imply_exec_intra with (1:=H5) (3:=Ti); auto.
        assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,r2) rt (ppu',regs') ut').
             elim well_types_imply_exec_intra with (1:=H4) (3:=Ti'); auto.
        apply DEX_BigStepWithTypes.exec_intra_normal in H1;
        apply DEX_BigStepWithTypes.exec_intra_normal in H2.
        apply soap2_intra with (5:=H2) (4:=H1) (7:= H); auto.
        specialize hyp with (m:=m) (sgn:=sgn) (1:=H0); auto.
      Qed.
    End well_formed_lookupswitch.

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
      (* *)
      specialize H2 with rn. inversion H2.
      (* case where both are high *)
        assert_some_not_none rt rn H6.
        apply VarMap.get_some_in_dom in H9. rewrite H3 in H9.
        apply VarMap.in_dom_get_some in H9.
        assert_not_none_some rt' rn k'' t.
        destruct H10 as [k'']. 
        constructor 1 with (k:=k) (k':=k''); auto.
        symmetry in H6.
        specialize H4 with (r:=rn) (1:=H6) (2:=H10).
        apply not_leql_trans with (k1:=k'); auto.
      (* case where both are low *)
      constructor 2; auto.
      auto.
    Qed.

    Lemma sub_simple : forall sgn rt rt' rt0 s s0,
      indist sgn rt0 rt s0 s ->
      sub rt rt' ->
      indist sgn rt0 rt' s0 s.
    Proof.
      intros.
      inversion_mine H; inversion_mine H1; constructor.
      constructor. eapply Regs_in_sub_simple; eauto.
    Qed.

    Lemma branch_indist : forall m sgn s s' u u' (H0:P (SM _ _ m sgn)), 
      pc s = pc s' ->
      indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) s s' ->
      exec m s (inl u) ->
      exec m s' (inl u') ->
      pc u <> pc u' ->
      indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) u u'.
    Proof.
      intros m sgn s s' u u' HPM Hpc Hindist Hexec Hexec' Hpc'.
      rewrite <- Hpc in Hindist.
      destruct (typable_hyp m sgn HPM) as [T1 [T2 T3]].
      assert (e:=Hexec). apply tcc0 with (1:=PM_P _ HPM) in e.
      assert (e':=Hexec'). apply tcc0 with (1:=PM_P _ HPM) in e'.
      assert (T3':=T3).
      specialize T3 with (i:=pc s) (j:=pc u) (1:=e).
        destruct T3 as [ut [Htexec Hsub]].
      specialize T3' with (i:=pc s') (j:=pc u') (1:=e').
        destruct T3' as [ut' [Htexec' Hsub']].
      apply sub_simple with (2:=Hsub'). apply tcc3.
      apply sub_simple with (2:=Hsub). apply tcc3.
      apply indist2_intra with (m:=m) (se:=se m sgn) (rt:=(RT m sgn (pc s))) (s:=s) (s':=s') (H0:=HPM)
        (ut:=ut) (ut':=ut'); auto.
      rewrite Hpc; auto.
    Qed.

  End TypableProg.

End hyps. 

Require check_cdr.
Module MapKind' := MapOption_Base Map2P.
  Module MapKind <: MAP with Definition key := Kind := Map_Of_MapBase MapKind'.
  Module CheckCdr := check_cdr.Make MapN.

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
    Variable m : DEX_Method.
    Definition for_all_steps : (PC -> option PC -> bool) -> bool :=
      fun test => for_all_steps_m m (fun pc i => test pc).
    Definition test_all_steps : (PC -> option PC -> bool) -> list (PC*bool) :=
      fun test => test_all_steps_m m (fun pc i => test pc).

    Lemma for_all_steps_true : forall test,
      for_all_steps test = true ->
      forall (i : PC) (oj : option PC),
        step p m i oj -> test i oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_steps_m_true m (fun p i => test p)); eauto.
    Qed.

    Definition for_all_succs : PC -> (option PC -> bool) -> bool :=
      for_all_succs_m m.

    Lemma for_all_succs_true : forall i test,
      for_all_succs i test = true ->
      forall oj, step p m i oj -> test oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_succs_m_true m); eauto.
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
      { cdr : CDR (step p m) |
        forall i j,
          region cdr i j -> CheckCdr.region reg i j}.
    Proof
    (CheckCdr.check_soap_true (step p m) for_all_steps
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
  Variable reg : Method -> MapN.t (MapN.t bool).
  Variable jun : Method -> MapN.t (CheckCdr.PC).
  Variable cdr_checked : forall m,
    PM p m ->  check_cdr m (reg m) (jun m) = true.

  Definition cdr_local : forall m, 
    PM p m -> CDR (step p m) :=
    fun m H => let (cdr_local,_) := 
      check_cdr_prop p m (reg m) (jun m)
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

   Definition selift m sgn i k :=
    for_all_region m i (fun j => L.leql_t k (se m sgn j)). 

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
                     eq_set_test (VarMap.dom L.t rt) (DEX_BYTECODEMETHOD.regs bm) &&
                     check_rt0_rec rt sgn (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level)
    end.

  Lemma check_rt0_rec_true : forall m sgn bm default_level,
    check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn 
      (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) default_level = true ->
    DEX_METHOD.body m = Some bm -> 
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = VarMap.get _ (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)).
  Proof.
    intros. 
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
      for_all_steps_m m
      (fun i ins oj => 
        DEX_tcheck m sgn (se m sgn) (selift m sgn) (RT m sgn) i ins)
    ).

  Lemma PC_eq_dec' : forall x y : PC, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

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
      forall i, init_pc m i -> eq_rt (RT m sgn i) (rt0 m sgn).
  Proof.
    unfold check; intros.
    inversion_mine H1.
    assert (T:=for_all_P_true _ _ H _ _ H0).
    destruct (andb_prop _ _ T) as [TT _].
    unfold rt0. rewrite H2.
    apply check_correct1_aux with (m:=m) (bm:=bm) (sgn:=sgn); auto.
  Qed.

  Lemma check_correct2 : check = true ->
    forall m sgn (h:P p (SM _ _ m sgn)),
      forall i,
        step p m i None ->
        texec p cdr_local m (PM_P _ _ h) sgn (se m sgn) i (RT m sgn i) None.
  Proof.
    unfold check; intros.
    assert (T:=for_all_P_true _ _ H _ _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    exists ins; split; [idtac|assumption].
    assert (T':=for_all_steps_m_true _ _ TT _ _ _ H2 H3).
    apply tcheck_correct1 with (selift:=selift m sgn) (m:=m); auto.
  Qed.

  Lemma tsub_sub : forall rt1 rt2,
    tsub_rt rt1 rt2 = true -> sub rt1 rt2.
  Proof.
    intros.
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
        step p m i (Some j) ->
        exists rt,
          texec p cdr_local m (PM_P _ _ h) sgn (se m sgn) i (RT m sgn i) (Some rt) 
          /\ sub rt (RT m sgn j).
  Proof.
    unfold check; intros.
    assert (T:=for_all_P_true _ _ H _ _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    assert (T':=for_all_steps_m_true _ _ TT _ _ _ H2 H3).
    elim (tcheck_correct2 m sgn (region (cdr_local _ (PM_P _ _ h)))  (se m sgn)
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
    TypableProg p cdr_local se RT.
  Proof.
    intros H m sgn H1.
    constructor.
    apply check_correct1; auto.
    split.
    apply check_correct2; auto.
    apply check_correct3; auto.
  Qed.

End CheckTypable.

Theorem ni_safe : forall (kobs:L.t) (p:DEX_ExtendedProgram),
  forall cdr : forall m, PM p m -> CDR (step p m),
    (exists se, exists RT, TypableProg p cdr se RT) ->
    (forall m sgn, P p (SM _ _ m sgn) -> well_formed_lookupswitch m) ->
    forall m sgn i r1 r2 res1 res2,
      P p (SM _ _ m sgn) ->
      init_pc m i -> 
      indist kobs sgn (rt0 m sgn) (rt0 m sgn) (i, r1) (i, r2) ->
      evalsto p m (i,r1) (res1) -> 
      evalsto p m (i,r2) (res2) -> 
        indist_return_value kobs sgn res1 res2.
Proof.
  intros kobs p cdr [se [RT HT]] Hwfl m sgn i r1 r2 res1 res2 H Hinit Hindist Hevalsto1 Hevalsto2.
  assert (Hni:=safe_ni kobs PC Method (step p) (PM p) cdr Reg Sign istate rstate (exec p) pc 
    (tcc0 p) (tcc1 p) registertypes (texec p cdr) (high_reg kobs)
    (indist_reg_val) (indist_reg_val_trans) (indist_reg_val_sym)
    (indist kobs) (indist_from_reg kobs) (indist_reg_from_indist kobs)
    (rindist kobs) (tcc3 kobs) (high_result kobs) (rt0) (init_pc)
    (P p) (PM_P p) (indist2_intra kobs p cdr) (indist2_return kobs p cdr)
    (soap2_basic_intra kobs p cdr Hwfl) (sub) (sub_simple kobs)
    (tevalsto_high_result kobs p cdr ) (tevalsto_diff_high_result' kobs p cdr ) (high_result_indist kobs)
    (eq_rt) (indist_morphism_proof kobs) se RT HT (changed p) (changed_high kobs p cdr se RT HT)
    (not_changed_same kobs p cdr se RT HT) (high_reg_dec kobs) (changed_dec p) (branch_indist kobs p cdr se RT HT)
    m sgn
  ). 
  elim evalsto_Tevalsto with (1:=Hevalsto1); intros p1 He1.
  elim evalsto_Tevalsto with (1:=Hevalsto2); intros p2 He2.
  elim Hni with (6:=He1) (7:=He2); auto.
Qed.

Definition check_all_cdr 
  (p:DEX_Program)
  (reg : Method -> MapN.t (MapN.t bool))
  (jun : Method -> MapN.t (CheckCdr.PC)) : bool :=
  for_all_methods p (fun m => check_cdr m (reg m) (jun m)).

Lemma check_all_cdr_correct : forall p reg jun,
  check_all_cdr p reg jun = true ->
  forall m, PM p m -> check_cdr m (reg m) (jun m) = true.
Proof.
  unfold check_all_cdr; intros.
  apply (for_all_methods_true p (fun m => check_cdr m (reg m) (jun m))); auto.
Qed.

Lemma IntraStep_evalsto_aux : forall p m s r,
  DEX_BigStepAnnot.DEX_IntraStepStar p.(DEX_prog) m s r ->
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
  DEX_BigStepAnnot.DEX_BigStep p.(DEX_prog) m s r ->
  evalsto p m s r.
Proof.
  intros.
  apply IntraStep_evalsto_aux with (1:=H).
Qed.

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

  Definition check_well_formed_lookupswitch_m m := 
    for_all_instrs_m m 
    (fun i ins => match ins with 
                    | DEX_SparseSwitch reg size l => check_functionnal_list l
                    | _ => true
                  end).

  Definition check_well_formed_lookupswitch_m_correct : forall m,
    check_well_formed_lookupswitch_m m = true ->
    forall pc reg size l i o1 o2,
      instructionAt m pc = Some (DEX_SparseSwitch reg size l) ->
      In (i, o1) l -> In (i, o2) l -> o1=o2.
  Proof.
    unfold check_well_formed_lookupswitch_m; intros.
    generalize (for_all_instrs_m_true _ _ H).
    intros.
    generalize (H3 pc0 (DEX_SparseSwitch reg size l)); rewrite H0.
    intros T.
    assert (TT:=T (refl_equal _)).
    clear T H3 H.
    eapply check_functionnal_list_correct; eauto.
  Qed.

  Definition check_well_formed_lookupswitch p :=
    for_all_methods p check_well_formed_lookupswitch_m.

  Lemma check_well_formed_lookupswitch_correct : forall (p:DEX_ExtendedProgram),
    check_well_formed_lookupswitch p = true ->
    forall m sgn,
      P p (SM _ _ m sgn) -> well_formed_lookupswitch m.
  Proof.
    unfold check_well_formed_lookupswitch; intros.
    unfold well_formed_lookupswitch.
    intros.
    eapply (check_well_formed_lookupswitch_m_correct m); try eauto.
    apply (for_all_methods_true _ _ H).
    inversion_mine H0; auto.
  Qed.

End  well_formed_lookupswitch.

Theorem correctness : forall
  (p:DEX_ExtendedProgram),
  check_well_formed_lookupswitch p = true ->
  forall (kobs:L.t)
    (reg : Method -> MapN.t (MapN.t bool))
    (jun : Method -> MapN.t (CheckCdr.PC)),
    check_all_cdr p reg jun = true ->
    forall 
      (se : Method -> DEX_sign -> PC -> L.t) 
      (RT :  Method -> DEX_sign -> PC -> VarMap.t L.t),
      check p se RT reg = true ->
      forall m sgn i res1 res2 r1 r2,
        P p (SM _ _ m sgn) ->
        init_pc m i -> 
        indist kobs sgn (rt0 m sgn) (rt0 m sgn) (i, r1) (i, r2) ->
        evalsto p m (i,r1) res1 -> 
        evalsto p m (i,r2) res2 -> 

          indist_return_value kobs sgn res1 res2.
Proof.
  intros p Hwfl kobs reg jun Hcheck se RT.
  intros Hc.
  intros m sgn i res1 res2 r1 r2 H H0 H1 H2.
  assert (T:=check_all_cdr_correct p (reg) (jun) Hcheck).
  assert (TT:=check_correct _ _ _ _ jun T Hc).
  eapply ni_safe; eauto.
  apply check_well_formed_lookupswitch_correct; auto.
Qed.

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
  match instructionAt m i with
    | None => false
    | Some ins =>
      DEX_tcheck m sgn (se_get se) (selift_m reg se) (RT_get RT) i ins
  end.

Definition check_ni (p:DEX_ExtendedProgram) reg jun se RT : bool :=
      check_well_formed_lookupswitch p &&
      check_all_cdr p reg jun &&
      check p se RT reg.

Definition NI (p:DEX_ExtendedProgram) : Prop :=
  forall kobs m sgn i r1 r2 res1 res2,
    P p (SM _ _ m sgn) ->
    init_pc m i -> 
    indist kobs sgn (rt0 m sgn) (rt0 m sgn) (i,r1) (i,r2) ->
    DEX_BigStepAnnot.DEX_BigStep p.(DEX_prog) m (i,r1) (res1) -> 
    DEX_BigStepAnnot.DEX_BigStep p.(DEX_prog) m (i,r2) (res2) -> 
      indist_return_value kobs sgn res1 res2.

Theorem check_ni_correct : forall p reg jun se RT,
  check_ni p reg jun se RT = true ->
  NI p.
Proof.
  unfold check_ni, NI. intros p reg jun se RT HcheckTypable kobs m sgn i r1 r2 res1 res2
    HPM Hinit Hindist Hstep1 Hstep2.
  destruct (andb_prop _ _ HcheckTypable) as [HcheckTypable' Hcheck].
  destruct (andb_prop _ _ HcheckTypable') as [Hwfl Hcheck_all_cdr].
  generalize (BigStep_evalsto _ _ _ _ Hstep1). 
  generalize (BigStep_evalsto _ _ _ _ Hstep2). 
  intros Hevalsto2 Hevalsto1.
  assert (T:=for_all_P_true _ _ Hcheck _ _ HPM).
  destruct (andb_prop _ _ T).
  eapply correctness with (8:=Hevalsto2) (7:=Hevalsto1); eauto.
Qed.