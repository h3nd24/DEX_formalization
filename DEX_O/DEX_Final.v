Require Export DEX_Framework.
Require Export DEX_ProofBigStepWithType.
Require Export DEX_ElemLemmas.
Require Export DEX_ElemLemmaIntra.
Require Export DEX_ElemLemmaReturn.
Require Export DEX_step.
Require Export DEX_typing_rules.

Import DEX_BigStepWithTypes DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Ltac assert_some_not_none rt rn H := 
    assert (MapList.get rt rn <> None) by solve [
    destruct (MapList.get rt rn) as [a | ]; 
      try (intros Hf; inversion Hf);
      try (inversion H)].

Ltac assert_not_none_some rt rn k t:= 
   assert (exists k, Some k = MapList.get rt rn) by solve [
    destruct (MapList.get rt rn) as [t | ] eqn:Hget; 
      try (exists t; auto); 
      try (apply False_ind; auto)].

Definition ValidMethod (p:DEX_Program) (m:DEX_Method) : Prop :=
  exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

Definition step (p:DEX_Program) : DEX_Method -> DEX_PC -> option DEX_PC -> Prop := 
fun m pc (* tau *) opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ DEX_step m pc i opc.

Variable RT_domain_eq : forall rt1 rt2, eq_set (@MapList.dom L.t rt1) (@MapList.dom L.t rt2).
Lemma RT_domain_same : forall rt1 rt2 r, In r (@MapList.dom L.t rt1) -> In r (@MapList.dom L.t rt2). 
Proof. intros; rewrite RT_domain_eq with (rt2:=rt1); auto. Qed.
Lemma RT_domain_length_same : forall rt1 rt2, length (@MapList.dom L.t rt1) = length (@MapList.dom L.t rt2). 
Proof. intros. generalize (RT_domain_eq rt1 rt2); intros. inversion H; auto. Qed.

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

  Definition registertypes : Type := TypeRegisters.
  Definition pbij : Set := FFun.t DEX_Location.

  Definition pc : istate -> PC := @fst _ _.

  Definition texec : forall m, PM p m -> Sign -> (PC -> L.t) ->
    PC -> registertypes -> option registertypes -> Prop :=
    fun m H sgn se pc rt ort =>
      exists i, texec p sgn (region (cdr m H)) se pc i rt ort
        /\ instructionAt m pc = Some i.

  Inductive indist : Sign -> registertypes -> registertypes -> 
      pbij -> pbij -> istate -> istate -> Prop :=
    indist_def :forall sgn rt1 rt2 b1 b2 r1 r2 h1 h2 pc1 pc2,
      st_in kobs (DEX_ft p) b1 b2 rt1 rt2 (pc1,h1,r1) (pc2,h2,r2) ->
      indist sgn rt1 rt2 b1 b2 (pc1,(h1,r1)) (pc2,(h2,r2)).

  Inductive indist_heap : istate -> istate -> pbij -> pbij -> Prop :=
  | indist_heap_cons : forall pc1 h1 r1 pc2 h2 r2 b1 b2,
      hp_in kobs (DEX_ft p) b1 b2 h1 h2 -> indist_heap (pc1, (h1, r1)) (pc2, (h2, r2)) b1 b2.

  Lemma indist_heap_sym : forall s1 s2 b1 b2,
    indist_heap s1 s2 b1 b2 -> indist_heap s2 s1 b2 b1.
  Proof.
    intros. inversion H; auto. constructor. apply hp_in_sym; auto.
  Qed.

  Lemma indist_heap_from_indist : forall sgn rt1 rt2 s1 s2 b1 b2,
    indist sgn rt1 rt2 b1 b2 s1 s2 -> indist_heap s1 s2 b1 b2.
  Proof.
    intros. inversion H. inversion H0. constructor; auto.
  Qed. 

  Inductive rindist : Sign -> pbij -> pbij -> rstate -> rstate -> Prop :=
  | rindist_def : forall sgn r1 r2 b1 b2 h1 h2,
    hp_in kobs (DEX_ft p) b1 b2 h1 h2 ->
    indist_return_value kobs h1 h2 sgn r1 r2 b1 b2 -> 
    rindist sgn b1 b2 (h1,r1) (h2,r2).

  Definition default_level := L.High.

  Inductive init_pc (m:Method) : PC -> Prop :=
    init_pc_def : forall bm,
      DEX_METHOD.body m = Some bm ->
      init_pc m (DEX_BYTECODEMETHOD.firstAddress bm).

  Definition rt0 (m:Method) (sgn:Sign): registertypes := 
  match DEX_METHOD.body m with
  | Some bm => (Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level))
  | None => MapList.empty L.t
  end.

  Definition ni := ni _ _ _ _ _ exec pc registertypes pbij indist rindist 
    rt0 init_pc border P.

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
  | forall_sub : forall rt1 rt2, eq_set (MapList.dom rt1) (MapList.dom rt2) ->
      (forall r k1 k2, Some k1 = MapList.get rt1 r -> Some k2 = MapList.get rt2 r -> L.leql k1 k2) 
      -> sub rt1 rt2
  | nil_sub : sub (MapList.empty _) (MapList.empty _). 

  Lemma sub_forall : forall rt rt', sub rt rt' -> 
    (forall r k1 k2, 
      Some k1 = MapList.get rt r /\ Some k2 = MapList.get rt' r -> 
    L.leql k1 k2).
  Proof. intros. inversion H0; auto.
    inversion H; subst. apply H4 with (r:=r); auto.
    rewrite MapList.get_empty in H1. inversion H1.
  Qed.

  Lemma indist_morphism_proof : forall (y : Sign) (x y0 : registertypes),
    eq_rt x y0 ->
    forall x0 y1 : registertypes,
    eq_rt x0 y1 -> forall (s2 s3 : istate) (b2 b3 : pbij), 
    indist y x x0 b2 b3 s2 s3 <-> indist y y0 y1 b2 b3 s2 s3.
  Proof.
    split; intros.
    (* -> *)
    inversion_mine H1.
    constructor.
    inversion_mine H2.
    inversion_mine H4.
    constructor; auto; constructor; intros.
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
      apply MapList.get_some_in_dom in H10.
      apply MapList.get_some_in_dom in H11.      
      constructor 1 with (k:=k) (k':=k'); auto.
      rewrite eq_rt_get with (rt1:=y0) (rt2:=x); auto. apply eq_rt_sym; auto.
      rewrite <- H3; auto.
      rewrite eq_rt_get with (rt1:=y1) (rt2:=x0); auto. apply eq_rt_sym; auto.
      rewrite H in H11; auto.
      constructor 2. auto.
    (* <- *)
    inversion_mine H1.
    constructor.
    inversion_mine H2.
    inversion_mine H4.
    constructor; auto; constructor; intros.
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
      apply MapList.get_some_in_dom in H10.
      apply MapList.get_some_in_dom in H11.      
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
      match MapList.get rt r with
      | None => False
      | Some k => ~L.leql k kobs
      end.

    Variable not_high_reg : forall rt r, ~high_reg rt r -> (exists k, MapList.get rt r = Some k /\ L.leql k kobs).

    Definition indist_reg_val (s1 s2: istate) (b1 b2: pbij) (r: Reg) : Prop :=
      let rho1 := snd (snd s1) in
      let rho2 := snd (snd s2) in
        match DEX_Registers.get rho1 r, DEX_Registers.get rho2 r with
        | Some v1, Some v2 => Value_in b1 b2 v1 v2
        | None, None => True
        | _, _ => False
        end.

    (* Lemma indist_reg_val_trans : forall s1 s2 s3 b1 b2 b3 r, 
      FFun.is_inj b2 ->
      indist_reg_val s1 s2 b1 b2 r -> 
      indist_reg_val s2 s3 b2 b3 r -> 
      indist_reg_val s1 s3 b1 b3 r.
    Proof.
      intros.
      unfold indist_reg_val in *.
      destruct (DEX_Registers.get (snd (snd s1)) r);
      destruct (DEX_Registers.get (snd (snd s2)) r);
      destruct (DEX_Registers.get (snd (snd s3)) r); auto.
      apply Value_in_trans with (b2:=b2) (v2:=d0); auto.
      inversion H0.
    Qed. *)

    Lemma indist_reg_val_sym : forall s1 s2 b1 b2 r, 
      indist_reg_val s1 s2 b1 b2 r -> indist_reg_val s2 s1 b2 b1 r.
    Proof.
      unfold indist_reg_val in *.
      intros.
      destruct (DEX_Registers.get (snd (snd s1)) r);
      destruct (DEX_Registers.get (snd (snd s2)) r); auto.
      apply Value_in_sym; auto.
    Qed.

    Definition indist_reg := DEX_Framework.indist_reg Reg 
      istate registertypes pbij high_reg indist_reg_val.

    Definition indist_regs := DEX_Framework.indist_regs Reg
      istate registertypes pbij high_reg indist_reg_val.

    Lemma indist_from_regs_heap : forall sgn rt1 rt2 s1 s2 b1 b2, 
(*       (forall r, indist_reg rt1 rt2 s1 s2 b1 b2 r) ->  *)
      indist_regs rt1 rt2 s1 s2 b1 b2 ->
      indist_heap s1 s2 b1 b2 ->
      indist sgn rt1 rt2 b1 b2 s1 s2.
    Proof.
      intros.
      destruct s1 as [pc1 [h1 r1]].
      destruct s2 as [pc2 [h2 r2]].
      constructor.
      constructor; auto.
      constructor.
      constructor.
        apply RT_domain_length_same.
        split; eapply RT_domain_same; eauto.
      intros.
      inversion H.
      specialize H1 with rn. 
      inversion_mine H1.
      unfold high_reg in *. 
      destruct (MapList.get rt1 rn) eqn:Hget1; destruct (MapList.get rt2 rn) eqn:Hget2; try (contradiction).
      constructor 1 with (k:=t) (k':=t0); auto. 
      constructor 2. subst. 
      unfold indist_reg_val in H8.
      simpl in H8. (* unfold indist_reg_val in H1; simpl in H1. *)
      destruct (DEX_Registers.get r1 rn); 
        destruct (DEX_Registers.get r2 rn); subst; try contradiction.
      constructor; auto. constructor.
      inversion H0; auto.
    Qed.

    Lemma indist_reg_from_indist : forall sgn rt1 rt2 s1 s2 b1 b2,
      indist sgn rt1 rt2 b1 b2 s1 s2 -> 
      forall r, 
        (high_reg rt1 r -> high_reg rt2 r -> indist_reg rt1 rt2 s1 s2 b1 b2 r) /\ 
        ((~high_reg rt1 r /\ ~high_reg rt2 r) \/
          (high_reg rt1 r /\ ~high_reg rt2 r) \/
          (~high_reg rt1 r /\ high_reg rt2 r) ->
        indist_reg_val s1 s2 b1 b2 r).
    Proof.
      intros sgn rt1 rt2 b1 b2 s1 s2 Hindist r.
      inversion Hindist as [sgn0 rt3 rt4 b0 b3 r1 r2 h1 h2 pc1 pc2 Hstin]; clear Hindist; subst.
      inversion Hstin as [pc0 pc' h h' r0 r' HRegsIn HHpIn]; clear Hstin; subst.
      inversion HRegsIn as [Heqset HRegIn].
      specialize HRegIn with (rn:=r).
      inversion HRegIn as [k k' Hget1 Hget2 Hnleq Hnleq' | HValInOpt].
      split; intros.
      constructor; auto. (* *)
      inversion H as [HnHigh1 | HnHigh2_3]; clear H.
      inversion HnHigh1 as [HnHigh_1 HnHigh_2]; clear HnHigh1.
      unfold high_reg in HnHigh_1, HnHigh_2.
      rewrite Hget1 in HnHigh_1; rewrite Hget2 in HnHigh_2. contradiction.
      inversion HnHigh2_3 as [HnHigh2 | HnHigh3]; clear HnHigh2_3.
      inversion HnHigh2 as [HHigh1 HnHigh_2]; clear HnHigh2.
      unfold high_reg in HHigh1, HnHigh_2.
      rewrite Hget1 in HHigh1; rewrite Hget2 in HnHigh_2. contradiction.
      inversion HnHigh3 as [HnHigh_1 HHigh2]; clear HnHigh3.
      unfold high_reg in HnHigh_1, HHigh2.
      rewrite Hget1 in HnHigh_1; rewrite Hget2 in HHigh2. contradiction.
      split; intros. constructor; auto.
      unfold indist_reg_val. simpl.
      destruct (DEX_Registers.get r1 r); destruct (DEX_Registers.get r2 r); subst; auto.
      inversion HValInOpt as [v v' HValIn | ]; auto.
      inversion HValInOpt. inversion HValInOpt.
    Qed.

    Definition high_result := high_result kobs.

    Lemma tevalsto_high_result : forall m sgn (H:PM p m) s res,
      ~L.leql (se m sgn (pc s)) kobs ->
      exec m s (inr res) ->
      texec m H sgn (se m sgn) (pc s) (RT m sgn (pc s)) None -> high_result sgn res.
    Proof.
      intros m sgn H s res Hnleq Hexec Htexec.
      inversion Htexec as [x Htexec']; clear Htexec.
      inversion Hexec as [| m0 s0 ret Hexec']; clear Hexec; subst.
      destruct Htexec' as [Htexec Hins].
      inversion Hexec' as [h s0 ov HReturnStep]; subst.
      inversion HReturnStep as [h0 m0 pc0 regs Hins' Hsig
        | h0 m0 pc0 regs val t k rs Hins' Hinreg Hsig Hassign_compat Hcompat Hget]; subst.
      inversion Htexec. constructor 1. auto.
      subst. simpl in Hins. rewrite Hins in Hins'. inversion Hins'.
      inversion Htexec. subst. simpl in Hins. rewrite Hins in Hins'. inversion Hins'.
      constructor 2 with (k:=kv); auto.
      simpl in H3, Hnleq.
      apply leql_join_each in H3. Cleanexand.
      apply not_leql_trans with (k1:=se m sgn pc0); auto.
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

    Lemma high_result_indist : forall sgn pc h r res pc0 h0 r0 res0 b b0,
      indist_heap (pc, (h,r)) (pc0, (h0,r0)) b b0 ->
(*       hp_in kobs (DEX_ft p) b b0 h h0 -> *)
      high_result sgn (h,res) -> high_result sgn (h0,res0) -> 
        rindist sgn b b0 (h,res) (h0,res0).
    Proof.
      intros.
      constructor; auto.
      destruct sgn. destruct DEX_resType eqn:Hres.
      destruct res. destruct res0.
      destruct o. destruct o0.
      constructor 1 with (k:=t); auto.
      intros. inversion H1. simpl in H5. inversion H5. subst. contradiction.
      inversion H1. simpl in H3. inversion H3.
      destruct o0.
      inversion H0. simpl in H3. inversion H3.
      inversion H1. simpl in H3. inversion H3.
      inversion H0. inversion H1. subst. constructor 2; auto.
      simpl in H7; inversion H7.
      simpl in H4; inversion H4.
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
      | ibinopConst_change : forall op rs v, instructionAt m (pc i) = Some (DEX_IbinopConst op r rs v) -> changed_at m i r
      | iget_change : forall t ro f, instructionAt m (pc i) = Some (DEX_Iget t r ro f) -> changed_at m i r
      | new_change : forall c, instructionAt m (pc i) = Some (DEX_New r c) -> changed_at m i r.

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
        | Some (DEX_Iget _ r' _ _) => Reg_eq r r'
        | Some (DEX_New r' _) => Reg_eq r r'
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
      constructor 9 with (t:=t) (ro:=ro) (f:=f); subst; auto.
      constructor 10 with (c:=c); subst; auto. 
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

    Definition same_val (i j: istate) (r:Reg) : Prop :=
        match DEX_Registers.get (snd (snd i)) r, DEX_Registers.get (snd (snd j)) r with
          | Some v, Some v' => v = v'
          | None, None => True
          | _, _ => False
        end.

    Lemma same_val_indist1: forall s1 s2 s1' b1 b2 r,
      indist_reg_val s1 s2 b1 b2 r ->
      same_val s1 s1' r ->
      indist_reg_val s1' s2 b1 b2 r.
    Proof.
      intros s1 s2 s1' b1 b2 r Hindist Hsame.
      unfold indist_reg_val in *. unfold same_val in *.
      destruct (DEX_Registers.get (snd (snd s1))); destruct (DEX_Registers.get (snd (snd s2))); 
      destruct (DEX_Registers.get (snd (snd s1'))); auto.
      rewrite <- Hsame; auto.
      contradiction.
    Qed.

    Lemma same_val_indist2: forall s1 s2 s1' s2' b1 b2 r,
      indist_reg_val s1 s2 b1 b2 r ->
      same_val s1 s1' r -> same_val s2 s2' r ->
      indist_reg_val s1' s2' b1 b2 r.
    Proof.
      intros s1 s2 s1' s2' b1 b2 r Hindist Hsame1 Hsame2.
      apply same_val_indist1 with (s1:=s1); auto.
      apply indist_reg_val_sym. apply same_val_indist1 with (s1:=s2); auto.
      apply indist_reg_val_sym; auto.
    Qed.

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
      destruct (MapList.get (RT m sgn (pc j)) r) eqn:Hval);
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (pc j)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end).
      (* Const *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (se m sgn (pc i))) r = Some k) as Hget. 
      exists (se m sgn (pc i)). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
      (* Move *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) k_rs)) r = Some k) as Hget. 
      exists ((L.join (se m sgn (pc i)) k_rs)). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
      apply leql_join_each in Hleql; destruct Hleql; auto.
      (* Ineg *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* Inot *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.  
      (* I2b *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* I2s *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (se m sgn (pc i)) ks)) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) ks). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* Ibinop *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join (L.join ka kb) (se m sgn (pc i)))) r = Some k) as Hget. 
      exists (L.join (L.join ka kb) (se m sgn (pc i))). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* IbinopConst *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (L.join ks (se m sgn (pc i)))) r = Some k) as Hget. 
      exists (L.join ks (se m sgn (pc i))). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=se m sgn (pc i)); auto.
      apply leql_join_each in Hleql. Cleanexand; auto.
      (* Iget *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r 
        (L.join (se m sgn (pc i)) (L.join ko (DEX_ft p f)))) r = Some k) as Hget. 
      exists (L.join (se m sgn (pc i)) (L.join ko (DEX_ft p f))). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t0). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t0) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
      apply leql_join_each in Hleql; destruct Hleql; auto.
      (* New *)
      assert (exists k, MapList.get (MapList.update (RT m sgn (pc i)) r (se m sgn (pc i))) r = Some k) as Hget. 
      exists (se m sgn (pc i)). rewrite MapList.get_update1; auto.
      destruct Hget as [lvl Hget]. specialize Hsub_forall with (k1:=lvl) (k2:=t). rewrite Hget in Hsub_forall.
      assert (L.leql lvl t) as Hleql; auto.
      rewrite MapList.get_update1 in Hget. inversion_mine Hget.
      apply not_leql_trans with (k1:=(se m sgn (pc i))); auto.
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
      destruct (MapList.get (RT m sgn pc0) r) eqn:Hrt0.

    Lemma not_changed_same_onestep : forall m sgn i j r (HPM: P (SM _ _ m sgn)),
      ~changed_at m i r -> 
      exec m i (inl j) ->
      (same_val i j r)
      (*indist_reg_val i j r*) /\ (high_reg (RT m sgn (pc i)) r -> high_reg (RT m sgn (pc j)) r). 
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
      unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* move *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Move k rt rs).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Return *)
      inversion Hexec. inversion H2. inversion_mine H3; clear_other_ins (DEX_Return).
      (* VReturn *)
      inversion Hexec. inversion H2. inversion_mine H3; clear_other_ins (DEX_VReturn k rt).
      (* Const *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Const k rt v).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* goto *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Goto o).
      split.
      unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (MapList.get (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* PackedSwitch *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_PackedSwitch rt firstKey size l).
      (* the case where the successor is the next instruction *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (MapList.get (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the targets *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* SparseSwitch *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_SparseSwitch rt size l).
      (* the case where the successor is the next instruction *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (MapList.get (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the targets *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get l0 r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ifeq *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ifcmp cmp ra rb o).
      (* the case where the successor is the target *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (MapList.get (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the next instruction *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.  
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ifz *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ifz cmp r0 o).
      (* the case where the successor is the target *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 (DEX_OFFSET.jump pc0 o) H r.
      destruct (MapList.get (RT m sgn (DEX_OFFSET.jump pc0 o)) r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn (DEX_OFFSET.jump pc0 o)) in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* the case where the successor is the next instruction *)
      split. unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* Ineg *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ineg rt rs).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction. 
      (* Inot *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Inot rt rs).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* I2b *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_I2b rt rs).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.  
      (* I2s *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_I2s rt rs).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.  
      (* Ibinop *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Ibinop op rt ra rb).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* IbinopConst *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_IbinopConst op rt r0 v).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction. 
      (* Iget *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Iget t rt ro f).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t0) (k2:=t1) in Hsub; auto.
      apply not_leql_trans with (k1:=t0); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). contradiction.
      (* Iput *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_Iput t rs ro f).
      split.
      unfold same_val. simpl. destruct (DEX_Registers.get regs r); auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t0) (k2:=t1) in Hsub; auto.
      apply not_leql_trans with (k1:=t0); auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
      end). 
      contradiction.
      (* New *)
      inversion Hexec. inversion_mine H2. inversion_mine H3; clear_other_ins (DEX_New rt c).
      split.
      unfold same_val. simpl. rewrite DEX_Registers.get_update_old. destruct (DEX_Registers.get regs r); auto.
      unfold Reg_eq in Hchanged_at; generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      (* the case where the registers is high *)
      not_changed_same_onestep_aux1 m sgn HPM Hexec pc0 pc' H r.
      destruct (MapList.get (RT m sgn pc') r) eqn:Hrt'.
      apply sub_forall with (r:=r) (k1:=t) (k2:=t0) in Hsub; auto.
      apply not_leql_trans with (k1:=t); auto.
      split; auto. rewrite MapList.get_update2; auto.
      unfold Reg_eq in Hchanged_at. generalize (Neq_spec r rt); rewrite Hchanged_at; auto.
      assert (MapList.get (RT m sgn pc0) r <> None) as Hget.
      destruct (MapList.get (RT m sgn pc0) r). congruence.
      inversion Hrt0. apply MapList.get_some_in_dom in Hget.
      try (  match goal with
      | [ H:In r ?dom |- False] => apply RT_domain_same with (rt2:=RT m sgn pc') in H; 
        apply MapList.in_dom_get_some in H; contradiction
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
      (same_val i j r)
      (*indist_reg_val i j r*) /\ (high_reg (RT m sgn (pc i)) r -> high_reg (RT m sgn (pc j)) r). 
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
      unfold same_val in *.
      destruct (DEX_Registers.get (snd (snd i)) r);
      destruct (DEX_Registers.get (snd (snd k)) r);
      destruct (DEX_Registers.get (snd (snd j)) r); try (congruence); try (contradiction). 
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

    Lemma indist2_intra_aux : forall se m sgn i s s' rt rt' b b' (H:P (SM _ _ m sgn)),
      DEX_BigStepWithTypes.NormalStep kobs p se
       (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i
       s rt b s' rt' b' -> border b b'.
    Proof.
      intros se0 m sgn i s s' rt rt' b b' H Hstep.
      destruct i eqn:Hins; try 
        (inversion Hstep; subst; apply border_refl; fail).
      inversion Hstep; subst. unfold DEX_BigStepWithTypes.newb.
      destruct (L.leql_dec (se0 pc0) kobs).
      apply border_extends. apply border_refl.
    Qed.

    Lemma indist2_intra : forall m sgn se rt ut ut' s s' u u' b b',
      forall H0:P (SM _ _ m sgn),
        indist sgn rt rt b b' s s' ->
        pc s = pc s' ->
        exec m s (inl _ u) ->
        exec m s' (inl _ u') ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
        exists bu, exists bu',
          border b bu /\ border b' bu' /\
          indist sgn ut ut' bu bu' u u'.
    Proof.
      unfold pc; intros m sgn se0 rt ut ut' s s' u u' b b' H Hindist Hpc Hexec Hexec' Htexec Htexec'.
      inversion_mine Hexec. inversion_mine Hexec'.
  
      elim DEX_BigStepWithTypes.exec_intra_instructionAt with (1:=H3); intros i Hi.
      destruct Htexec as [i' [Ti Ti']]; DiscrimateEq.
      
      assert (exists bu, DEX_BigStepWithTypes.NormalStep kobs p se0 
        (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i s rt b u ut bu).
        elim well_types_imply_exec_intra with (kobs:=kobs) (b1:=b) (1:=H3) (3:=Ti); auto.
        intros bu Hassert. exists bu. inversion Hassert.
        inversion H0. eauto.
      destruct Htexec' as [i' [Ui Ui']]; DiscrimateEq.
      rewrite Hpc in Ui.
      assert (exists bu', DEX_BigStepWithTypes.NormalStep kobs p se0 
        (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i s' rt b' u' ut' bu').
        elim well_types_imply_exec_intra with (kobs:=kobs) (b1:=b') (1:=H4) (3:=Ui).
        intros bu' Hassert. exists bu'. inversion Hassert.
        inversion H1; eauto.
      rewrite Hpc in Ui'; auto. 
      inversion_mine Hindist.
      destruct u as [pu [hu ru]].
      destruct u' as [pu' [hu' ru']].
      destruct H1 as [bu' H1]. destruct H0 as [bu H0].
      exists bu. exists bu'. split. 
      apply indist2_intra_aux with (se:=se0) (m:=m) (sgn:=sgn) (i:=i) 
        (s:=(pc1, (h1, r1))) (s':=(pu, (hu, ru))) (rt:=rt) (rt':=ut) 
        (H:=H); auto.
      split. 
      apply indist2_intra_aux with (se:=se0) (m:=m) (sgn:=sgn) (i:=i) 
        (s:=(pc2, (h2, r2))) (s':=(pu', (hu', ru'))) (rt:=rt) (rt':=ut') 
        (H:=H); auto.
      constructor.
      eapply indist2_intra; eauto. 
      constructor; eauto.
      rewrite Hpc; constructor; eauto.
      simpl. simpl in Hpc.
      rewrite <- Hpc in H2; auto.
    Qed.
    
    Lemma tcc3 : forall m rt1 rt2 s1 s2 b1 b2,
      indist m rt1 rt2 b1 b2 s1 s2 -> indist m rt2 rt1 b2 b1 s2 s1.
    Proof.
      intros.
      inversion_clear H; constructor.
      apply st_in_sym; auto.
    Qed.

    Lemma indist_return_value_sym : forall sgn hu hu' vu' vu bu' bu,
      indist_return_value kobs hu' hu sgn vu' vu bu' bu ->
      indist_return_value kobs hu hu' sgn vu vu' bu bu'.
    Proof.
      intros.
      inversion_clear H.
      constructor 1 with k; auto; intros.
      apply Value_in_sym; auto.
      constructor; auto.
    Qed.

    Lemma rindist_sym : forall sgn r1 r2 b1 b2,
      rindist sgn b1 b2 r1 r2 -> rindist sgn b2 b1 r2 r1.
    Proof.
      intros sgn r1 r2 b1 b2 Hindist.
      destruct r1 as [h1 res1]; destruct r2 as [h2 res2].
      constructor; inversion Hindist; auto. apply hp_in_sym; auto.
      apply indist_return_value_sym; auto.
    Qed.

    Definition border : pbij -> pbij -> Prop := beta_pre_order.

    Lemma tcc8 : forall b1 b2 b3 : pbij, border b1 b2 -> border b2 b3 -> border b1 b3.
    Proof.
      unfold border, beta_pre_order; intros.
      firstorder.
    Qed.

    Lemma indist2_return : forall (m : Method) (sgn : Sign) (se : PC -> L.t) 
      (rt : registertypes) (s s' : istate) (u u' : rstate) (b b' : pbij),
      forall H:P (SM Method Sign m sgn),
        indist sgn rt rt b b' s s' ->
        pc s = pc s' ->
        exec m s (inr istate u) ->
        exec m s' (inr istate u') ->
        texec m (PM_P _ H) sgn se (pc s) rt None ->
        texec m (PM_P _ H) sgn se (pc s) rt None ->
        exists bu, exists bu',
          border b bu /\ border b' bu' /\
          rindist sgn bu bu' u u'.
    Proof.
      unfold pc; intros m sgn se0 rt s s' u u' b b' H Hindist Hpc Hexec Hexec' Htexec Htexec'.
      destruct Htexec as [i' [Ti Ti']].
      destruct Htexec' as [i [Ui Ui']]; DiscrimateEq.
      destruct s as [pp [h regs]].
      destruct s' as [pp' [h' regs']].
      simpl in Hpc; subst; simpl in *.
      destruct u as [hu vu].
      destruct u' as [hu' vu'].
      inversion_mine Hindist;
      inversion_mine Hexec; inversion_mine Hexec'.
  (**)
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i 
          (pp', (h, regs)) rt (hu, vu)).
        elim well_types_imply_exec_return with (1:=H3) (3:=Ti) (b1:=b); auto.
        intros bu Hassert. inversion Hassert. inversion H0; auto.
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i 
          (pp', (h', regs')) rt (hu', vu')).
        elim well_types_imply_exec_return with (1:=H4) (3:=Ui) (b1:=b'); auto.
        intros bu' Hassert. inversion Hassert. inversion H1; auto.
      exists b. exists b'. split. apply border_refl.
      split. apply border_refl. destruct vu; destruct vu'. 
      apply DEX_BigStepWithTypes.exec_return_normal with (b:=b) in H0; auto.
      apply DEX_BigStepWithTypes.exec_return_normal with (b:=b') in H1; auto.
      apply indist2_return with (1:=H0) (2:=H1) in H6. inversion H6. 
      constructor; auto.  
    Qed.

    Section well_formed_lookupswitch.

      Variable hyp : forall m sgn, P (SM _ _ m sgn) -> well_formed_lookupswitch m.

      Lemma soap2_basic_intra : forall m sgn se rt ut ut' s s' u u' b b',
        forall H0:P (SM _ _ m sgn),
          indist sgn rt rt b b' s s' -> 
          pc s = pc s' ->
          exec m s (inl _ u) ->
          exec m s' (inl _ u') -> 
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
          texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
          pc u <> pc u' -> 
          forall j:PC, region (cdr m (PM_P _ H0)) (pc s) j -> ~ L.leql (se j) kobs.
      Proof.
        intros m sgn se0 rt ut ut' s s' u u' b b' H0 Hindist Hpcs Hexec Hexec' Htexec Htexec' Hpcu.
        intros j Hreg.
        destruct Htexec as [i' [Ti Ui]].
        destruct Htexec' as [i [Ti' Ui']]. DiscrimateEq.
        inversion_mine Hindist.
        destruct u as [ppu [h regs]].
        destruct u' as [ppu' [h' regs']].
        inversion_mine Hexec'; inversion_mine Hexec; simpl in *; subst.
  (**)
        assert (exists bu, DEX_BigStepWithTypes.NormalStep kobs p se0 
          (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,(h1,r1)) rt b (ppu,(h,regs)) ut bu).
             elim well_types_imply_exec_intra with (1:=H5) (3:=Ti) (kobs:=kobs) (b1:=b); auto.
             intros bu Hassert; inversion Hassert. inversion H1. exists bu. auto.
        assert (exists bu', DEX_BigStepWithTypes.NormalStep kobs p se0 
          (region (cdr m (PM_P {| unSign := m; sign := sgn |} H0))) 
          m sgn i (pc2,(h2,r2)) rt b' (ppu',(h',regs')) ut' bu').
             elim well_types_imply_exec_intra with (1:=H4) (3:=Ti') (kobs:=kobs) (b1:=b'); auto.
             intros bu' Hassert; inversion Hassert. inversion H2. exists bu'; auto.
        destruct H1 as [bu H1]; destruct H2 as [bu' H2].
        apply DEX_BigStepWithTypes.exec_intra_normal in H1;
        apply DEX_BigStepWithTypes.exec_intra_normal in H2.
        apply soap2_intra with (4:=H2) (3:=H1) (6:= H); auto.
        specialize hyp with (m:=m) (sgn:=sgn) (1:=H0); auto.
      Qed.
    End well_formed_lookupswitch.

    Lemma Regs_in_sub_simple : forall rt rt0 s s0 b b0,
      Regs_in kobs s0 s b0 b rt0 rt -> forall rt',
        sub rt rt' -> 
        Regs_in kobs s0 s b0 b rt0 rt'.
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
        apply MapList.get_some_in_dom in H9. rewrite H3 in H9.
        apply MapList.in_dom_get_some in H9.
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

    Lemma sub_simple : forall sgn rt rt' rt0 s s0 b b0,
      indist sgn rt0 rt b0 b s0 s ->
      sub rt rt' ->
      indist sgn rt0 rt' b0 b s0 s.
    Proof.
      intros.
      inversion_mine H; inversion_mine H1; constructor.
      constructor; auto. eapply Regs_in_sub_simple; eauto.
    Qed.

    Lemma branch_indist : forall m sgn s s' u u' b b' (H0:P (SM _ _ m sgn)), 
      pc s = pc s' ->
      indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) b b' s s' ->
      exec m s (inl u) ->
      exec m s' (inl u') ->
      pc u <> pc u' ->
      exists bu, exists bu',
        border b bu /\ border b' bu' /\
        indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) bu bu' u u'.
    Proof.
      intros m sgn s s' u u' b b' HPM Hpc Hindist Hexec Hexec' Hpc'.
      rewrite <- Hpc in Hindist.
      destruct (typable_hyp m sgn HPM) as [T1 [T2 T3]].
      assert (e:=Hexec). apply tcc0 with (1:=PM_P _ HPM) in e.
      assert (e':=Hexec'). apply tcc0 with (1:=PM_P _ HPM) in e'.
      assert (T3':=T3).
      specialize T3 with (i:=pc s) (j:=pc u) (1:=e).
        destruct T3 as [ut [Htexec Hsub]].
      specialize T3' with (i:=pc s') (j:=pc u') (1:=e').
        destruct T3' as [ut' [Htexec' Hsub']].
      elim indist2_intra with (m:=m) (se:=se m sgn) (rt:=(RT m sgn (pc s))) 
        (s:=s) (s':=s') (H0:=HPM) (ut:=ut) (ut':=ut') (b:=b) (b':=b') (u:=u) (u':=u'); auto.
      intros bu [bu' [Hborder1 [Hborder2 Hindist']]].
      exists bu. exists bu'. repeat (split); auto.      
      apply sub_simple with (2:=Hsub'). apply tcc3.
      apply sub_simple with (2:=Hsub). apply tcc3.
      auto.
      rewrite Hpc; auto.
    Qed.

    Lemma high_path_heap_indist_onestep_left : forall m sgn s i i' b b' j (H: P (SM _ _ m sgn)),
      (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) kobs) ->
      region (cdr m (PM_P _ H)) s (pc i) ->
      exec m i (inl j) ->
      indist_heap i i' b b' ->
        indist_heap j i' b b'.
    Proof.
      intros m sgn s i i' b b' j H k Hreg Hexec Hindist.
      inversion Hexec. inversion_mine H3. destruct i' as [pc' [h' r']].
      inversion_mine H4; try (constructor; inversion Hindist; auto).
      subst. apply ffun_extends_hp_in_new_left with (c:=c) (h:=h) (loc:=loc); auto.
      subst. apply hp_in_putfield_high_update_left with (cn:=cn); auto.
      destruct (typable_hyp _ _ H) as [T1 [T2 T3]].
      specialize T3 with (i:=pc0) (j:=pc'0). elim T3.
      intros rt [Htexec Hsub].
      inversion Htexec. 
      assert (x=(DEX_Iput k0 rs ro f)).
        inversion H4. rewrite H0 in H11. inversion H11; auto.
      subst. inversion H4. inversion_mine H10.
      apply not_leql_trans with (k1:=(se m sgn pc0)); auto.
      apply tcc0 with (s:=(pc0, (h, regs))) (s':=(pc'0,
             (DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) v, regs))) (1:=PM_P _ H); auto.
    Qed.

    Lemma high_path_heap_indist_onestep_right : forall m sgn s i i' b b' j (H: P (SM _ _ m sgn)),
      (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) kobs) ->
      region (cdr m (PM_P _ H)) s (pc i') ->
      exec m i' (inl j) ->
      indist_heap i i' b b' ->
        indist_heap i j b b'.
    Proof.
      intros.
      apply indist_heap_sym. 
      apply high_path_heap_indist_onestep_left with (m:=m) (sgn:=sgn) (s:=s) (i:=i') (H:=H); auto.
      auto. apply indist_heap_sym; auto.
    Qed.

    Lemma high_path_heap_indist : forall m sgn s i i' b b' j (H:P (SM _ _ m sgn)) (Hpath: path m i j), 
      (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) kobs) ->
      path_in_region m (cdr m (PM_P _ H)) s i j Hpath ->
      region (cdr m (PM_P _ H)) s (pc i) ->
      junc (cdr m (PM_P _ H)) s (pc j) ->
      indist_heap i i' b b' ->
        indist_heap j i' b b'.
    Proof.
      intros.
      induction Hpath.
      (* base case *)
      inversion_mine H4. 
      apply high_path_heap_indist_onestep_left with (s:=s) (H:=H) (i:=(pc1, (h1, r1))); auto.
      constructor; auto.

      (* induction case *)
      apply IHHpath; auto. inversion H1.
      assert ((existT (fun k : istate => path m k j) k p1) = (existT (fun k : istate => path m k j) k Hpath)).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H6); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      assert (p1 = Hpath).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H9); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      subst; auto.
      (* region *)
      inversion H1.
      assert ((existT (fun k : istate => path m k j) k p1) = (existT (fun k : istate => path m k j) k Hpath)).
      apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec with (2:=H6); auto.
      intros x y; apply excluded_middleT with (P:=x=y).
      inversion H8; auto.
      (* indist_heap *)
      apply high_path_heap_indist_onestep_left with (s:=s) (H:=H) (i:=i); auto.
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
  Variable RT :  DEX_Method -> DEX_sign -> PC -> MapList.t L.t.
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
          match MapList.get rt h with
          | None => false
          | Some k => (L.eq_t k (DEX_lvt sgn h))
          end
        else
          match MapList.get rt h with
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
                     eq_set_test (MapList.dom rt) (DEX_BYTECODEMETHOD.regs bm) &&
                     check_rt0_rec rt sgn (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level)
    end.

  Lemma check_rt0_rec_true : forall m sgn bm default_level,
    check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn 
      (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) default_level = true ->
    DEX_METHOD.body m = Some bm -> 
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)).
  Proof.
    intros. 
    split; intros.
    (* case where the register is in the domain *)
      induction (DEX_BYTECODEMETHOD.regs bm). inversion H1.
      unfold check_rt0_rec in H. 
      assert ((if In_test a (DEX_BYTECODEMETHOD.locR bm) then
      match MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k (DEX_lvt sgn a) 
      | None => false
      end
     else
      match MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
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
      destruct (MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a). 
      flatten_bool. apply IHl; subst; auto.
      inversion H4. 
      destruct (MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a). 
      flatten_bool; apply IHl; subst; auto.
      inversion H4. 
    (* case where the register is not in the domain *)
    induction (DEX_BYTECODEMETHOD.regs bm). inversion H1.
    assert ((if In_test a (DEX_BYTECODEMETHOD.locR bm)
     then
      match MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k (DEX_lvt sgn a) 
      | None => false
      end
     else
      match MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) a with
      | Some k =>
          L.eq_t k default_level0
      | None => false
      end) &&
      check_rt0_rec (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) sgn (DEX_BYTECODEMETHOD.locR bm) l default_level0 = true). auto.
    clear H.
    inversion H1.
    apply not_In_In_test in H2.
    rewrite <- H in H2; rewrite H2 in H3. subst.
    destruct (MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r).
    flatten_bool; auto.
    generalize (L.eq_t_spec t default_level0); intros Heq; rewrite H in Heq; rewrite Heq; auto.
    inversion H3.
    (* induction case *)
    flatten_bool. apply IHl; subst; auto.
  Qed.

  Lemma check_rt0_true : forall m sgn bm, check_rt0 m sgn = true ->
    DEX_METHOD.body m = Some bm ->
    (forall r, In r (DEX_BYTECODEMETHOD.regs bm) ->
    (forall k, In r (DEX_BYTECODEMETHOD.locR bm) -> Some k = MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r -> k = (DEX_lvt sgn r)) /\
    (~In r (DEX_BYTECODEMETHOD.locR bm) -> Some (default_level) = MapList.get (RT m sgn (DEX_BYTECODEMETHOD.firstAddress bm)) r)).
  Proof.
    intros. unfold check_rt0 in H.
    rewrite H0 in H. flatten_bool. apply check_rt0_rec_true; auto.  
  Qed.

  Definition check : bool := for_all_P p
    (fun m sgn =>
      (check_rt0 m sgn) &&
      for_all_steps_m m
      (fun i ins oj => 
        DEX_tcheck p m sgn (se m sgn) (selift m sgn) (RT m sgn) i ins)
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
    (* *)
    rewrite make_rt_from_lvt_prop3 in H2. contradiction.
    apply DEX_BYTECODEMETHOD.noDup_regs.
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
    assert (MapList.get rt2 r <> None). unfold not; intros. 
      rewrite H4 in H3; inversion H3.
    apply MapList.get_some_in_dom in H4; auto.
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
    elim (tcheck_correct2 p m sgn (region (cdr_local _ (PM_P _ _ h)))  (se m sgn)
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
    forall m sgn i h1 h2 r1 r2 hr1 hr2 res1 res2 b1 b2,
      P p (SM _ _ m sgn) ->
      init_pc m i -> 
      indist kobs p sgn (rt0 m sgn) (rt0 m sgn) b1 b2 (i, (h1,r1)) (i, (h2,r2)) ->
      evalsto p m (i,(h1,r1)) (hr1,res1) -> 
      evalsto p m (i,(h2,r2)) (hr2,res2) -> 
      exists br1, exists br2,
        border b1 br1 /\ border b2 br2 /\
        hp_in kobs (DEX_ft p) br1 br2 hr1 hr2 /\
        indist_return_value kobs hr1 hr2 sgn res1 res2 br1 br2.
Proof.
  intros kobs p cdr [se [RT HT]] Hwfl m sgn i h1 h2 r1 r2 hr1 hr2 res1 res2 
    b1 b2 H Hinit Hindist Hevalsto1 Hevalsto2.
  assert (Hni:=safe_ni kobs PC Method (step p) (PM p) cdr Reg Sign istate rstate (exec p) pc 
    (tcc0 p) (tcc1 p) registertypes pbij (texec p cdr) (high_reg kobs)
    (indist_reg_val) (same_val) (same_val_indist2) (same_val_indist1)
    (indist kobs p) (indist_heap kobs p) (indist_heap_sym kobs p) 
    (indist_from_regs_heap kobs p) (indist_reg_from_indist kobs p)
    (indist_heap_from_indist kobs p) (rindist kobs p) 
    (tcc3 kobs p) (rindist_sym kobs p) (high_result kobs) (rt0) (init_pc)
    (border) (border_refl) (border_trans p)
    (P p) (PM_P p) (indist2_intra kobs p cdr) (indist2_return kobs p cdr)
    (soap2_basic_intra kobs p cdr Hwfl) (sub) (sub_simple kobs p)
    (tevalsto_high_result kobs p cdr) (tevalsto_diff_high_result' kobs p cdr ) (high_result_indist kobs p)
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
      (RT :  Method -> DEX_sign -> PC -> MapList.t L.t),
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

Definition RT_empty := MapN.empty (MapList.t L.t).
Definition RT_add (i:PC) (rt:MapList.t L.t) RT := MapN.update _ RT i rt.

Definition m_RT_empty := DEX_MapShortMethSign.empty (MapN.t (MapList.t L.t)).
Definition m_RT_add (m:Method) (RT:MapN.t (MapList.t L.t)) m_RT :=
  DEX_MapShortMethSign.update _ m_RT m.(DEX_METHOD.signature) RT.
Definition RT_get RT : PC -> (MapList.t L.t) := fun i =>
  match MapN.get _ RT i with
    | None => MapList.empty L.t
    | Some rt => rt
  end.
Definition m_RT_get map : Method -> DEX_sign -> PC -> (MapList.t L.t) :=
  fun m sgn => match DEX_MapShortMethSign.get _ map m.(DEX_METHOD.signature) with
                 | None => fun _ => MapList.empty L.t
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