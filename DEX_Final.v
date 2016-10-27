Require Export DEX_Framework.
Require Export DEX_ProofBigStepWithType.
Require Export DEX_ElemLemmas.
Require Export DEX_ElemLemmaIntra.
Require Export DEX_ElemLemmaReturn.
(* Require Export ElemLemmaCall1.
Require Export ElemLemmaSideEffect. *)
(* Require DEX_compat.  *)
Require Export DEX_step.
Require Export DEX_typing_rules.

Import DEX_BigStepWithTypes DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Definition ValidMethod (p:DEX_Program) (m:DEX_Method) : Prop :=
  exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

Definition step (p:DEX_Program) (* subclass_test *) : DEX_Method -> DEX_PC (* -> option DEX_ClassName *) -> option DEX_PC -> Prop := 
fun m pc (* tau *) opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ DEX_step (*p subclass_test *) m pc i (* None *) opc.

Variable RT_domain_same : forall rt1 rt2 r, In r (VarMap.dom L.t rt1) -> In r (VarMap.dom L.t rt2).
Variable valid_regs_prop : forall m bm r rt, DEX_METHOD.body m = Some bm -> 
    ~ In r (DEX_BYTECODEMETHOD.regs bm) -> VarMap.get L.t rt r = None.
Variable RT_domain_length_same : forall rt1 rt2, length (VarMap.dom L.t rt1) = length (VarMap.dom L.t rt2). 

Section hyps.
  Variable kobs: L.t.
  Variable p : DEX_ExtendedProgram.
  (* Variable subclass_test : ClassName -> ClassName -> bool.
  Variable subclass_test_correct : forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2. *)
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

(*   Definition compat : Sign -> istate -> registertypes -> Prop := 
    DEX_compat.compat_state.
  Definition compat_res : Sign -> rstate -> Prop :=
    DEX_compat.compat_res. *)

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
(*   Inductive rt0 (m:Method) (sgn:Sign): registertypes -> Prop := 
    rt0_def : forall bm, 
      DEX_METHOD.body m = Some bm ->
      P (SM _ _ m sgn) ->
      rt0 m sgn (Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level)). *)

  Definition rt0 (m:Method) (sgn:Sign): registertypes := 
  match DEX_METHOD.body m with
  | Some bm => (Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level))
  | None => VarMap.empty L.t
  end.

 (*  Definition rt0 (m:Method) : registertypes := 
    Annotated.make_rt_from_lvt_rec (sgn) (DEX_BYTECODEMETHOD.locR bm) (DEX_BYTECODEMETHOD.regs bm) (default_level). *)


  Definition ni := ni _ _ _ _ _ exec pc registertypes indist rindist (* compat *) rt0 init_pc P.

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

  Lemma evalsto_Tevalsto2 : forall m s r p,
    DEX_Framework.evalsto Method istate rstate exec m p s r ->
    evalsto m s r.
  Proof.
(*     intros m n; pattern n; apply lt_wf_ind; clear n; intros. *)
    intros.
    induction H.
    constructor 1; auto.
    constructor 2 with (s2:=s2); auto.
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

(*   Lemma tcc6 : forall sgn m se s s' rt rt',
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
  Qed. *)

(*   Lemma tcc7 : forall sgn m se s r rt,
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
  Qed. *)

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

(*   Lemma compat_register_sub : forall (rt1 rt2 : registertypes),
    sub rt1 rt2 -> forall r,
      DEX_compat.compat_registers r rt1 ->
      DEX_compat.compat_registers r rt2.
  Proof.
    induction 1; simpl; intuition.
    unfold DEX_compat.compat_registers in H0.
    unfold DEX_compat.compat_registers. 
    intros. destruct v; constructor; auto. 
  Qed. *)

(*   Lemma compat_sub : forall (sgn : Sign) (s : istate) (rt1 rt2 : registertypes),
    sub rt1 rt2 -> compat sgn s rt1 -> compat sgn s rt2.
  Proof.
    intros.
    destruct s.
    apply compat_register_sub with (r:=t) in H; auto.
  Qed. *)

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
(*       apply H2 with (rn:=rn) (v:=v) (v':=v') (k:=k) (k':=k'); auto. *)
(*       rewrite H9; auto. *)
(*       rewrite H; auto. *)
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
(*       apply H2 with (rn:=rn) (v:=v) (v':=v') (k:=k) (k':=k'); auto. *)
(*       rewrite H9; auto. *)
(*       rewrite H; auto. *)
      rewrite eq_rt_get with (rt1:=x) (rt2:=y0); auto. rewrite H3; auto.
      rewrite eq_rt_get with (rt1:=x0) (rt2:=y1); auto. rewrite H; auto. 
      constructor 2. auto.
  Qed.

(*   Lemma compat_morphism_proof : forall (y : Sign) (y0 : istate) (x y1 : registertypes),
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
  Qed. *)

  Definition TypableProg := TypableProg PC Method step (PM p) Sign (* istate pc *) registertypes 
    texec (*indist*) rt0 init_pc P PM_P sub eq_rt.

  Section TypableProg.

    Variable se : Method -> Sign -> PC -> L.t.
    Variable RT : Method -> Sign -> PC -> registertypes.
    Variable typable_hyp : TypableProg se RT.

(* TODO *)

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

(* Inductive indist_reg : registertypes -> registertypes -> istate -> istate -> Reg -> Prop :=
  | high_indist_reg : forall rt1 rt2 s1 s2 r,
      high_reg rt1 r -> high_reg rt2 r -> indist_reg rt1 rt2 s1 s2 r
  | low_indist_reg : forall rt1 rt2 s1 s2 r, indist_reg_val s1 s2 r -> indist_reg rt1 rt2 s1 s2 r. *)

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
  inversion H. (*  Cleanexand.
  inversion H7. subst. *)
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
(*   induction typable_hyp with m sgn H. *)
(*   Cleanexand. *)
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
(*   DEX_resType sgn = Some k -> *)
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

(* Lemma high_reg_dec : forall rt r, In r (VarMap.dom _ rt) -> high_reg rt r \/ ~high_reg rt r.
Proof.
  intros.
  unfold high_reg.
  apply VarMap.in_dom_get_some in H.
  assert (exists k, VarMap.get L.t rt r = Some k). 
    unfold not in H.
    destruct (VarMap.get L.t rt r); auto.
    exists t; auto.
    apply False_ind. auto.
  destruct H0.
  rewrite H0.
  generalize (L.leql_dec x kobs); intros.
  inversion H1; auto.
Qed. *)

Definition path := DEX_Framework.path Method istate rstate exec.

(* Inductive path (m:Method) (i:istate) : istate -> Type :=
  | path_base : forall j, exec m i (inl j) -> path m i j 
  | path_step : forall j k, path m k j -> exec m i (inl k) -> path m i j. *)

(* Inductive path (m:Method) (sgn:Sign) (H:PM _ m) (i:istate) : istate -> Type :=
  | path_base : forall j ort, texec m H sgn (se m sgn) (pc i) (RT m sgn (pc i)) ort -> 
      exec m i (inl j) -> path m sgn H i j
  | path_step : forall j k ort, path m sgn H k j -> exec m i (inl k) -> 
      texec m H sgn (se m sgn) (pc i) (RT m sgn (pc i)) ort -> path m sgn H i j. *)

Definition path_in_region := DEX_Framework.path_in_region PC Method step istate rstate exec pc.
(* Inductive path_in_region (m:Method) (cdr: CDR (step m)) (s:PC) (i j:istate) : (path m i j) -> Prop :=
  | path_in_reg_base : forall (Hexec:exec m i (inl j)), region cdr s (pc i) -> 
      path_in_region m cdr s i j (path_base m i j Hexec)
  | path_in_reg_ind : forall k (Hexec:exec m i (inl k)) (p:path m k j), region cdr s (pc i) ->
      path_in_region m cdr s k j p -> path_in_region m cdr s i j (path_step m i j k p Hexec). *)

Inductive path_prop (m:Method) (i j:istate) : Prop := path_exists : path m i j -> path_prop m i j.
(* Inductive path_prop (m:Method) (sgn:Sign) (H:PM _ m) (i j:istate) : Prop := 
  path_exists : path m sgn H i j -> path_prop m sgn H i j. *)

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

(* Inductive changed (m:Method) (sgn:Sign) (H:PM _ m) (i j: istate) : (path m sgn H i j) -> Reg -> Prop :=
  | changed_onestep : forall r (p:path m sgn H i j), changed_at m i r -> changed m sgn H i j p r
  | changed_path : forall k r ort (p:path m sgn H k j) (Hexec:exec m i (inl k)) 
      (Htexec:texec m H sgn (se m sgn) (pc i) (RT m sgn (pc i)) ort), 
      changed m sgn H k j p r -> changed m sgn H i j (path_step m sgn H i j k ort p Hexec Htexec) r.
 *)
(* Inductive changed : Set -> Reg -> Prop :=
  | changed_onestep : forall m i j r, changed_at m i r -> changed (path m i j) r
(*   | changed_onestep : forall k, step m i (Some k) -> path m k j -> changed_at m i r -> changed m i j r *)
  | changed_path : forall m i j k r, step m i (Some k) -> (* path m k j ->  *)
      changed (path m k j) r -> changed (path m i j) r. *)

Lemma changed_dec : forall m (* sgn (H:PM _ m) *) i j r (*p:path m sgn H i j*) (p:path m i j), (* path_prop m i j -> *)
(*   changed (path m i j) r \/ ~changed (path m i j) r. *)
  changed m (* sgn H *) i j (p) r \/ ~changed m (* sgn H *) i j (p) r. 
Proof.
  intros.
  apply excluded_middle with (P:=changed m i j p0 r). 
Qed.

Lemma changed_high_onestep : forall m sgn s i j r (H: P (SM _ _ m sgn)),
  (forall k:PC, region (cdr m (PM_P _ H)) s (* kd *) k -> ~ L.leql (se m sgn k) kobs) ->
  region (cdr m (PM_P _ H)) s (pc i) ->
  exec m i (inl j) ->
(*   In r (VarMap.dom _ (RT m sgn (pc j))) -> *)
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
(*   In r (VarMap.dom _ (RT m sgn (pc j))) -> *)
  changed m (* sgn (PM_P _ H) *) i j Hpath r -> high_reg (RT m sgn (pc j)) r.
Proof.
  intros.
  induction Hpath.
  (* base case *)
  inversion_mine H4; apply changed_high_onestep with (s:=s) (i:=i) (H:=H); auto.

  (* induction case *)
  (* assert (e':=e); apply tcc0 with (1:=PM_P _ H) in e'.
  elim soap2 with PC (step m) (cdr m (PM_P _ H)) s (pc i) (pc k); auto; intros. *)
  inversion H4.
  (* the case where the change is happening at the current step *)
  generalize changed_high_onestep; intros.
(*   assert (H4':=H4). apply RT_domain_same with (i:=pc j) (j:=pc k) (r:=r) in H4'. *)
  specialize H8 with (m:=m) (sgn:=sgn) (s:=s) (i:=i) (j:=k) (r:=r) (H:=H) (1:=H0) (2:=H2) (3:=e) (* (4:=H4') *) (4:=H5).
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
(* end TODO *)

    Lemma indist2_intra : forall m sgn se rt ut ut' s s' u u',
(*       (forall k, (k<N)%nat -> ni k) -> *)
      forall H0:P (SM _ _ m sgn),
        indist sgn rt rt (* b b' *) s s' ->
        pc s = pc s' ->
        exec m s (inl _ u) ->
        exec m s' (inl _ u') ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
        texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
(*         compat sgn s rt ->
        compat sgn s' rt -> *)
(*         exists bu, exists bu',
          border b bu /\
          border b' bu' /\ *)
          indist sgn ut ut' (* bu bu'  *) u u'.
    Proof.
      unfold pc; intros m sgn se0 rt ut ut' s s' u u' H Hindist Hpc Hexec Hexec' Htexec Htexec'.
      inversion_mine Hexec. inversion_mine Hexec'.
  (**)
      elim DEX_BigStepWithTypes.exec_intra_instructionAt with (1:=H3); intros i Hi.
      destruct Htexec as [i' [Ti Ti']]; DiscrimateEq.
      
(*       elim well_types_imply_exec_intra with (1:=H11) (3:=Ti); auto. *)
      assert (DEX_BigStepWithTypes.NormalStep se0 (region (cdr m (PM_P {| unSign := m; sign := sgn |} H))) m sgn i s rt u ut).
        elim well_types_imply_exec_intra with (1:=H3) (3:=Ti); eauto. 
(*       intros b2 [T1 T2]. *)
      destruct Htexec' as [i' [Ui Ui']]; DiscrimateEq.
      rewrite Hpc in Ui.
(*       elim well_types_imply_exec_intra with (1:=H10) (3:=Ui); auto. *)
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
(*         compat sgn s rt -> *)
(*         compat sgn s' rt -> *)
        (* exists bu : pbij,
          (exists bu' : pbij,
            border b bu /\ border b' bu' /\  *)rindist sgn (* bu bu' *) u u'.
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
      (* elim well_types_imply_exec_return with (1:=H5) (3:=Ti); auto.
      intros. (*  [T1 T2]. *) *)
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs) rt (Normal vu)).
        elim well_types_imply_exec_return with (1:=H3) (3:=Ti); auto.
      assert (DEX_BigStepWithTypes.ReturnStep p se0 m sgn i (pp', regs') rt (Normal vu')).
        elim well_types_imply_exec_return with (1:=H5) (3:=Ui); auto.
      apply DEX_BigStepWithTypes.exec_return_normal in H0.
      apply DEX_BigStepWithTypes.exec_return_normal in H1.
      constructor. 
      apply indist2_return with (1:=H0) (2:=H1) (3:=H4). 
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

(*     Section well_formed_lookupswitch. *)

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
(*           compat sgn s rt -> *)
(*           compat sgn s' rt -> *)
          pc u <> pc u' -> 
(*           high_opstack ut u /\ *)
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
        apply soap2_intra with (4:=H2) (3:=H1) (6:= H); auto.
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
        sub rt rt' -> (* high_opstack st s -> *)
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

(*     End well_formed_lookupswitch. *)

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

(*   Lemma check_correct1 : check = true ->
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
  Qed.   *)

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

(* Section well_formed_lookupswitch.

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

End  well_formed_lookupswitch. *)

Theorem ni_safe : forall (kobs:L.t) (p:DEX_ExtendedProgram) (*subclass_test : ClassName -> ClassName -> bool*),
  (*(forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2) ->*)
  forall cdr : forall m, PM p m -> CDR (step p (* subclass_test *) m),
    (exists se, exists RT, TypableProg p (* subclass_test *) cdr se RT) ->
(*     (forall m sgn, P p (SM _ _ m sgn) -> well_formed_lookupswitch m) -> *)
    forall m sgn i (* rt *) r1 r2 res1 res2,
      P p (SM _ _ m sgn) ->
      init_pc m i -> 
(*       rt0 p m sgn rt -> *)
(*       compat sgn (i,r1) rt -> *)
(*       compat sgn (i,r2) rt -> *)
      indist kobs sgn (rt0 m sgn) (rt0 m sgn) (i, r1) (i, r2) ->
      evalsto p m (i,r1) (res1) -> 
      evalsto p m (i,r2) (res2) -> 
        indist_return_value kobs sgn res1 res2.
Proof.
  intros kobs p cdr [se [RT HT]] m sgn i r1 r2 res1 res2 H Hinit Hindist Hevalsto1 Hevalsto2.
  assert (Hni:=safe_ni kobs PC Method (step p) (PM p) cdr Reg Sign istate rstate (exec p) pc 
    (tcc0 p) (tcc1 p) registertypes (texec p cdr) (high_reg kobs)
    (indist_reg_val) (indist_reg_val_trans) (indist_reg_val_sym)
    (indist kobs) (indist_from_reg kobs) (indist_reg_from_indist kobs)
    (rindist kobs) (tcc3 kobs) (high_result kobs) (rt0) (init_pc)
    (P p) (PM_P p) (indist2_intra kobs p cdr) (indist2_return kobs p cdr)
    (soap2_basic_intra kobs p cdr) (sub) (sub_simple kobs)
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

Theorem correctness : forall
  (p:DEX_ExtendedProgram)
(*   (subclass_test : ClassName -> ClassName -> bool), *)
(*   (forall c1 c2, if subclass_test c1 c2 then subclass_name p c1 c2 else ~ subclass_name p c1 c2) -> *)
(*   check_well_formed_lookupswitch p =true -> *)
(*   forall  *)
    (kobs:L.t)
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
  intros p kobs reg jun Hcheck se RT.
  intros Hc.
  intros m sgn i res1 res2 r1 r2 H H0 H1 H2.
  assert (T:=check_all_cdr_correct p (reg) (jun) Hcheck).
  assert (TT:=check_correct _ _ _ _ jun T Hc).
  eapply ni_safe; eauto.
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
  destruct (andb_prop _ _ HcheckTypable) as [Hcheck_all_cdr Hcheck].
  generalize (BigStep_evalsto _ _ _ _ Hstep1). 
  generalize (BigStep_evalsto _ _ _ _ Hstep2). 
  intros Hevalsto2 Hevalsto1.
  assert (T:=for_all_P_true _ _ Hcheck _ _ HPM).
  destruct (andb_prop _ _ T).
  eapply correctness with (7:=Hevalsto2) (6:=Hevalsto1); eauto.
Qed.