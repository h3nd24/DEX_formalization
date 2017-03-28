(** Static Intra-method control flow step. We also implement an iterator on it *)
(* Hendra : - Modified to suit DEX program. 
            - DEX has different instructions list from JVM.
            - Also trim the system to contain only Arithmetic
            - Only retain the for_all_steps lemma *)
Require Export Annotated.
Import DEX_BigStep.DEX_Dom DEX_Prog.

  Section DEX_S_section.   (** step relation **)
    Variable m : DEX_Method.

    Inductive DEX_step : DEX_PC -> DEX_Instruction -> option DEX_PC -> Prop := 
    | DEX_nop : forall i j,

      next m i = Some j ->
      DEX_step i DEX_Nop (Some j)

    | DEX_move : forall i j (k:DEX_ValKind) (rt:DEX_Reg) (rs:DEX_Reg),
      
      next m i = Some j ->
      DEX_step i (DEX_Move k rt rs) (Some j)

    | DEX_return_s : forall i,
      DEX_step i DEX_Return None

    | DEX_vReturn : forall i (k:DEX_ValKind) (rt:DEX_Reg),
      DEX_step i (DEX_VReturn k rt) None

    | DEX_const : forall i j (k:DEX_ValKind) (rt:DEX_Reg) (v:Z),

      next m i = Some j ->
      DEX_step i (DEX_Const k rt v) (Some j)

    | DEX_goto : forall i (o:DEX_OFFSET.t),
      DEX_step i (DEX_Goto o) (Some (DEX_OFFSET.jump i o))

    | DEX_ifcmp : forall i j (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t),
      next m i = Some j \/ j = DEX_OFFSET.jump i o ->
      DEX_step i (DEX_Ifcmp cmp ra rb o) (Some j)

    | DEX_ifz : forall i j (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t),
      next m i = Some j \/ j = DEX_OFFSET.jump i o ->
      DEX_step i (DEX_Ifz cmp r o) (Some j)

    | DEX_ineg : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (DEX_Ineg rt rs) (Some j)

    | DEX_inot : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (DEX_Inot rt rs) (Some j)

    | DEX_i2b : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (DEX_I2b rt rs) (Some j)

    | DEX_i2s : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
       next m i = Some j -> 
      DEX_step i (DEX_I2s rt rs) (Some j)
    | DEX_ibinop : forall i j (op:DEX_BinopInt) (rt:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg),
       next m i = Some j -> 
      DEX_step i (DEX_Ibinop op rt ra rb) (Some j)

    | DEX_ibinopConst : forall i j (op:DEX_BinopInt) (rt:DEX_Reg) (r:DEX_Reg) (v:Z),
       next m i = Some j -> 
      DEX_step i (DEX_IbinopConst op rt r v) (Some j)

    | DEX_packedSwitch : forall i j (reg:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t),
      next m i = Some j ->
      DEX_step i (DEX_PackedSwitch reg firstKey size l) (Some j)

    | DEX_packedSwitch_jump : forall i j (reg:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t),
      In j l ->
      DEX_step i (DEX_PackedSwitch reg firstKey size l) (Some (DEX_OFFSET.jump i j))

    | DEX_sparseSwitch_default : forall i j (reg:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)),
      next m i = Some j ->
      DEX_step i (DEX_SparseSwitch reg size l) (Some j)

    | DEX_sparseSwitch_jump : forall i (j:DEX_OFFSET.t) (reg:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)),
      In j (@map _ _ (@snd _ _) l) ->
      DEX_step i (DEX_SparseSwitch reg size l) (Some (DEX_OFFSET.jump i j))

    | DEX_iput : forall i j k rs ro f,
      next m i = Some j ->
      DEX_step i (DEX_Iput k rs ro f) (Some j)

    | DEX_iget : forall i j k r ro f,
      next m i = Some j ->
      DEX_step i (DEX_Iget k r ro f) (Some j)

    | DEX_new : forall i j r c,
      next m i = Some j ->
      DEX_step i (DEX_New r c) (Some j)
.

    Definition get_steps (i:DEX_PC) (ins:DEX_Instruction) (next:option DEX_PC): list (option DEX_PC) := 
      match ins with
        | DEX_SparseSwitch r size l =>
            next :: map (fun o => (Some (DEX_OFFSET.jump i o))) (@map _ _ (@snd _ _) l)
        | DEX_PackedSwitch r firstKey size l =>
            next :: map (fun o => (Some (DEX_OFFSET.jump i o))) (l)
        | DEX_Return => None::nil
        | DEX_VReturn k rt => None::nil
        | DEX_Goto o => (Some (DEX_OFFSET.jump i o))::nil
        | DEX_Ifcmp cmp ra rb o => next::(Some (DEX_OFFSET.jump i o))::nil
        | DEX_Ifz cmp r o => next::(Some (DEX_OFFSET.jump i o))::nil
        | _ => next::nil
      end.

    Lemma all_step_in_get_steps : forall i ins oj,
        DEX_step i ins oj -> 
        In oj (get_steps i ins (next m i)).
    Proof.
      intros.
      inversion_clear H;
      simpl get_steps; try rewrite H0;
      auto with datatypes;
      (* ifcmp and ifz cases *)
        try (destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes;
        right; subst; left; reflexivity).
      (* PackedSwitch case *)
      right; apply in_map with (f:=(fun o : DEX_OFFSET.t => Some (DEX_OFFSET.jump i o))); auto.
      (* SparseSwitch case *)
      right; apply in_map with (f:=(fun o : DEX_OFFSET.t => Some (DEX_OFFSET.jump i o))); auto.
    Qed.

  Section for_all_steps.
    Variable test : DEX_PC -> DEX_Instruction -> option DEX_PC -> bool.

    Definition for_all_steps_bm (bm:DEX_BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:DEX_Instruction*(option DEX_PC *list DEX_ClassName )) =>
        let (ins,next) := ins_next in
          for_all _
          (fun (oj:option DEX_PC) => test i ins oj)
          (get_steps i ins ( fst  next)))
      bm.(DEX_BYTECODEMETHOD.instr).

    Lemma for_all_steps_bm_true : forall bm,
      DEX_METHOD.body m = Some bm ->
      for_all_steps_bm bm = true ->
      forall i ins oj,
        instructionAt m i = Some ins ->
        DEX_step i ins oj -> test i ins oj = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      assert (T2:=all_step_in_get_steps _ _ _ H2).
      unfold instructionAt, DEX_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (DEX_Instruction * (option DEX_PC*list DEX_ClassName)) (DEX_BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      apply for_all_true with
        (test:=(fun oj : option DEX_PC => test i ins oj))
        (2:=T2).
      unfold next, DEX_BYTECODEMETHOD.nextAddress.
      rewrite H; rewrite T3; simpl.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

  Definition for_all_steps_m : bool :=
    match DEX_METHOD.body m with
      | None => false
      | Some bm => for_all_steps_bm bm
    end.

  Definition test_all_steps_m : list (DEX_PC*bool) :=
    match DEX_METHOD.body m with
      | None => nil
      | Some bm => 
      List.map
      (fun (ins_next:DEX_PC*(DEX_Instruction*(option DEX_PC*list DEX_ClassName))) =>
        let (i,ins_next) := ins_next in
        let (ins,next) := ins_next in
          (i,for_all _
            (fun (oj:option DEX_PC) => test i ins oj)
            (get_steps i ins (fst next))))
      (MapN.elements _ bm.(DEX_BYTECODEMETHOD.instr))
    end.

  Lemma for_all_steps_m_true : for_all_steps_m = true ->
      forall i ins oj,
        instructionAt m i = Some ins ->
        DEX_step i ins oj -> test i ins oj = true.
  Proof.
    unfold for_all_steps_m.
    generalize for_all_steps_bm_true.
    destruct (DEX_METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.
  End for_all_steps.

  Section for_all_succs.
    Variable pc:DEX_PC.
    Variable test : option DEX_PC -> bool.

    Definition for_all_succs_bm (bm:DEX_BytecodeMethod) : bool :=
      match MapN.get _ bm.(DEX_BYTECODEMETHOD.instr) pc with
        | None => true
        | Some (ins,(op,l)) => 
          for_all _
          (fun (oj:option DEX_PC) => test oj)
          (get_steps pc ins op)
      end.

    Lemma for_all_succs_bm_true : forall bm,
      DEX_METHOD.body m = Some bm ->
      for_all_succs_bm bm = true ->
      forall ins oj,
        instructionAt m pc = Some ins ->
        DEX_step pc ins oj -> test oj = true.
    Proof.
      unfold for_all_succs_bm; intros.
      assert (T2:=all_step_in_get_steps _ _ _ H2).
      unfold instructionAt, DEX_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (DEX_Instruction * (option DEX_PC*list DEX_ClassName)) (DEX_BYTECODEMETHOD.instr bm) pc).
      intros (ins0,next0) T3.
      rewrite T3 in H1; rewrite T3 in H0.
      destruct next0.
      apply for_all_true with
        (test:=(fun oj : option DEX_PC => test oj))
        (2:=T2).
      unfold next, DEX_BYTECODEMETHOD.nextAddress.
      inversion_mine H1.
      rewrite H; rewrite T3; simpl; auto.
      intros.
      rewrite H3 in H1; discriminate.
    Qed.

  Definition for_all_succs_m : bool :=
    match DEX_METHOD.body m with
      | None => false
      | Some bm => for_all_succs_bm bm
    end.

  Lemma for_all_succs_m_true : for_all_succs_m = true ->
      forall ins oj,
        instructionAt m pc = Some ins ->
        DEX_step pc ins oj -> test oj = true.
  Proof.
    unfold for_all_succs_m.
    generalize for_all_succs_bm_true.
    destruct (DEX_METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.
   
 End for_all_succs.


  Section for_all_instrs.
    Variable test : DEX_PC -> DEX_Instruction -> bool.

    Definition for_all_instrs_bm (bm:DEX_BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:DEX_Instruction*(option DEX_PC*list DEX_ClassName)) =>
        let (ins,next) := ins_next in test i ins)
      bm.(DEX_BYTECODEMETHOD.instr).

    Lemma for_all_instrs_bm_true : forall bm,
      DEX_METHOD.body m = Some bm ->
      for_all_instrs_bm bm = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      unfold instructionAt, DEX_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (DEX_Instruction * (option DEX_PC*list DEX_ClassName)) (DEX_BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

    Definition for_all_instrs_m : bool :=
      match DEX_METHOD.body m with
        | None => false
        | Some bm => for_all_instrs_bm bm
      end.

    Lemma for_all_instrs_m_true : for_all_instrs_m = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      unfold for_all_instrs_m.
      generalize for_all_instrs_bm_true.
      destruct (DEX_METHOD.body m) as [bm|]; intro.
      apply H; auto.
      intros; discriminate.
    Qed.

  End for_all_instrs.

End DEX_S_section.

Module DEX_MapClassTools := MapProjTools DEX_PROG.DEX_MapClass.

Section p.
  Variable p : DEX_Program.

  Definition ValidMethod (m:DEX_Method) : Prop :=
    exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

  Variable test : DEX_Method -> bool.

  Definition for_all_methods : bool :=
    DEX_MapClassTools.for_all
    (fun cl =>  DEX_MapShortMethSign.for_all _ (fun _ => test) cl.(DEX_CLASS.methods))
    p.(DEX_PROG.classes_map).

  Lemma for_all_methods_true : for_all_methods = true ->
    forall m, ValidMethod m -> test m = true.
  Proof.
    intros.
    destruct H0 as [c [H0 H1]].
    generalize (DEX_MapClassTools.for_all_true _ _ H _ H0); intros.
    unfold DEX_CLASS.defined_Method, DEX_CLASS.method in H1.
    caseeq (DEX_MapShortMethSign.get DEX_Method (DEX_CLASS.methods c) (DEX_METHOD.signature m)); intros.
    rewrite H3 in H1.
    destruct (DEX_METHODSIGNATURE.eq_t (DEX_METHOD.signature m) (DEX_METHOD.signature d)); inversion_mine H1.
    apply (DEX_MapShortMethSign.for_all_true _ _ _ H2 _ _ H3).
    rewrite H3 in H1; discriminate.
  Qed.

End p.