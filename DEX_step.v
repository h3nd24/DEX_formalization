(** Static Intra-method control flow step. We also implement an iterator on it *)

Require Export Annotated.
Import DEX_StaticHandler.DEX_StaticHandler DEX_BigStep.DEX_Dom DEX_Prog.


  Section DEX_S_section.   (** step relation **)
    Variable p : DEX_Program.
    Variable subclass_test : DEX_ClassName -> DEX_ClassName -> bool.
    Variable m : DEX_Method.

    (* DEX Definition handler := handler subclass_test m.*)

    Inductive DEX_step : DEX_PC -> DEX_Instruction -> DEX_tag -> option DEX_PC -> Prop :=
    | nop : forall i j,
      next m i = Some j ->
      DEX_step i Nop None (Some j)
    | move : forall i j (k:DEX_ValKind) (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Move k rt rs) None (Some j)
    | moveResult : forall i j (k:DEX_ValKind) (rt:DEX_Reg),
      next m i = Some j ->
      DEX_step i (MoveResult k rt) None (Some j)
    | return_s : forall i,
      DEX_step i Return None None
    | vReturn : forall i (k:DEX_ValKind) (rt:DEX_Reg),
      DEX_step i (VReturn k rt) None None
    | const : forall i j (k:DEX_ValKind) (rt:DEX_Reg) (v:Z),
      next m i = Some j ->
      DEX_step i (Const k rt v) None (Some j)
    | instanceOf : forall i j (rt:DEX_Reg) (r:DEX_Reg) (t:DEX_refType),
      next m i = Some j ->
      DEX_step i (InstanceOf rt r t) None (Some j)
    | arrayLength : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (ArrayLength rt rs) None (Some j)
    | new : forall i j (rt:DEX_Reg) (t:DEX_refType),
      next m i = Some j ->
      DEX_step i (New rt t) None (Some j) 
    | newArray : forall i j (rt:DEX_Reg) (rl:DEX_Reg) (t:DEX_type),
      next m i = Some j ->
      DEX_step i (NewArray rt rl t) None (Some j)
    | goto : forall i (o:DEX_OFFSET.t),
      DEX_step i (Goto o) None (Some (DEX_OFFSET.jump i o))
(* still experimental for PackedSwitch in that the next instruction is
   defined as the difference between i and j *)
(*    | packedSwitch : forall i j (rt:DEX_Reg) (firstKey:Z) (size:Z) (l:list OFFSET.t),
      (* next m i = Some j \/ In o ((j - i)::l) -> *)
      next m i = Some j \/ In j (@map _ _ (OFFSET.jump i) l) ->
      step i (PackedSwitch rt firstKey size l) None (Some j)
    | sparseSwitch : forall i j (rt:DEX_Reg) (size:Z) (l:list (Z * OFFSET.t)),
      next m i = Some j \/ In j (@map _ _ (OFFSET.jump i) (@map _ _ (@snd _ _) l)) ->
      step i (SparseSwitch rt size l) None (Some j) *)
    | ifcmp : forall i j (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t),
      next m i = Some j \/ j = DEX_OFFSET.jump i o ->
      DEX_step i (Ifcmp cmp ra rb o) None (Some j)
    | ifz : forall i j (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t),
      next m i = Some j \/ j = DEX_OFFSET.jump i o ->
      DEX_step i (Ifz cmp r o) None (Some j)
    | aget : forall i j (k:DEX_ArrayKind) (rt:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Aget k rt ra ri) None (Some j)
    | aput : forall i j (k:DEX_ArrayKind) (rs:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Aput k rs ra ri) None (Some j)
    | iget : forall i j (k:DEX_ValKind) (rt:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      next m i = Some j ->
      DEX_step i (Iget k rt ro f) None (Some j)
    | iput : forall i j (k:DEX_ValKind) (rs:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      next m i = Some j ->
      DEX_step i (Iput k rs ro f) None (Some j)
(*    
    | Sget (k:ValKind) (rt:DEX_Reg) (f:FieldSignature)
    | Sput (k:ValKind) (rs:DEX_Reg) (f:FieldSignature) 
*)
    | invokevirtual : forall i j (m0:DEX_MethodSignature) (n:Z) (p:list DEX_Reg),
      next m i = Some j ->
      DEX_step i (Invokevirtual m0 n p) None (Some j)
    | invokesuper : forall i j (m0:DEX_MethodSignature) (n:Z) (p:list DEX_Reg),
      next m i = Some j ->
      DEX_step i (Invokesuper m0 n p) None (Some j)
    | invokedirect : forall i j (m0:DEX_MethodSignature) (n:Z) (p:list DEX_Reg),
      next m i = Some j ->
      DEX_step i (Invokedirect m0 n p) None (Some j)
    | invokestatic : forall i j (m0:DEX_MethodSignature) (n:Z) (p:list DEX_Reg),
      next m i = Some j ->
      DEX_step i (Invokestatic m0 n p) None (Some j)
    | invokeinterface : forall i j (m0:DEX_MethodSignature) (n:Z) (p:list DEX_Reg),
      next m i = Some j ->
      DEX_step i (Invokeinterface m0 n p) None (Some j)
    | ineg : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Ineg rt rs) None (Some j)
    | inot : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Inot rt rs) None (Some j)
    | i2b : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (I2b rt rs) None (Some j)
    | i2s : forall i j (rt:DEX_Reg) (rs:DEX_Reg),
      next m i = Some j ->
      DEX_step i (I2s rt rs) None (Some j)
    | ibinop : forall i j (op:DEX_BinopInt) (rt:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg),
      next m i = Some j ->
      DEX_step i (Ibinop op rt ra rb) None (Some j)
    | ibinopConst : forall i j (op:DEX_BinopInt) (rt:DEX_Reg) (r:DEX_Reg) (v:Z),
      next m i = Some j ->
      DEX_step i (IbinopConst op rt r v) None (Some j)
    | packedSwitch : forall i j d (rt:DEX_Reg) (firstKey:Z) (size:Z) (l:list DEX_OFFSET.t),
      (next m i = Some d /\ d = DEX_OFFSET.jump i j) \/ In j l ->
      DEX_step i (PackedSwitch rt firstKey size l) None (Some (DEX_OFFSET.jump i j))
    | sparseSwitch : forall i j d (rt:DEX_Reg) (size:Z) (l:list (Z * DEX_OFFSET.t)),
      (next m i = Some d /\ d = DEX_OFFSET.jump i j) \/ 
        In j (@map _ _ (@snd _ _) l) ->
      DEX_step i (SparseSwitch rt size l) None (Some (DEX_OFFSET.jump i j))
.

    Definition get_steps (i:DEX_PC) (ins:DEX_Instruction) (next:option DEX_PC): list (DEX_tag * option DEX_PC) := 
      match ins with
        | SparseSwitch r size l =>
          (None,next) :: map (fun o => (None,Some (DEX_OFFSET.jump i o))) (@map _ _ (@snd _ _) l)
        | PackedSwitch r firstKey size l =>
          (None,next) :: map (fun o => (None,Some (DEX_OFFSET.jump i o))) (l)
        | Return => (None,None)::nil
        | VReturn k rt => (None,None)::nil
        | Goto o => (None,Some (DEX_OFFSET.jump i o))::nil
        | Ifcmp cmp ra rb o => (None,next)::(None,Some (DEX_OFFSET.jump i o))::nil
        | Ifz cmp r o => (None,next)::(None,Some (DEX_OFFSET.jump i o))::nil
        | _ => (None,next)::nil
      end.

    Lemma all_step_in_get_steps : forall i ins tau oj,
        DEX_step i ins tau oj -> 
        In (tau,oj) (get_steps i ins (next m i)).
    Proof.
      intros.
      inversion_clear H; simpl get_steps; try rewrite H0;
      auto with datatypes;
      (* ifcmp and ifz cases *)
        try (destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes;
        right; subst; left; reflexivity).
      (* PackedSwitch case *)
        (* default case : next instruction *)
        destruct H0. left. inversion H. rewrite <- H1. rewrite H0. reflexivity.
        (* other successors case *)
        right. try match goal with
          [ |- In (_,_) (map ?F _) ] => 
          apply in_map with (f:=F); try assumption
        end.
      (* SparseSwitch case *)
        (* default case : next instruction *)
        destruct H0. left. inversion H. rewrite <- H1. rewrite H0. reflexivity.
        (* other successors case *)
        right. try match goal with
          [ |- In (_,_) (map ?F _) ] => 
          apply in_map with (f:=F); try assumption
        end.
    Qed.

  Section for_all_steps.
    Variable test : DEX_PC -> DEX_Instruction -> DEX_tag -> option DEX_PC -> bool.

    Definition for_all_steps_bm (bm:DEX_BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:DEX_Instruction*(option DEX_PC*list DEX_ClassName)) =>
        let (ins,next) := ins_next in
          for_all _
          (fun (tau_oj:DEX_tag*option DEX_PC) => let (tau,oj):=tau_oj in test i ins tau oj)
          (get_steps i ins (fst next)))
      bm.(DEX_BYTECODEMETHOD.instr).

    Lemma for_all_steps_bm_true : forall bm,
      DEX_METHOD.body m = Some bm ->
      for_all_steps_bm bm = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        DEX_step i ins tau oj -> test i ins tau oj = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, DEX_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (DEX_Instruction * (option DEX_PC*list DEX_ClassName)) (DEX_BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      apply for_all_true with
        (test:=(fun tau_oj : DEX_tag * option DEX_PC =>
          let (tau, oj) := tau_oj in test i ins tau oj))
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
            (fun (tau_oj:DEX_tag*option DEX_PC) => let (tau,oj):=tau_oj in test i ins tau oj)
            (get_steps i ins (fst next))))
      (MapN.elements _ bm.(DEX_BYTECODEMETHOD.instr))
    end.

  Lemma for_all_steps_m_true : for_all_steps_m = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        DEX_step i ins tau oj -> test i ins tau oj = true.
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
    Variable test : DEX_tag -> option DEX_PC -> bool.

    Definition for_all_succs_bm (bm:DEX_BytecodeMethod) : bool :=
      match MapN.get _ bm.(DEX_BYTECODEMETHOD.instr) pc with
        | None => true
        | Some (ins,(op,l)) => 
          for_all _
          (fun (tau_oj:DEX_tag*option DEX_PC) => let (tau,oj):=tau_oj in test tau oj)
          (get_steps pc ins op)
      end.

    Lemma for_all_succs_bm_true : forall bm,
      DEX_METHOD.body m = Some bm ->
      for_all_succs_bm bm = true ->
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        DEX_step pc ins tau oj -> test tau oj = true.
    Proof.
      unfold for_all_succs_bm; intros.
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, DEX_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (DEX_Instruction * (option DEX_PC*list DEX_ClassName)) (DEX_BYTECODEMETHOD.instr bm) pc).
      intros (ins0,next0) T3.
      rewrite T3 in H1; rewrite T3 in H0.
      destruct next0.
      apply for_all_true with
        (test:=(fun tau_oj : DEX_tag * option DEX_PC =>
          let (tau, oj) := tau_oj in test tau oj))
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
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        DEX_step pc ins tau oj -> test tau oj = true.
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


  




