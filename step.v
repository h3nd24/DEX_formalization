(** Static Intra-method control flow step. We also implement an iterator on it *)

Require Export Annotated.
Import StaticHandler.StaticHandler BigStep.Dom Prog.


  Section S_section.   (** step relation **)
    Variable p : Program.
    Variable subclass_test : ClassName -> ClassName -> bool.
    Variable m : Method.

    (* DEX Definition handler := handler subclass_test m.*)

    Inductive step : PC -> Instruction -> tag -> option PC -> Prop :=
    | nop : forall i j,
      next m i = Some j ->
      step i Nop None (Some j)
    | move : forall i j (k:ValKind) (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (Move k rt rs) None (Some j)
    | moveResult : forall i j (k:ValKind) (rt:Var),
      next m i = Some j ->
      step i (MoveResult k rt) None (Some j)
    | return_s : forall i,
      step i Return None None
    | vReturn : forall i (k:ValKind) (rt:Var),
      step i (VReturn k rt) None None
    | const : forall i j (k:ValKind) (rt:Var) (v:Z),
      next m i = Some j ->
      step i (Const k rt v) None (Some j)
    | instanceOf : forall i j (rt:Var) (r:Var) (t:refType),
      next m i = Some j ->
      step i (InstanceOf rt r t) None (Some j)
    | arrayLength : forall i j (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (ArrayLength rt rs) None (Some j)
    | new : forall i j (rt:Var) (t:refType),
      next m i = Some j ->
      step i (New rt t) None (Some j) 
    | newArray : forall i j (rt:Var) (rl:Var) (t:type),
      next m i = Some j ->
      step i (NewArray rt rl t) None (Some j)
    | goto : forall i (o:OFFSET.t),
      step i (Goto o) None (Some (OFFSET.jump i o))
(* still experimental for PackedSwitch in that the next instruction is
   defined as the difference between i and j *)
(*    | packedSwitch : forall i j (rt:Var) (firstKey:Z) (size:Z) (l:list OFFSET.t),
      (* next m i = Some j \/ In o ((j - i)::l) -> *)
      next m i = Some j \/ In j (@map _ _ (OFFSET.jump i) l) ->
      step i (PackedSwitch rt firstKey size l) None (Some j)
    | sparseSwitch : forall i j (rt:Var) (size:Z) (l:list (Z * OFFSET.t)),
      next m i = Some j \/ In j (@map _ _ (OFFSET.jump i) (@map _ _ (@snd _ _) l)) ->
      step i (SparseSwitch rt size l) None (Some j) *)
    | ifcmp : forall i j (cmp:CompInt) (ra:Var) (rb:Var) (o:OFFSET.t),
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (Ifcmp cmp ra rb o) None (Some j)
    | ifz : forall i j (cmp:CompInt) (r:Var) (o:OFFSET.t),
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (Ifz cmp r o) None (Some j)
    | aget : forall i j (k:ArrayKind) (rt:Var) (ra:Var) (ri:Var),
      next m i = Some j ->
      step i (Aget k rt ra ri) None (Some j)
    | aput : forall i j (k:ArrayKind) (rs:Var) (ra:Var) (ri:Var),
      next m i = Some j ->
      step i (Aput k rs ra ri) None (Some j)
    | iget : forall i j (k:ValKind) (rt:Var) (ro:Var) (f:FieldSignature),
      next m i = Some j ->
      step i (Iget k rt ro f) None (Some j)
    | iput : forall i j (k:ValKind) (rs:Var) (ro:Var) (f:FieldSignature),
      next m i = Some j ->
      step i (Iput k rs ro f) None (Some j)
(*    
    | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
    | Sput (k:ValKind) (rs:Var) (f:FieldSignature) 
*)
    | invokevirtual : forall i j (m0:MethodSignature) (n:Z) (p:list Var),
      next m i = Some j ->
      step i (Invokevirtual m0 n p) None (Some j)
    | invokesuper : forall i j (m0:MethodSignature) (n:Z) (p:list Var),
      next m i = Some j ->
      step i (Invokesuper m0 n p) None (Some j)
    | invokedirect : forall i j (m0:MethodSignature) (n:Z) (p:list Var),
      next m i = Some j ->
      step i (Invokedirect m0 n p) None (Some j)
    | invokestatic : forall i j (m0:MethodSignature) (n:Z) (p:list Var),
      next m i = Some j ->
      step i (Invokestatic m0 n p) None (Some j)
    | invokeinterface : forall i j (m0:MethodSignature) (n:Z) (p:list Var),
      next m i = Some j ->
      step i (Invokeinterface m0 n p) None (Some j)
    | ineg : forall i j (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (Ineg rt rs) None (Some j)
    | inot : forall i j (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (Inot rt rs) None (Some j)
    | i2b : forall i j (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (I2b rt rs) None (Some j)
    | i2s : forall i j (rt:Var) (rs:Var),
      next m i = Some j ->
      step i (I2s rt rs) None (Some j)
    | ibinop : forall i j (op:BinopInt) (rt:Var) (ra:Var) (rb:Var),
      next m i = Some j ->
      step i (Ibinop op rt ra rb) None (Some j)
    | ibinopConst : forall i j (op:BinopInt) (rt:Var) (r:Var) (v:Z),
      next m i = Some j ->
      step i (IbinopConst op rt r v) None (Some j)
    | packedSwitch : forall i j d (rt:Var) (firstKey:Z) (size:Z) (l:list OFFSET.t),
      (next m i = Some d /\ d = OFFSET.jump i j) \/ In j l ->
      step i (PackedSwitch rt firstKey size l) None (Some (OFFSET.jump i j))
    | sparseSwitch : forall i j d (rt:Var) (size:Z) (l:list (Z * OFFSET.t)),
      (next m i = Some d /\ d = OFFSET.jump i j) \/ 
        In j (@map _ _ (@snd _ _) l) ->
      step i (SparseSwitch rt size l) None (Some (OFFSET.jump i j))
.

    Definition get_steps (i:PC) (ins:Instruction) (next:option PC): list (tag * option PC) := 
      match ins with
        | SparseSwitch r size l =>
          (None,next) :: map (fun o => (None,Some (OFFSET.jump i o))) (@map _ _ (@snd _ _) l)
        | PackedSwitch r firstKey size l =>
          (None,next) :: map (fun o => (None,Some (OFFSET.jump i o))) (l)
        | Return => (None,None)::nil
        | VReturn k rt => (None,None)::nil
        | Goto o => (None,Some (OFFSET.jump i o))::nil
        | Ifcmp cmp ra rb o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | Ifz cmp r o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | _ => (None,next)::nil
      end.

    Lemma all_step_in_get_steps : forall i ins tau oj,
        step i ins tau oj -> 
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
    Variable test : PC -> Instruction -> tag -> option PC -> bool.

    Definition for_all_steps_bm (bm:BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:Instruction*(option PC*list ClassName)) =>
        let (ins,next) := ins_next in
          for_all _
          (fun (tau_oj:tag*option PC) => let (tau,oj):=tau_oj in test i ins tau oj)
          (get_steps i ins (fst next)))
      bm.(BYTECODEMETHOD.instr).

    Lemma for_all_steps_bm_true : forall bm,
      METHOD.body m = Some bm ->
      for_all_steps_bm bm = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        step i ins tau oj -> test i ins tau oj = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (Instruction * (option PC*list ClassName)) (BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      apply for_all_true with
        (test:=(fun tau_oj : tag * option PC =>
          let (tau, oj) := tau_oj in test i ins tau oj))
        (2:=T2).
      unfold next, BYTECODEMETHOD.nextAddress.
      rewrite H; rewrite T3; simpl.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

  Definition for_all_steps_m : bool :=
    match METHOD.body m with
      | None => false
      | Some bm => for_all_steps_bm bm
    end.

  Definition test_all_steps_m : list (PC*bool) :=
    match METHOD.body m with
      | None => nil
      | Some bm => 
      List.map
      (fun (ins_next:PC*(Instruction*(option PC*list ClassName))) =>
        let (i,ins_next) := ins_next in
        let (ins,next) := ins_next in
          (i,for_all _
            (fun (tau_oj:tag*option PC) => let (tau,oj):=tau_oj in test i ins tau oj)
            (get_steps i ins (fst next))))
      (MapN.elements _ bm.(BYTECODEMETHOD.instr))
    end.

  Lemma for_all_steps_m_true : for_all_steps_m = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        step i ins tau oj -> test i ins tau oj = true.
  Proof.
    unfold for_all_steps_m.
    generalize for_all_steps_bm_true.
    destruct (METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.

  End for_all_steps.

  Section for_all_succs.
    Variable pc:PC.
    Variable test : tag -> option PC -> bool.

    Definition for_all_succs_bm (bm:BytecodeMethod) : bool :=
      match MapN.get _ bm.(BYTECODEMETHOD.instr) pc with
        | None => true
        | Some (ins,(op,l)) => 
          for_all _
          (fun (tau_oj:tag*option PC) => let (tau,oj):=tau_oj in test tau oj)
          (get_steps pc ins op)
      end.

    Lemma for_all_succs_bm_true : forall bm,
      METHOD.body m = Some bm ->
      for_all_succs_bm bm = true ->
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        step pc ins tau oj -> test tau oj = true.
    Proof.
      unfold for_all_succs_bm; intros.
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (Instruction * (option PC*list ClassName)) (BYTECODEMETHOD.instr bm) pc).
      intros (ins0,next0) T3.
      rewrite T3 in H1; rewrite T3 in H0.
      destruct next0.
      apply for_all_true with
        (test:=(fun tau_oj : tag * option PC =>
          let (tau, oj) := tau_oj in test tau oj))
        (2:=T2).
      unfold next, BYTECODEMETHOD.nextAddress.
      inversion_mine H1.
      rewrite H; rewrite T3; simpl; auto.
      intros.
      rewrite H3 in H1; discriminate.
    Qed.

  Definition for_all_succs_m : bool :=
    match METHOD.body m with
      | None => false
      | Some bm => for_all_succs_bm bm
    end.

  Lemma for_all_succs_m_true : for_all_succs_m = true ->
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        step pc ins tau oj -> test tau oj = true.
  Proof.
    unfold for_all_succs_m.
    generalize for_all_succs_bm_true.
    destruct (METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.
   
 End for_all_succs.

  Section for_all_instrs.
    Variable test : PC -> Instruction -> bool.

    Definition for_all_instrs_bm (bm:BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:Instruction*(option PC*list ClassName)) =>
        let (ins,next) := ins_next in test i ins)
      bm.(BYTECODEMETHOD.instr).

    Lemma for_all_instrs_bm_true : forall bm,
      METHOD.body m = Some bm ->
      for_all_instrs_bm bm = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      unfold instructionAt, BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (Instruction * (option PC*list ClassName)) (BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

    Definition for_all_instrs_m : bool :=
      match METHOD.body m with
        | None => false
        | Some bm => for_all_instrs_bm bm
      end.

    Lemma for_all_instrs_m_true : for_all_instrs_m = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      unfold for_all_instrs_m.
      generalize for_all_instrs_bm_true.
      destruct (METHOD.body m) as [bm|]; intro.
      apply H; auto.
      intros; discriminate.
    Qed.

  End for_all_instrs.

End S_section.

Module MapClassTools := MapProjTools PROG.MapClass.

Section p.
  Variable p : Program.

  Definition ValidMethod (m:Method) : Prop :=
    exists c, PROG.defined_Class p c /\ CLASS.defined_Method c m.

  Variable test : Method -> bool.

  Definition for_all_methods : bool :=
    MapClassTools.for_all
    (fun cl =>  MapShortMethSign.for_all _ (fun _ => test) cl.(CLASS.methods))
    p.(PROG.classes_map).

  Lemma for_all_methods_true : for_all_methods = true ->
    forall m, ValidMethod m -> test m = true.
  Proof.
    intros.
    destruct H0 as [c [H0 H1]].
    generalize (MapClassTools.for_all_true _ _ H _ H0); intros.
    unfold CLASS.defined_Method, CLASS.method in H1.
    caseeq (MapShortMethSign.get Method (CLASS.methods c) (METHOD.signature m)); intros.
    rewrite H3 in H1.
    destruct (METHODSIGNATURE.eq_t (METHOD.signature m) (METHOD.signature m0)); inversion_mine H1.
    apply (MapShortMethSign.for_all_true _ _ _ H2 _ _ H3).
    rewrite H3 in H1; discriminate.
  Qed.

End p.


  




