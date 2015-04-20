(** Static Intra-method control flow step. We also implement an iterator on it *)

Require Export Annotated.
Import StaticHandler.StaticHandler BigStep.Dom Prog.


  Section S_section.   (** step relation **)
    Variable p : Program.
    Variable subclass_test : ClassName -> ClassName -> bool.
    Variable m : Method.

    Definition handler := handler subclass_test m.

    Inductive step : PC -> Instruction -> tag -> option PC -> Prop :=
    | aconst_null : forall i j,
      next m i = Some j ->
      step i Aconst_null None (Some j)
    | arraylength : forall i j,
      next m i = Some j ->
      step i Arraylength None (Some j)
    | arraylength_np_caught : forall i t,
      In np (throwableAt m i) ->
      handler i np = Some t ->
      step i Arraylength (Some np) (Some t)
    | arraylength_np_uncaught : forall i,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i Arraylength (Some np) None
    | athrow_caught : forall e i t,
      In e (throwableAt m i) ->
      handler i e = Some t ->
      step i Athrow (Some e) (Some t)
    | athrow_uncaught : forall e i,
      In e (throwableAt m i) ->
      handler i e = None ->
      step i Athrow (Some e) None
    | checkcast1 : forall i t j,
      next m i = Some j ->
      step i (Checkcast t) None (Some j)
    | checkcast_caught : forall i t te,
      In cc (throwableAt m i) ->
      handler i cc = Some te ->
      step i (Checkcast t) (Some cc) (Some te)
    | checkcast_uncaught : forall i t,
      In cc (throwableAt m i) ->
      handler i cc = None ->
      step i (Checkcast t) (Some cc) None
    | const : forall i t z j,
      next m i = Some j ->
      step i (Const t z) None (Some j)
    | dup : forall i j,
      next m i = Some j ->
      step i Dup None (Some j)
    | dup_x1 : forall i j,
      next m i = Some j ->
      step i Dup_x1 None (Some j)
    | dup_x2 : forall i j,
      next m i = Some j ->
      step i Dup_x2 None (Some j)
    | dup2 : forall i j,
      next m i = Some j ->
      step i Dup2 None (Some j)
    | dup2_x1 : forall i j,
      next m i = Some j ->
      step i Dup2_x1 None (Some j)
    | dup2_x2 : forall i j,
      next m i = Some j ->
      step i Dup2_x2 None (Some j)
    | getfield : forall i f j,
      next m i = Some j ->
      step i (Getfield f) None (Some j)
    | getfield_np_caught : forall i t f,
      In np (throwableAt m i) ->
      handler i np = Some t ->
      step i (Getfield f) (Some np) (Some t)
    | getfield_np_uncaught : forall i f,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Getfield f) (Some np) None
    | goto : forall i o,
      step i (Goto o) None (Some (OFFSET.jump i o))
    | i2b : forall i j,
      next m i = Some j ->
      step i I2b None (Some j)
    | i2s : forall i j,
      next m i = Some j ->
      step i I2s None (Some j)
    | ibinop : forall i op j,
      next m i = Some j ->
      step i (Ibinop op) None (Some j)
    | ibinop_ae_caught : forall i t op,
      In ae (throwableAt m i) ->
      op = DivInt \/ op = RemInt ->
      handler i ae = Some t ->
      step i (Ibinop op) (Some ae) (Some t)
    | ibinop_ae_uncaught : forall i op,
      In ae (throwableAt m i) ->
      op = DivInt \/ op = RemInt ->
      handler i ae = None ->
      step i (Ibinop op) (Some ae) None
    | if_acmp : forall i cmp o j,
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (If_acmp cmp o) None (Some j)
    | if_icmp : forall i cmp o j,
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (If_icmp cmp o) None (Some j)
    | ifeq : forall i cmp o j,
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (If0 cmp o) None (Some j)
    | ifnull : forall i cmp o j,
      next m i = Some j \/ j = OFFSET.jump i o ->
      step i (Ifnull cmp o) None (Some j)
    | iinc : forall i x c j,
      next m i = Some j ->
      step i (Iinc x c) None (Some j)
    | ineg : forall i j,
      next m i = Some j ->
      step i Ineg None (Some j)
    | instanceof : forall i t j,
      next m i = Some j ->
      step i (Instanceof t) None (Some j)
    | invokestatic : forall i mid j,
      next m i = Some j ->
      step i (Invokestatic mid) None (Some j)
    | invokestatic_caught : forall i mid t e,
      In e (throwableBy p (snd mid)) -> 
      handler i e = Some t ->
      step i (Invokestatic mid) (Some e) (Some t)
    | invokestatic_uncaught : forall i mid e,
      In e (throwableBy p (snd mid)) -> 
      handler i e = None ->
      step i (Invokestatic mid) (Some e) None
    | invokevirtual : forall i mid j,
      next m i = Some j ->
      step i (Invokevirtual mid) None (Some j)
    | invokevirtual_caught : forall i mid t e,
      In e ((throwableAt m i)++throwableBy p (snd mid)) -> 
      handler i e = Some t ->
      step i (Invokevirtual mid) (Some e) (Some t)
    | invokevirtual_uncaught : forall i mid e,
      In e ((throwableAt m i)++throwableBy p (snd mid)) -> 
      handler i e = None ->
      step i (Invokevirtual mid) (Some e) None
    | lookupswitch : forall i d l o,
      In o (d::@map _ _ (@snd _ _) l) ->
      step i (Lookupswitch d l) None (Some (OFFSET.jump i o))
    | new : forall i c j,
      next m i = Some j ->
      step i (New c) None (Some j)
    | newarray : forall i t j,
      next m i = Some j ->
      step i (Newarray t) None (Some j)
    | newarray_nase_caught : forall i t te,
      In nase (throwableAt m i) ->
      handler i nase = Some te ->
      step i (Newarray t) (Some nase) (Some te)
    | newarray_nase_uncaught : forall i t,
      In nase (throwableAt m i) ->
      handler i nase = None ->
      step i (Newarray t) (Some nase) None
    | nop : forall i j,
      next m i = Some j ->
      step i Nop None (Some j)
    | pop : forall i j,
      next m i = Some j ->
      step i Pop None (Some j)
    | pop2 : forall i j,
      next m i = Some j ->
      step i Pop2 None (Some j)
    | putfield : forall i f j,
      next m i = Some j ->
      step i (Putfield f) None (Some j)
    | putfield_np_caught : forall i t f,
      In np (throwableAt m i) ->
      handler i np = Some t ->
      step i (Putfield f) (Some np) (Some t)
    | putfield_np_uncaught : forall i f,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Putfield f) (Some np) None
    | return_ : forall i,
      step i Return None None
    | swap : forall i j,
      next m i = Some j ->
      step i Swap None (Some j)
    | tableswitch : forall i d lo hi l o,
      In o (d::l) ->
      step i (Tableswitch d lo hi l) None (Some (OFFSET.jump i o))
    | vaload : forall i t j,
      next m i = Some j ->
      step i (Vaload t)  None (Some j)
    | vaload_np_caught : forall i t te,
      In np (throwableAt m i) ->
      handler i np = Some te ->
      step i (Vaload t) (Some np) (Some te)
    | vaload_np_uncaught : forall i t,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Vaload t) (Some np) None
    | vaload_iob_caught : forall i te t,
      In iob (throwableAt m i) ->
      handler i iob = Some te ->
      step i (Vaload t) (Some iob) (Some te)
    | vaload_iob_uncaught : forall i t,
      In iob (throwableAt m i) ->
      handler i iob = None ->
      step i (Vaload t) (Some iob) None
    | vastore : forall i t j,
      next m i = Some j ->
      step i (Vastore t) None (Some j)
    | vastore_np_caught : forall i t te,
      In np (throwableAt m i) ->
      handler i np = Some te ->
      step i (Vastore t) (Some np) (Some te)
    | vastore_np_uncaught : forall i t,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Vastore t) (Some np) None
    | vastore_ase_caught : forall i t te,
      In ase (throwableAt m i) ->
      handler i ase = Some te ->
      step i (Vastore t) (Some ase) (Some te)
    | vastore_ase_uncaught : forall i t,
      In ase (throwableAt m i) ->
      handler i ase = None ->
      step i (Vastore t) (Some ase) None
    | vastore_iob_caught : forall i t te,
      In iob (throwableAt m i) ->
      handler i iob = Some te ->
      step i (Vastore t) (Some iob) (Some te)
    | vastore_iob_uncaught : forall i t,
      In iob (throwableAt m i) ->
      handler i iob = None ->
      step i (Vastore t) (Some iob) None
    | vload : forall i t x j,
      next m i = Some j ->
      step i (Vload t x) None (Some j)
    | vstore : forall i t x j,
      next m i = Some j ->
      step i (Vstore t x) None (Some j)
    | vreturn : forall i x,
      step i (Vreturn x) None None.

    Definition get_steps (i:PC) (ins:Instruction) (next:option PC): list (tag * option PC) := 
      match ins with
        | Arraylength => (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Athrow => map (fun e => (Some e,handler i e)) (throwableAt m i)
        | Checkcast _ => (None,next)::(Some cc,handler i cc)::nil
        | Getfield _ => (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Ibinop op => (None,next)::
          (match op with
             | DivInt =>map (fun e => (Some e,handler i e)) (throwableAt m i)
             | RemInt => map (fun e => (Some e,handler i e)) (throwableAt m i)
             | _ => nil
           end)
        | Invokestatic mid => 
          (None,next)::(map (fun e => (Some e,handler i e)) ((throwableAt m i)++throwableBy p (snd mid)))
        | Invokevirtual mid =>
          (None,next)::(map (fun e => (Some e,handler i e)) ((throwableAt m i)++throwableBy p (snd mid)))
        | Lookupswitch d l =>
          map (fun o => (None,Some (OFFSET.jump i o))) (d::@map _ _ (@snd _ _) l)
        | Newarray _ =>  (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Putfield _ => (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Return => (None,None)::nil
        | Tableswitch d lo hi l =>
          map (fun o => (None,Some (OFFSET.jump i o))) (d::l) 
        | Vaload _ => (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Vastore _ => (None,next)::(map (fun e => (Some e,handler i e)) (throwableAt m i))
        | Vreturn _ => (None,None)::nil
        | Goto o => (None,Some (OFFSET.jump i o))::nil
        | If_acmp cmp o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | If_icmp cmp o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | If0 cmp o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | Ifnull cmp o => (None,next)::(None,Some (OFFSET.jump i o))::nil
        | _ => (None,next)::nil
      end.

    Lemma all_step_in_get_steps : forall i ins tau oj,
        step i ins tau oj -> 
        In (tau,oj) (get_steps i ins (next m i)).
    Proof.
      intros.
      inversion_clear H; simpl get_steps; try rewrite H0; auto with datatypes;
      try match goal with
        [ id : handler _ _ = ?x |- _ ] => 
        pattern x at 1; rewrite <- id
          end;
      try (
        repeat ((left; reflexivity)||right);
          try match goal with
                [ |- In (_,_) (map ?F _) ] => 
                apply in_map with (f:=F); try assumption;
                  apply in_or_app; auto
              end; fail).
      right;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
      apply in_map with (f:=F); try assumption
      end.
      destruct H1; subst; simpl; auto with datatypes;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
            apply in_map with (f:=F); try assumption
      end.
      right; destruct H1; subst; simpl; auto with datatypes;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
            apply in_map with (f:=F); try assumption
      end.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0; subst.
      left; reflexivity.
      right; match goal with
      [ |- In (_,_) (map ?F _) ] => 
      apply in_map with (f:=F); try assumption
      end.
      destruct H0; subst.
      left; reflexivity.
      right; match goal with
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


  




