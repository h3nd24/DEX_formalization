(** Static Intra-method control flow step. We also implement an iterator on it *)

Require Export Annotated.
Import JVM_StaticHandler.JVM_StaticHandler JVM_BigStep.JVM_Dom JVM_Prog.


  Section JVM_S_section.   (** step relation **)
    Variable p : JVM_Program.
    Variable subclass_test : JVM_ClassName -> JVM_ClassName -> bool.
    Variable m : JVM_Method.

    (* DEX Definition handler := handler subclass_test m. *)

    Inductive JVM_step : JVM_PC -> JVM_Instruction -> JVM_tag -> option JVM_PC -> Prop :=
(* DEX Object
    | JVM_aconst_null : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Aconst_null None (Some j)
    | arraylength : forall i j,
      next m i = Some j ->
      JVM_step i Arraylength None (Some j)
*)
(* DEX Exception
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
*)
(* DEX
    | checkcast1 : forall i t j,
      next m i = Some j ->
      step i (Checkcast t) None (Some j)
*)
(* DEX
    | checkcast_caught : forall i t te,
      In cc (throwableAt m i) ->
      handler i cc = Some te ->
      step i (Checkcast t) (Some cc) (Some te)
    | checkcast_uncaught : forall i t,
      In cc (throwableAt m i) ->
      handler i cc = None ->
      step i (Checkcast t) (Some cc) None
*)
    | JVM_const : forall i t z j,
      next m i = Some j ->
      JVM_step i (JVM_Const t z) None (Some j)
    | JVM_dup : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup None (Some j)
    | JVM_dup_x1 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup_x1 None (Some j)
    | JVM_dup_x2 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup_x2 None (Some j)
    | JVM_dup2 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup2 None (Some j)
    | JVM_dup2_x1 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup2_x1 None (Some j)
    | JVM_dup2_x2 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Dup2_x2 None (Some j)
(* DEX Object
    | getfield : forall i f j,
      next m i = Some j ->
      JVM_step i (Getfield f) None (Some j)
*)
(* DEX Exception
    | getfield_np_caught : forall i t f,
      In np (throwableAt m i) ->
      handler i np = Some t ->
      step i (Getfield f) (Some np) (Some t)
    | getfield_np_uncaught : forall i f,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Getfield f) (Some np) None
*)
    | JVM_goto : forall i o,
      JVM_step i (JVM_Goto o) None (Some (JVM_OFFSET.jump i o))
    | JVM_i2b : forall i j,
      next m i = Some j ->
      JVM_step i JVM_I2b None (Some j)
    | JVM_i2s : forall i j,
      next m i = Some j ->
      JVM_step i JVM_I2s None (Some j)
    | JVM_ibinop : forall i op j,
      next m i = Some j ->
      JVM_step i (JVM_Ibinop op) None (Some j)
(* DEX
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
*)
(* DEX Object
    | if_acmp : forall i cmp o j,
      next m i = Some j \/ j = JVM_OFFSET.jump i o ->
      JVM_step i (If_acmp cmp o) None (Some j)
*)
    | JVM_if_icmp : forall i cmp o j,
      next m i = Some j \/ j = JVM_OFFSET.jump i o ->
      JVM_step i (JVM_If_icmp cmp o) None (Some j)
    | JVM_ifeq : forall i cmp o j,
      next m i = Some j \/ j = JVM_OFFSET.jump i o ->
      JVM_step i (JVM_If0 cmp o) None (Some j)
(* DEX Object
    | ifnull : forall i cmp o j,
      next m i = Some j \/ j = JVM_OFFSET.jump i o ->
      JVM_step i (Ifnull cmp o) None (Some j)
*)
    | JVM_iinc : forall i x c j,
      next m i = Some j ->
      JVM_step i (JVM_Iinc x c) None (Some j)
    | JVM_ineg : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Ineg None (Some j)
(* DEX Object and Method
    | instanceof : forall i t j,
      next m i = Some j ->
      JVM_step i (Instanceof t) None (Some j)
    | invokestatic : forall i mid j,
      next m i = Some j ->
      JVM_step i (Invokestatic mid) None (Some j)
(* DEX
    | invokestatic_caught : forall i mid t e,
      In e (throwableBy p (snd mid)) -> 
      handler i e = Some t ->
      step i (Invokestatic mid) (Some e) (Some t)
    | invokestatic_uncaught : forall i mid e,
      In e (throwableBy p (snd mid)) -> 
      handler i e = None ->
      step i (Invokestatic mid) (Some e) None
*)
    | invokevirtual : forall i mid j,
      next m i = Some j ->
      JVM_step i (Invokevirtual mid) None (Some j)
(* DEX
    | invokevirtual_caught : forall i mid t e,
      In e ((throwableAt m i)++throwableBy p (snd mid)) -> 
      handler i e = Some t ->
      step i (Invokevirtual mid) (Some e) (Some t)
    | invokevirtual_uncaught : forall i mid e,
      In e ((throwableAt m i)++throwableBy p (snd mid)) -> 
      handler i e = None ->
      step i (Invokevirtual mid) (Some e) None
*)
*)
    | JVM_lookupswitch : forall i d l o,
      In o (d::@map _ _ (@snd _ _) l) ->
      JVM_step i (JVM_Lookupswitch d l) None (Some (JVM_OFFSET.jump i o))
(* DEX Object
    | new : forall i c j,
      next m i = Some j ->
      JVM_step i (New c) None (Some j)
    | newarray : forall i t j,
      next m i = Some j ->
      JVM_step i (Newarray t) None (Some j)
*)
(* DEX Exception
    | newarray_nase_caught : forall i t te,
      In nase (throwableAt m i) ->
      handler i nase = Some te ->
      step i (Newarray t) (Some nase) (Some te)
    | newarray_nase_uncaught : forall i t,
      In nase (throwableAt m i) ->
      handler i nase = None ->
      step i (Newarray t) (Some nase) None
*)
    | JVM_nop : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Nop None (Some j)
    | JVM_pop : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Pop None (Some j)
    | JVM_pop2 : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Pop2 None (Some j)
(* DEX Object
    | putfield : forall i f j,
      next m i = Some j ->
      JVM_step i (Putfield f) None (Some j)
*)
(* DEX Exception
    | putfield_np_caught : forall i t f,
      In np (throwableAt m i) ->
      handler i np = Some t ->
      step i (Putfield f) (Some np) (Some t)
    | putfield_np_uncaught : forall i f,
      In np (throwableAt m i) ->
      handler i np = None ->
      step i (Putfield f) (Some np) None
*)
    | JVM_return_ : forall i,
      JVM_step i JVM_Return None None
    | JVM_swap : forall i j,
      next m i = Some j ->
      JVM_step i JVM_Swap None (Some j)
    | JVM_tableswitch : forall i d lo hi l o,
      In o (d::l) ->
      JVM_step i (JVM_Tableswitch d lo hi l) None (Some (JVM_OFFSET.jump i o))
(* DEX Object
    | vaload : forall i t j,
      next m i = Some j ->
      JVM_step i (Vaload t)  None (Some j)
*)
(* DEX Exception
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
*)
(* DEX Object
    | vastore : forall i t j,
      next m i = Some j ->
      JVM_step i (Vastore t) None (Some j)
*)
(* DEX Exception
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
*)
    | JVM_vload : forall i t x j,
      next m i = Some j ->
      JVM_step i (JVM_Vload t x) None (Some j)
    | JVM_vstore : forall i t x j,
      next m i = Some j ->
      JVM_step i (JVM_Vstore t x) None (Some j)
    | JVM_vreturn : forall i x,
      JVM_step i (JVM_Vreturn x) None None.

    Definition get_steps (i:JVM_PC) (ins:JVM_Instruction) (next:option JVM_PC): list (JVM_tag * option JVM_PC) := 
      match ins with
        (* DEX | Arraylength => (None,next)::nil (* DEX ::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *)*)
        (* DEX | Athrow => map (fun e => (Some e,handler i e)) (throwableAt m i) *)
        (* DEX | Checkcast _ => (None,next)::(Some cc,handler i cc)::nil *)
        (* DEX | Getfield _ => (None,next)::nil(* DEX ::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *) *)
        | JVM_Ibinop op => (None,next)::nil(* DEX ::
          (match op with
             | DivInt =>map (fun e => (Some e,handler i e)) (throwableAt m i)
             | RemInt => map (fun e => (Some e,handler i e)) (throwableAt m i)
             | _ => nil
           end) *)
(* DEX Method
        | Invokestatic mid => 
          (None,next)::nil (* DEX ::(map (fun e => (Some e,handler i e)) ((throwableAt m i)++throwableBy p (snd mid))) *)
        | Invokevirtual mid =>
          (None,next)::nil (* DEX ::(map (fun e => (Some e,handler i e)) ((throwableAt m i)++throwableBy p (snd mid))) *)
*)
        | JVM_Lookupswitch d l =>
          map (fun o => (None,Some (JVM_OFFSET.jump i o))) (d::@map _ _ (@snd _ _) l)
(* DEX Object
        | Newarray _ =>  (None,next)::nil (* DEX ::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *)
        | Putfield _ => (None,next)::nil (* DEX ::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *)
*)
        | JVM_Return => (None,None)::nil
        | JVM_Tableswitch d lo hi l =>
          map (fun o => (None,Some (JVM_OFFSET.jump i o))) (d::l) 
(* DEX Object
        | Vaload _ => (None,next)::nil (* ::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *)
        | Vastore _ => (None,next)::nil (*::(map (fun e => (Some e,handler i e)) (throwableAt m i)) *)
*)
        | JVM_Vreturn _ => (None,None)::nil
        | JVM_Goto o => (None,Some (JVM_OFFSET.jump i o))::nil
(* DEX Object        | If_acmp cmp o => (None,next)::(None,Some (JVM_OFFSET.jump i o))::nil*)
        | JVM_If_icmp cmp o => (None,next)::(None,Some (JVM_OFFSET.jump i o))::nil
        | JVM_If0 cmp o => (None,next)::(None,Some (JVM_OFFSET.jump i o))::nil
(* DEX Object        | Ifnull cmp o => (None,next)::(None,Some (JVM_OFFSET.jump i o))::nil*)
        | _ => (None,next)::nil
      end.

    Lemma all_step_in_get_steps : forall i ins tau oj,
        JVM_step i ins tau oj -> 
        In (tau,oj) (get_steps i ins (next m i)).
    Proof.
      intros.
      inversion_clear H; simpl get_steps; try rewrite H0; auto with datatypes;
      (* DEX try match goal with
        [ id : handler _ _ = ?x |- _ ] => 
        pattern x at 1; rewrite <- id
          end; *)
      try (
        repeat ((left; reflexivity)||right);
          try match goal with
                [ |- In (_,_) (map ?F _) ] => 
                apply in_map with (f:=F); try assumption;
                  apply in_or_app; auto
              end; fail).
(* DEX
      right;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
      apply in_map with (f:=F); try assumption
      end.
      destruct H0; subst; simpl; auto with datatypes;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
            apply in_map with (f:=F); try assumption
      end.
      right; destruct H; subst; simpl; auto with datatypes;
      try match goal with
      [ |- In (_,_) (map ?F _) ] => 
            apply in_map with (f:=F); try assumption
      end.
*)
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
(*
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
      destruct H0 as [H0|H0]; rewrite <- H0; auto with datatypes.
*)
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
    Variable test : JVM_PC -> JVM_Instruction -> JVM_tag -> option JVM_PC -> bool.

    Definition for_all_steps_bm (bm:JVM_BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:JVM_Instruction*(option JVM_PC*list JVM_ClassName)) =>
        let (ins,next) := ins_next in
          for_all _
          (fun (tau_oj:JVM_tag*option JVM_PC) => let (tau,oj):=tau_oj in test i ins tau oj)
          (get_steps i ins (fst next)))
      bm.(JVM_BYTECODEMETHOD.instr).

    Lemma for_all_steps_bm_true : forall bm,
      JVM_METHOD.body m = Some bm ->
      for_all_steps_bm bm = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        JVM_step i ins tau oj -> test i ins tau oj = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, JVM_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (JVM_Instruction * (option JVM_PC*list JVM_ClassName)) (JVM_BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      apply for_all_true with
        (test:=(fun tau_oj : JVM_tag * option JVM_PC =>
          let (tau, oj) := tau_oj in test i ins tau oj))
        (2:=T2).
      unfold next, JVM_BYTECODEMETHOD.nextAddress.
      rewrite H; rewrite T3; simpl.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

  Definition for_all_steps_m : bool :=
    match JVM_METHOD.body m with
      | None => false
      | Some bm => for_all_steps_bm bm
    end.

  Definition test_all_steps_m : list (JVM_PC*bool) :=
    match JVM_METHOD.body m with
      | None => nil
      | Some bm => 
      List.map
      (fun (ins_next:JVM_PC*(JVM_Instruction*(option JVM_PC*list JVM_ClassName))) =>
        let (i,ins_next) := ins_next in
        let (ins,next) := ins_next in
          (i,for_all _
            (fun (tau_oj:JVM_tag*option JVM_PC) => let (tau,oj):=tau_oj in test i ins tau oj)
            (get_steps i ins (fst next))))
      (MapN.elements _ bm.(JVM_BYTECODEMETHOD.instr))
    end.

  Lemma for_all_steps_m_true : for_all_steps_m = true ->
      forall i ins tau oj,
        instructionAt m i = Some ins ->
        JVM_step i ins tau oj -> test i ins tau oj = true.
  Proof.
    unfold for_all_steps_m.
    generalize for_all_steps_bm_true.
    destruct (JVM_METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.

  End for_all_steps.

  Section for_all_succs.
    Variable pc:JVM_PC.
    Variable test : JVM_tag -> option JVM_PC -> bool.

    Definition for_all_succs_bm (bm:JVM_BytecodeMethod) : bool :=
      match MapN.get _ bm.(JVM_BYTECODEMETHOD.instr) pc with
        | None => true
        | Some (ins,(op,l)) => 
          for_all _
          (fun (tau_oj:JVM_tag*option JVM_PC) => let (tau,oj):=tau_oj in test tau oj)
          (get_steps pc ins op)
      end.

    Lemma for_all_succs_bm_true : forall bm,
      JVM_METHOD.body m = Some bm ->
      for_all_succs_bm bm = true ->
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        JVM_step pc ins tau oj -> test tau oj = true.
    Proof.
      unfold for_all_succs_bm; intros.
      assert (T2:=all_step_in_get_steps _ _ _ _ H2).
      unfold instructionAt, JVM_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (JVM_Instruction * (option JVM_PC*list JVM_ClassName)) (JVM_BYTECODEMETHOD.instr bm) pc).
      intros (ins0,next0) T3.
      rewrite T3 in H1; rewrite T3 in H0.
      destruct next0.
      apply for_all_true with
        (test:=(fun tau_oj : JVM_tag * option JVM_PC =>
          let (tau, oj) := tau_oj in test tau oj))
        (2:=T2).
      unfold next, JVM_BYTECODEMETHOD.nextAddress.
      inversion_mine H1.
      rewrite H; rewrite T3; simpl; auto.
      intros.
      rewrite H3 in H1; discriminate.
    Qed.

  Definition for_all_succs_m : bool :=
    match JVM_METHOD.body m with
      | None => false
      | Some bm => for_all_succs_bm bm
    end.

  Lemma for_all_succs_m_true : for_all_succs_m = true ->
      forall ins tau oj,
        instructionAt m pc = Some ins ->
        JVM_step pc ins tau oj -> test tau oj = true.
  Proof.
    unfold for_all_succs_m.
    generalize for_all_succs_bm_true.
    destruct (JVM_METHOD.body m) as [bm|]; intro.
    apply H; auto.
    intros; discriminate.
  Qed.
   
 End for_all_succs.

  Section for_all_instrs.
    Variable test : JVM_PC -> JVM_Instruction -> bool.

    Definition for_all_instrs_bm (bm:JVM_BytecodeMethod) : bool :=
      MapN.for_all _
      (fun i (ins_next:JVM_Instruction*(option JVM_PC*list JVM_ClassName)) =>
        let (ins,next) := ins_next in test i ins)
      bm.(JVM_BYTECODEMETHOD.instr).

    Lemma for_all_instrs_bm_true : forall bm,
      JVM_METHOD.body m = Some bm ->
      for_all_instrs_bm bm = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      intros.
      assert (T1:=MapN.for_all_true _ _ _ H0).
      unfold instructionAt, JVM_BYTECODEMETHOD.instructionAt in H1.
      rewrite H in H1.
      caseeq (MapN.get (JVM_Instruction * (option JVM_PC*list JVM_ClassName)) (JVM_BYTECODEMETHOD.instr bm) i).
      intros (ins0,next0) T3.
      rewrite T3 in H1.
      generalize (T1 _ _ T3); clear T1; intros T1.
      inversion_mine H1; auto.
      intros T3; rewrite T3 in H1; discriminate.
    Qed.

    Definition for_all_instrs_m : bool :=
      match JVM_METHOD.body m with
        | None => false
        | Some bm => for_all_instrs_bm bm
      end.

    Lemma for_all_instrs_m_true : for_all_instrs_m = true ->
      forall i ins,
        instructionAt m i = Some ins -> test i ins = true.
    Proof.
      unfold for_all_instrs_m.
      generalize for_all_instrs_bm_true.
      destruct (JVM_METHOD.body m) as [bm|]; intro.
      apply H; auto.
      intros; discriminate.
    Qed.

  End for_all_instrs.

End JVM_S_section.

Module JVM_MapClassTools := MapProjTools JVM_PROG.JVM_MapClass.

Section p.
  Variable p : JVM_Program.

  Definition ValidMethod (m:JVM_Method) : Prop :=
    exists c, JVM_PROG.defined_Class p c /\ JVM_CLASS.defined_Method c m.

  Variable test : JVM_Method -> bool.

  Definition for_all_methods : bool :=
    JVM_MapClassTools.for_all
    (fun cl =>  JVM_MapShortMethSign.for_all _ (fun _ => test) cl.(JVM_CLASS.methods))
    p.(JVM_PROG.classes_map).

  Lemma for_all_methods_true : for_all_methods = true ->
    forall m, ValidMethod m -> test m = true.
  Proof.
    intros.
    destruct H0 as [c [H0 H1]].
    generalize (JVM_MapClassTools.for_all_true _ _ H _ H0); intros.
    unfold JVM_CLASS.defined_Method, JVM_CLASS.method in H1.
    caseeq (JVM_MapShortMethSign.get JVM_Method (JVM_CLASS.methods c) (JVM_METHOD.signature m)); intros.
    rewrite H3 in H1.
    destruct (JVM_METHODSIGNATURE.eq_t (JVM_METHOD.signature m) (JVM_METHOD.signature j)); inversion_mine H1.
    apply (JVM_MapShortMethSign.for_all_true _ _ _ H2 _ _ H3).
    rewrite H3 in H1; discriminate.
  Qed.

End p.


  




