(* Require Export JVM_Framework. *)
(* Hendra : Used for method typability *)
Require Export JVM_step.
Require Export JVM_typing_rules.
Require Export cdr.

Import (*JVM_BigStepWithTypes*) JVM_BigStepAnnot.JVM_BigStepAnnot JVM_BigStep.JVM_BigStep JVM_Dom JVM_Prog.
Import Level.L.

(*
Definition ValidMethod (p:JVM_Program) (m:JVM_Method) : Prop :=
  exists c, JVM_PROG.defined_Class p c /\ JVM_CLASS.defined_Method c m.
*)

Definition step (p:JVM_Program) (*subclass_test*) : JVM_Method -> JVM_PC -> option JVM_ClassName -> option JVM_PC -> Prop := fun m pc tau opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ JVM_step (*p subclass_test*) m pc i tau opc.

Section hyps.
  Variable kobs: L.t.

  Definition Method := JVM_Method.
  Definition Tag := option JVM_ClassName.
  Variable p : JVM_ExtendedProgram.
  Notation step := (step p).
  Variable cdr : forall m, CDR (step m).
  Definition stacktype : Set := TypeStack.

  Record JVM_SignedMethod : Type := SM {JVM_unSign:JVM_Method; sign:JVM_sign}.
  Coercion JVM_unSign :  JVM_SignedMethod >-> JVM_Method.

  Inductive JVM_M : JVM_SignedMethod -> Prop :=
    M_def : forall (m:JVM_Method) sgn,
      (JVM_METHOD.isStatic m = true -> sgn = JVM_static_signature p (JVM_METHOD.signature m)) ->
      (JVM_METHOD.isStatic m = false -> exists k, sgn = JVM_virtual_signature p (JVM_METHOD.signature m) k) ->
      JVM_M (SM m sgn).

  Definition texec : forall m, JVM_sign -> (JVM_PC -> L.t) ->
    JVM_PC -> Tag -> stacktype -> option stacktype -> Prop :=
    fun m sgn se pc tau st ost =>
      exists i, texec sgn (region (cdr m)) se pc i tau st ost
        /\ instructionAt m pc = Some i.

End hyps.

Require check_cdr.
Module MapKind' := MapOption_Base Map2P(*ClassName*).
  
  Module MapKind <: MAP with Definition key := Tag := Map_Of_MapBase MapKind'.
  Module CheckCdr := check_cdr.Make MapN(*PC*) MapKind.

  Fixpoint map_from_list (l:list JVM_PC) : MapN.t bool :=
    match l with
      | nil => MapN.empty _
      | cons i l => MapN.update _ (map_from_list l) i true
    end.

  Definition upd_reg : 
    JVM_PC -> Tag -> list JVM_PC -> CheckCdr.M.t (MapN.t bool) -> CheckCdr.M.t (MapN.t bool) :=
    fun i kd l reg =>
      CheckCdr.M.update _ reg (i,kd) (map_from_list l).

  Definition empty_reg : CheckCdr.M.t (MapN.t bool) := CheckCdr.M.empty _.

  Definition upd_jun : 
    JVM_PC -> Tag -> JVM_PC -> MapN.t (MapKind.t CheckCdr.PC) -> MapN.t (MapKind.t CheckCdr.PC) :=
    fun i kd j jun =>     CheckCdr.M.update _ jun (i ,kd) j.

  Definition empty_jun : MapN.t (MapKind.t CheckCdr.PC) := MapN.empty _.
  
  Section check.
    Variable p : JVM_Program.
    Variable m : JVM_Method.
    Definition for_all_steps : (JVM_PC -> Tag -> option JVM_PC -> bool) -> bool :=
      fun test => for_all_steps_m m (fun pc i => test pc).
    Definition test_all_steps : (JVM_PC -> Tag -> option JVM_PC -> bool) 
      -> list (JVM_PC*bool) :=
      fun test => test_all_steps_m m (fun pc i => test pc).

    Lemma for_all_steps_true : forall test,
      for_all_steps test = true ->
      forall (i : JVM_PC) (tau : Tag) (oj : option JVM_PC),
        step p m i tau oj -> test i tau oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_steps_m_true m (fun p i => test p)); eauto.
    Qed.

    Definition for_all_succs : JVM_PC -> (Tag -> option JVM_PC -> bool) -> bool :=
      for_all_succs_m m.

    Lemma for_all_succs_true : forall i test,
      for_all_succs i test = true ->
      forall tau oj, step p m i tau oj -> test tau oj = true.
    Proof.
      intros.
      destruct H0 as [T0 [ins [T1 T2]]].
      eapply (for_all_succs_m_true m); eauto.
    Qed.

    Definition check_cdr : forall
      (reg : CheckCdr.M.t (MapN.t bool))
      (jun : MapN.t (MapKind.t CheckCdr.PC)), bool :=
      fun reg jun => CheckCdr.check_soaps for_all_steps for_all_succs reg jun.

    Definition check_cdr' 
      (reg : CheckCdr.M.t (MapN.t bool))
      (jun : MapN.t (MapKind.t CheckCdr.PC)) :=
      CheckCdr.check_soaps' for_all_steps for_all_succs reg jun.

    Definition check_soap1' 
      (reg : CheckCdr.M.t (MapN.t bool))
      (jun : MapN.t (MapKind.t CheckCdr.PC)) :=
      CheckCdr.check_soap1' test_all_steps reg jun.

    Definition test_soap2
      (reg : CheckCdr.M.t (MapN.t bool))
      (jun : MapN.t (MapKind.t CheckCdr.PC)) :=
      CheckCdr.test_soap2 for_all_succs reg jun.

    Lemma check_cdr_prop : forall 
      (reg : CheckCdr.M.t (MapN.t bool))
      (jun : MapN.t (MapKind.t CheckCdr.PC)),
      check_cdr reg jun = true ->
      { cdr : CDR (step p m) |
        forall i tau j,
          region cdr i tau j -> CheckCdr.region reg i tau j}.
    Proof
    (CheckCdr.check_soap_true (step p m) for_all_steps (*(fun _ => nil)*)
      for_all_steps_true
      for_all_succs for_all_succs_true).

  End check.

(* There was correctness check here *)
(*

  Section CDR_dummy.

    Variable PC Kind: Set.
    Variable step : PC -> Kind -> option PC -> Prop.

    Definition dummy_cdr : CDR step.
    refine (make_CDR (fun _ _ _ => True) (fun _ _ _ => False) _ _ _ _); auto.
    intuition.
  Qed.

End CDR_dummy.
*)

Section CheckTypable.

  Variable p : JVM_ExtendedProgram.
  Variable se : (*JVM_Method -> JVM_sign ->*) JVM_PC -> L.t.
  Variable reg : (*JVM_Method ->*) CheckCdr.M.t (MapN.t bool).
  Variable jun : (*JVM_Method ->*) MapN.t (MapKind.t CheckCdr.PC).
  Variable S :  (*JVM_Method -> JVM_sign ->*) JVM_PC -> list L.t'.
(*  Variable subclass_test : JVM_ClassName -> JVM_ClassName -> bool. *)
  Variable cdr_checked : forall m,
    check_cdr m (reg) (jun) = true.

  Definition cdr_local : forall m, 
    CDR (step p m) :=
    fun m => let (cdr_local,_) := 
      check_cdr_prop p m (reg) (jun)
      (cdr_checked m) in cdr_local.

  Definition for_all_region : (*JVM_Method -> *)JVM_PC -> JVM_tag -> (JVM_PC->bool) -> bool :=
    (*fun m => *) CheckCdr.for_all_region2 (reg).

  Lemma for_all_region_correct : forall i k test,
    for_all_region i k test = true ->
    forall j, CheckCdr.region (reg) i k j -> test j = true.
  Proof.
    unfold for_all_region; intros.
    eapply CheckCdr.for_all_region2_true; eauto.
  Qed.

  Lemma cdr_prop : forall m,
    forall i tau j,
      region (cdr_local m) i tau j -> CheckCdr.region (reg) i tau j.
  Proof.
    intros m h; unfold cdr_local.
    destruct check_cdr_prop.
    auto.
  Qed.

  Definition selift (*m sgn*) i (tau:JVM_tag) k :=
    for_all_region (*m*) i tau (fun j => L.leql_t k (se (*m sgn*) j)).

  Definition check_st0 m (*sgn*) : bool :=
    match JVM_METHOD.body m with
      | None => false
      | Some bm => match S (*m sgn*) (JVM_BYTECODEMETHOD.firstAddress bm) with
                     | nil => true
                     | _ => false
                   end
    end.
  
  Definition check_m m test :=
    if JVM_METHOD.isStatic m then test m (JVM_static_signature p (JVM_METHOD.signature m))
          else for_all _ (fun k => test m (JVM_virtual_signature p (JVM_METHOD.signature m) k)) L.all
    .
  
  Definition check m : bool := check_m m 
    (fun m sgn =>
      (check_st0 m (*sgn*)) &&
      for_all_steps_m (*p subclass_test*) m
      (fun i ins tag oj => 
        JVM_tcheck (*p subclass_test*) m sgn (se (*m sgn*)) (selift (*m sgn*)) (S (*m sgn*)) i ins)
    ).
(*
  Lemma check_correct2 : forall m, check m = true ->
    forall sgn ,
      forall i kd,
        step p m i kd None ->
        texec sgn se i kd (S m sgn i) None.
  Proof.
    unfold check; intros.
    assert (T:=for_all_P_true _ _ H _ _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    exists ins; split; [idtac|assumption].
    assert (T':=for_all_steps_m_true _ _ _ _ TT _ _ _ _ H2 H3).
    apply tcheck_correct1 with (selift:=selift m sgn); auto.
    unfold selift; intros.
    generalize (for_all_region_correct _ _ _ _ H1 _ (cdr_prop _ _ _ _ _ H4)).
    intros C; generalize (L.leql_t_spec k (se m sgn j)); rewrite C; auto.
  Qed.
*)

  Inductive sub : stacktype -> stacktype -> Prop :=
  | sub_nil : sub nil nil
  | sub_cons : forall x1 x2 st1 st2,
    L.leql' x1 x2 -> sub st1 st2 -> sub (x1::st1) (x2::st2).

  Lemma tsub_sub : forall st1 st2,
    tsub_st st1 st2 = true -> sub st1 st2.
  Proof.
    induction st1; destruct st2; simpl; intros; try discriminate.
    constructor.
    elim andb_prop with (1:=H); intros.
    constructor; auto.
    generalize (leql'_test_prop a t0); rewrite H0; auto.
    (*generalize (leql'_test_prop a t); rewrite H0; auto.*)
  Qed.

  Lemma check_m_true : forall m (test : JVM_METHOD.t -> JVM_sign -> bool), 
    check_m m test = true -> 
    forall sgn, JVM_M p (SM m sgn) ->
    test m sgn = true.
  Proof.
    unfold check_m; intros.
    inversion_mine H0.
    (*generalize (for_all_methods_true _ _ H _ H3).*)
    caseeq (JVM_METHOD.isStatic m); intros.
    rewrite H0 in H.
    apply H3 in H0. rewrite H0; auto.
    rewrite H0 in H.
    generalize (for_all_true _ _ _ H); intros.
    elim H4; auto.
    intros k Hk.
    rewrite Hk. apply H1.
    apply L.all_in_all.
  Qed.

  Lemma check_correct3 : forall m, check m = true ->
    forall sgn (h:JVM_M p (SM m sgn)),
      forall i j kd,
        step p m i kd (Some j) ->
        exists st,
          texec p cdr_local m sgn (se) i kd (S i) (Some st) 
          /\ sub st (S j).
  Proof.
    unfold check; intros.
    assert (T:=check_m_true _ _ H _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].

    assert (T':=for_all_steps_m_true _ _ TT _ _ _ _ H2 H3).
    elim tcheck_correct2 with 
      (se:=se) (region:=region (cdr_local m)) (sgn:=sgn) (m:=m)
      (selift:=selift) (S:=S) (i:=i) (ins:=ins) (tau:=kd) (j:=j)
      (2:=T') (3:=H3).
    intros st [T1 T2].
    exists st; split.
    exists ins; split; auto.
    apply tsub_sub; auto.
    unfold selift; intros.
    assert (T2:=for_all_region_correct _ _ _ H1).
    apply cdr_prop in H4.
    apply T2 in H4.
    generalize (L.leql_t_spec k (se j0)).
    rewrite H4; auto.
  Qed.

  Lemma check_correct2 : forall m, check m = true ->
    forall sgn (h:JVM_M p (SM m sgn)),
      forall i kd,
        step p m i kd None ->
        texec p cdr_local m sgn se i kd (S i) None.
  Proof.
    unfold check; intros.
    assert (T:=check_m_true _ _ H _ h).
    destruct (andb_prop _ _ T) as [_ TT].
    destruct H0 as [H0 [ins [H2 H3]]].
    exists ins; split; [idtac|assumption].
    assert (T':=for_all_steps_m_true _ _ TT _ _ _ _ H2 H3).
    apply tcheck_correct1 with (selift:=selift) (m:=m); auto.
  Qed.

(* There was correctness check here *)
End CheckTypable.
