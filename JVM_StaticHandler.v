(** * Bicolano: StaticHandler for exceptions *)

Require Export JVM_BigStep.

Module JVM_StaticHandler.
  
  Import JVM_BigStep.JVM_Dom.JVM_Prog.

  Section JVM_subclass_test.
    Variable p : JVM_Program.
    Variable JVM_subclass_test : JVM_ClassName -> JVM_ClassName -> bool.
    Variable JVM_subclass_test_correct :
      forall c1 c2,
        if JVM_subclass_test c1 c2 then subclass_name p c1 c2
          else ~ subclass_name p c1 c2.
(* DEX
    Fixpoint search_handler (pc:PC) (c:ClassName)
      (l:list ExceptionHandler) {struct l} : option ExceptionHandler :=
      match l with
        nil => None
        | h::q => 
          match EXCEPTIONHANDLER.catchType h with
            None => 
            (if EXCEPTIONHANDLER.isPCinRange h pc then Some h
              else search_handler pc c q)
            | Some ch => 
              if subclass_test c ch then
                (if EXCEPTIONHANDLER.isPCinRange h pc then Some h
                  else search_handler pc c q)
                else search_handler pc c q
          end
      end.

    Definition handler (m:Method) (pc:PC) (cl:ClassName) : option PC :=
      match METHOD.body m with
        None => None
        | Some bm =>
          match search_handler pc cl (BYTECODEMETHOD.exceptionHandlers bm) with
            None => None
            | Some h => Some (EXCEPTIONHANDLER.handler h)
          end
      end.

    Ltac caseeq t := generalize (refl_equal t); pattern t at -1 in |- * ; case t.

    Lemma lookup_handlers_search_handler : forall hs pc pc' cn,
      lookup_handlers p hs pc cn pc' ->
      exists hd, search_handler pc cn hs = Some hd
        /\ pc' = EXCEPTIONHANDLER.handler hd.
    Proof.
      induction hs; intros.
      inversion_clear H.
      inversion_clear H; simpl.
      exists a; split; auto.
      inversion_clear H0.
      rewrite H.
      rewrite H1.
      auto.
      rewrite H.
      generalize (subclass_test_correct cn cl1).
      destruct (subclass_test cn cl1); intros; try (intuition;fail).
      rewrite H1; auto.
      destruct (IHhs _ _ _ H1) as [hd [HH1 HH2]].
      caseeq (EXCEPTIONHANDLER.catchType a); intros.
      generalize (subclass_test_correct cn c).
      destruct (subclass_test cn c); intros; try (intuition;fail).
      caseeq (EXCEPTIONHANDLER.isPCinRange a pc); intros.
      elim H0; constructor 2 with c; auto.
      exists hd; auto.
      exists hd; auto.
      caseeq (EXCEPTIONHANDLER.isPCinRange a pc); intros.
      elim H0; constructor 1; auto.
      auto.
    Qed.

    Lemma search_handler_lookup_handlers : forall hs pc cn hd,
      search_handler pc cn hs = Some hd ->
      lookup_handlers p hs pc cn (EXCEPTIONHANDLER.handler hd).
    Proof.
      induction hs; simpl; intros.
      discriminate.
      generalize H; clear H.
      caseeq (EXCEPTIONHANDLER.catchType a); [intros c Hc|intros Hc].
      generalize (subclass_test_correct cn c).
      destruct (subclass_test cn c).
      caseeq (EXCEPTIONHANDLER.isPCinRange a pc); intros.
      injection H1; clear H1; intros; subst.
      constructor 1.
      constructor 2 with c; auto.
      constructor 2; eauto.
      intro.
      inversion_clear H2.
      rewrite Hc in H3; discriminate.
      rewrite H in H4; discriminate.
      intros; constructor 2; eauto.
      intro.
      inversion_clear H1.
      rewrite Hc in H2; discriminate.
      rewrite Hc in H2; injection H2; intros; subst.
      contradiction.
      caseeq (EXCEPTIONHANDLER.isPCinRange a pc); intros.
      injection H0; clear H0; intros; subst.
      constructor 1.
      constructor 1; auto.
      constructor 2; eauto.
      intro.
      inversion_clear H1.
      rewrite H in H3; discriminate.
      rewrite H in H3; discriminate.
    Qed.
*)
  End JVM_subclass_test.

End JVM_StaticHandler.

Module JVM_StaticHandlerProp.

  Import JVM_StaticHandler JVM_BigStep.JVM_BigStep JVM_Dom JVM_Prog.
  
  Section JVM_subclass_test.
    Variable p : JVM_Program.
    Variable JVM_subclass_test : JVM_ClassName -> JVM_ClassName -> bool.
    Variable JVM_subclass_test_correct :
      forall c1 c2,
        if JVM_subclass_test c1 c2 then subclass_name p c1 c2
          else ~ subclass_name p c1 c2.
(* DEX
    Lemma CaughtException_handler :
      forall m pc h loc pc' cn,
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        CaughtException p m (pc,h,loc) pc' ->
        handler subclass_test m pc cn = Some pc'.
    Proof.
      intros.
      inversion_clear H0.
      elim (lookup_handlers_search_handler p _ subclass_test_correct)
        with (1:=H3); intros hd [HH1 HH2].
      unfold handler.
      rewrite H1.
      rewrite H2 in H; inversion H; subst.
      rewrite HH1; auto.  
    Qed.

    Lemma handler_CaughtException :
      forall m pc h loc pc' cn,
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        handler subclass_test m pc cn = Some pc' ->
        CaughtException p m (pc,h,loc) pc'.
    Proof.
      intros until 1.
      unfold handler.
      case_eq (METHOD.body m); [intros bm Hbm|intros Hbm].
      case_eq (search_handler subclass_test pc cn (BYTECODEMETHOD.exceptionHandlers bm)); intros; try discriminate.
      constructor 1 with bm cn; auto.
      injection H1; clear H1; intros; subst.
      apply (search_handler_lookup_handlers p _ subclass_test_correct); auto.
      intros; discriminate.
    Qed.

    Lemma no_handler_no_CaughtException :
      forall m pc h loc cn,
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        handler subclass_test m pc cn = None ->
        forall pc', ~ CaughtException p m (pc,h,loc) pc'.
    Proof.
      red; intros.
      rewrite (CaughtException_handler m pc h loc pc' cn H H1) in H0; discriminate.
    Qed.

    Lemma no_CaughtException_no_handler :
      forall m pc h loc cn,
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        (forall pc', ~ CaughtException p m (pc,h,loc) pc') ->
        handler subclass_test m pc cn = None.
    Proof.
      intros.
      case_eq (handler subclass_test m pc cn); intros; auto.
      elim (H0 p0).
      eapply handler_CaughtException; eauto.
    Qed. 
*)
  End JVM_subclass_test.

End JVM_StaticHandlerProp.
