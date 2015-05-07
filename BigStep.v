(** * Bicolano: Big step (interface implementation) *)

(* <Insert License Here>

    $Id: BigStep.v 68 2006-02-02 15:06:27Z davidpichardie $ *)

(** Big step semantics.

 @author David Pichardie *)

Require Export BigStepType.
Require Export ImplemDomain.

Open Scope type_scope.

Module BigStep <: BIGSTEP.
 
  Module Dom := ImplemDomain.Dom.
 
  (* Inductive definition are put in BigStepLoad.v.
     They are shared with BigStepType.v *)
  Load "BigStepLoad.v".
 
  Lemma IntraStep_ind_ : 
      forall (p:Program) (P:Method->IntraNormalState->IntraNormalState+ReturnState->Prop),
         (forall m s, P m s (inl _ s)) ->
         (forall m s r, exec_return p m s r -> P m s (inr _ r)) ->
         (forall m s s' , exec_intra p m s s' -> 
            forall r, IntraStepStar p m s' r -> P m s' r ->
            P m s r) ->
         (forall m s s' ret m' r, 
            exec_call p m s ret m' s' (inr _ r) ->
            IntraStepStar p m' s' (inr _ ret) ->
            P m' s' (inr _ ret) ->
            P m s (inr _ r)) ->
         (forall m s s' ret m' s'' r, 
            exec_call p m s ret m' s' (inl _ s'') ->
            IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
            IntraStepStar p m s'' r -> P m s'' r ->
            P m s r) ->
      forall m s r, IntraStep p m s r -> 
        match r with
        | inr r' => P m s (inr _ r')
        | inl s' => forall r', IntraStepStar p m s' r' -> P m s' r' -> P m s r'
        end.
     Proof.
       intros p P H0 Hr Hi Hcr Hc.
       fix intra 4;intros m s r Hs;case Hs;clear m s r Hs;intros.
       apply Hr;trivial.
       apply Hi with s2;trivial. 
       assert (P m' s' (inr IntraNormalState ret')).
       generalize s' (inr IntraNormalState ret') H1;clear H1 H m s1 s' ret' r.
       fix fixp 3;intros s' s Ht;case Ht;clear Ht s' s;intros.
       apply H0.
       generalize (intra _ _ _ H);clear H;case r;intros.
       apply H;trivial. constructor. trivial. 
       assert (HH:= intra _ _ _ H);simpl in HH.
       apply HH;trivial. apply fixp;trivial.
       generalize H;clear H;case r.
       intros s'' Hcall r' Hint HP.
       eapply Hc;eauto.
       intros r' Hcall;eapply Hcr;eauto.
     Qed.

  Lemma IntraStepStar_ind : 
    forall (p:Program) 
     (P : Method -> IntraNormalState -> IntraNormalState + ReturnState -> Prop),
       (forall m s, P m s (inl _ s)) ->
       (forall m s r, exec_return p m s r -> P m s (inr _ r)) ->
       (forall m s s' , exec_intra p m s s' -> 
          forall r, IntraStepStar p m s' r -> P m s' r ->
          P m s r) ->
       (forall m s s' ret m' r, 
          exec_call p m s ret m' s' (inr _ r) ->
          IntraStepStar p m' s' (inr _ ret) ->
          P m' s' (inr _ ret) ->
          P m s (inr _ r)) ->
       (forall m s s' ret m' s'' r, 
          exec_call p m s ret m' s' (inl _ s'') ->
          IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
          IntraStepStar p m s'' r -> P m s'' r ->
          P m s r) ->
    forall m s r, IntraStepStar p m s r -> P m s r.
   Proof.
     intros p P H0 Hr Hi Hcr Hc.
     fix fixp 4;intros m s' s Ht;case Ht;clear Ht s' s;intros.
     apply H0.
     generalize (IntraStep_ind_ p P H0 Hr Hi Hcr Hc _ _ _ H).
     case r;intros;trivial.
     apply H1;trivial. constructor.
     assert (HH:=IntraStep_ind_  p P H0 Hr Hi Hcr Hc _ _ _ H);simpl in HH.
     apply HH;trivial.   
     apply fixp;trivial.
   Qed.

  Lemma IntraStepStar_intra_ind : 
    forall (p:Program) 
     (P : Method -> IntraNormalState -> IntraNormalState -> Prop),
       (forall m s, P m s s) ->
       (forall m s s', exec_intra p m s s' -> 
          forall s'', IntraStepStar_intra p m s' s'' -> P m s' s'' ->
          P m s s'') ->
       (forall m s s1 ret m' s2 s3, 
          exec_call p m s ret m' s1 (inl _ s2) ->
          BigStep p m' s1 ret -> 
          IntraStepStar_intra p m s2 s3 -> P m s2 s3 ->
          P m s s3) ->
    forall m s s', IntraStepStar_intra p m s s' -> P m s s'.
   Proof.
     intros p P H0 Hi Hc.
     assert (forall m s r, IntraStepStar p m s r ->
              forall s', r = inl _ s' -> P m s s').
      induction 1 using IntraStepStar_ind;intros;try discriminate;subst;eauto.
      inversion H;auto.
     intros; eapply H; eauto. 
   Qed.

  Lemma BigStep_ind : 
    forall (p:Program) 
     (P : Method -> IntraNormalState -> ReturnState -> Prop),
       (forall m s r, exec_return p m s r -> P m s r) ->
       (forall m s s' , exec_intra p m s s' -> 
          forall r, BigStep p m s' r -> P m s' r ->
          P m s r) ->
       (forall m s s' ret m' r, 
          exec_call p m s ret m' s' (inr _ r) ->
          BigStep p m' s' ret ->
          P m' s' ret ->
          P m s r) ->
       (forall m s s' ret m' s'' r, 
          exec_call p m s ret m' s' (inl _ s'') ->
          BigStep p m' s' ret -> P m' s' ret ->
          BigStep p m s'' r -> P m s'' r ->
          P m s r) ->
    forall m s r, BigStep p m s r -> P m s r.
  Proof.
   intros p P Hr Hi Hcr Hc.
   assert (forall m s R, IntraStepStar p m s R -> forall r, R = inr _ r -> P m s r).
   induction 1 using IntraStepStar_ind;intros r0 Heq;try inversion Heq;subst;
    try (eauto;fail).
   intros;eapply H;eauto. 
  Qed.

  Lemma ReachableStar_ind : 
    forall (p:Program) 
     (P : (Method * IntraNormalState) -> (Method * IntraNormalState) -> Prop),
       (forall m s, P (m,s) (m,s)) ->
       (forall m s s', exec_intra p m s s' -> 
          forall m' s'', ClosReflTrans (ReachableStep p) (m,s') (m',s'') -> 
          P (m,s') (m',s'') ->
          P (m,s) (m',s'')) ->
       (forall m s s1 ret m' s2, 
          exec_call p m s ret m' s1 (inl _ s2) ->
          BigStep p m' s1 ret -> 
          forall m' s3, ClosReflTrans (ReachableStep p) (m,s2) (m',s3) -> 
          P (m,s2) (m',s3) ->
          P (m,s) (m',s3)) ->
       (forall m pc h l m' l' bm',
        CallStep p m (pc,(h,l)) (m',l') ->
        METHOD.body m' = Some bm' ->
        forall m'' s'', 
        ClosReflTrans (ReachableStep p) 
          (m', (BYTECODEMETHOD.firstAddress bm',(h, l')))
          (m'',s'') ->
        P (m', (BYTECODEMETHOD.firstAddress bm',(h, l')))
          (m'',s'') ->
        P (m, (pc,(h, l))) (m'',s'')) ->
    forall ms ms', 
       ClosReflTrans (ReachableStep p) ms ms' -> P ms ms'.
   Proof.
     intros p P H0 Hi Hc Hsc.
     induction 1;intros.
     destruct a;eauto.
     destruct a'' as (m'',s'').
     inversion H;subst;eauto.
     inversion H2;clear H2;subst;eauto.
   Qed.

End BigStep.

