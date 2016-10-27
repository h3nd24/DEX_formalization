(** * Bicolano: Big step (interface implementation) *)

(* <Insert License Here>

    $Id: BigStep.v 68 2006-02-02 15:06:27Z davidpichardie $ *)

(** Big step semantics.

 @author David Pichardie *)

(* Hendra : - Modified to suit DEX program. 
            - Also trim the system to contain only Arithmetic *)

Require Export DEX_BigStepType.
Require Export DEX_ImplemDomain.

Open Scope type_scope.

Module DEX_BigStep <: DEX_BIGSTEP.
 
  Module DEX_Dom := DEX_ImplemDomain.DEX_Dom.
 
  (* Inductive definition are put in BigStepLoad.v.
     They are shared with BigStepType.v *)
  Load "DEX_BigStepLoad.v".
 
  Lemma IntraStep_ind_ : 
      forall (p:DEX_Program) (P:DEX_Method->DEX_IntraNormalState->DEX_IntraNormalState+DEX_ReturnState->Prop),
         (forall m s, P m s (inl _ s)) ->
         (forall m s r, DEX_exec_return p m s r -> P m s (inr _ r)) ->
         (forall m s s' , DEX_exec_intra p m s s' -> 
            forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
            P m s r) ->
      forall m s r, DEX_IntraStep p m s r -> 
        match r with
        | inr r' => P m s (inr _ r')
        | inl s' => forall r', DEX_IntraStepStar p m s' r' -> P m s' r' -> P m s r'
        end.
     Proof.
       intros p P H0 Hr Hi Hcr Hc.
       fix intra 2;intros r Hs;case Hs;clear r Hs;intros.
       apply Hr;trivial.
       apply Hi with s2;trivial. 
     Qed.

  Lemma IntraStepStar_ind : 
    forall (p:DEX_Program) 
     (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop),
       (forall m s, P m s (inl _ s)) ->
       (forall m s r, DEX_exec_return p m s r -> P m s (inr _ r)) ->
       (forall m s s' , DEX_exec_intra p m s s' -> 
          forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
          P m s r) ->
    forall m s r, DEX_IntraStepStar p m s r -> P m s r.
   Proof.
     intros p P H0 Hr Hi.
     fix fixp 4; intros m s' s Ht;case Ht;clear Ht s' s;intros.
     apply H0.
     generalize (IntraStep_ind_ p P H0 Hr Hi _ _ _ H).
     case r;intros;trivial.
     apply H1;trivial. constructor.
     assert (HH:=IntraStep_ind_  p P H0 Hr Hi _ _ _ H);simpl in HH.
     apply HH;trivial.   
     apply fixp;trivial.
   Qed.

  Lemma IntraStepStar_intra_ind : 
    forall (p:DEX_Program) 
     (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState -> Prop),
       (forall m s, P m s s) ->
       (forall m s s', DEX_exec_intra p m s s' -> 
          forall s'', DEX_IntraStepStar_intra p m s' s'' -> P m s' s'' ->
          P m s s'') ->
    forall m s s', DEX_IntraStepStar_intra p m s s' -> P m s s'.
   Proof.
     intros p P H0 Hi Hc.
     assert (forall m s r, DEX_IntraStepStar p m s r ->
              forall s', r = inl _ s' -> P m s s').
      induction 1 using IntraStepStar_ind;intros;try discriminate;subst;eauto.
      inversion H;auto.
     intros; eapply H; eauto. 
   Qed.

  Lemma BigStep_ind : 
    forall (p:DEX_Program) 
     (P : DEX_Method -> DEX_IntraNormalState -> DEX_ReturnState -> Prop),
       (forall m s r, DEX_exec_return p m s r -> P m s r) ->
       (forall m s s' , DEX_exec_intra p m s s' -> 
          forall r, DEX_BigStep p m s' r -> P m s' r ->
          P m s r) ->
    forall m s r, DEX_BigStep p m s r -> P m s r.
  Proof.
   intros p P Hr Hi Hcr Hc.
   assert (forall m s R, DEX_IntraStepStar p m s R -> forall r, R = inr _ r -> P m s r).
   induction 1 using IntraStepStar_ind;intros r0 Heq;try inversion Heq;subst;
    try (eauto;fail).
   intros;eapply H;eauto. 
  Qed.

  Lemma ReachableStar_ind : 
    forall (p:DEX_Program) 
     (P : (DEX_Method * DEX_IntraNormalState) -> (DEX_Method * DEX_IntraNormalState) -> Prop),
       (forall m s, P (m,s) (m,s)) ->
       (forall m s s', DEX_exec_intra p m s s' -> 
          forall m' s'', ClosReflTrans (DEX_ReachableStep p) (m,s') (m',s'') -> 
          P (m,s') (m',s'') ->
          P (m,s) (m',s'')) ->
    forall ms ms', 
       ClosReflTrans (DEX_ReachableStep p) ms ms' -> P ms ms'.
   Proof.
     intros p P H0 Hi Hc Hsc.
     induction 1;intros.
     destruct a;eauto.
     destruct a'' as (m'',s'').
     inversion H;subst;eauto.
     inversion H2;clear H2;subst;eauto.
   Qed.

End DEX_BigStep.