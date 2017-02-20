(** BigStepAnnot.v: We constrain the Bicolano bigstep semantics to handle only the executions where exception thrown at a given point are in a predefined set. Such a set could be computed for example with a CHA static analysis. *)
(* Hendra : - Modified to suit DEX program. 
            - Also trim the system to contain only Arithmetic *)
Require Export List.
Require Export ZArith.
Require Export LoadBicolano.

Inductive compat_op (A B:Set) : option A -> option B -> Prop :=
  compat_op_none : compat_op A B None None
| compat_op_some : forall k v, compat_op A B (Some k) (Some v).
Implicit Arguments compat_op [A B].


Module DEX_BigStepAnnot.

Import DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.



  Set Implicit Arguments.
  Section DEX_instr.

  Inductive DEX_exec_intra (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
    DEX_NormalStep p m s1 s2 ->
    DEX_exec_intra p m (* None *) s1 s2.

  Inductive DEX_exec_return (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | exec_return_normal : forall s ov,
     DEX_ReturnStep p m s (Normal ov) ->
     DEX_exec_return p m s (Normal ov).

 Inductive DEX_IntraStep (p:DEX_Program) : 
    DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop :=
  | IntraStep_res :forall m s ret,
     DEX_exec_return p m s ret ->
     DEX_IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2,
     DEX_exec_intra p m s1 s2 ->
     DEX_IntraStep p m s1 (inl _ s2).
 
 Definition DEX_IntraStepStar p m s r := TransStep_l (DEX_IntraStep p m) s r.

 Definition DEX_IntraStepStar_intra p m s s' := DEX_IntraStepStar p m s (inl _ s').

 Definition DEX_BigStep  p m s ret := DEX_IntraStepStar p m s (inr _ ret).

  Lemma DEX_IntraStep_ind_ : 
      forall (p:DEX_Program) 
        (P:DEX_Method->DEX_IntraNormalState->DEX_IntraNormalState+DEX_ReturnState->Prop),
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
       intros prg Q H0 Hr Hi Hcr Hc.
       fix intra 2;intros r Hs;case Hs;clear r Hs;intros.
       eapply Hr; eauto.
       apply Hi with s2;trivial. 
     Qed.

  Lemma DEX_IntraStepStar_ind : 
    forall (p:DEX_Program) 
     (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop),
       (forall m s, P m s (inl _ s)) ->
       (forall m s r, DEX_exec_return p m s r -> P m s (inr _ r)) ->
       (forall m s s' , DEX_exec_intra p m s s' -> 
          forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
          P m s r) ->
    forall m s r, DEX_IntraStepStar p m s r -> P m s r.
   Proof.
     intros p Q H0 Hr Hi.
     fix fixp 4;intros m s' s Ht;case Ht;clear Ht s' s;intros.
     apply H0.
     generalize (DEX_IntraStep_ind_ Q H0 Hr Hi H).
     case r;intros;trivial.
     apply H1;trivial. 
     constructor.
     assert (HH:=DEX_IntraStep_ind_ Q H0 Hr Hi H);simpl in HH.
     apply HH;trivial.   
     apply fixp;trivial.
   Qed.

End DEX_instr.
 
End DEX_BigStepAnnot.