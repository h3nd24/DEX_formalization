(** BigStepAnnot.v: We constrain the Bicolano bigstep semantics to handle only the executions where exception thrown at a given point are in a predefined set. Such a set could be computed for example with a CHA static analysis. *)
Require Export List.
Require Export ZArith.
Require Export LoadBicolano.

Inductive compat_op (A B:Set) : option A -> option B -> Prop :=
  compat_op_none : compat_op A B None None
| compat_op_some : forall k v, compat_op A B (Some k) (Some v).
Implicit Arguments compat_op [A B].


Module DEX_BigStepAnnot.

Import DEX_BigStep.DEX_BigStep DEX_StaticHandler.DEX_StaticHandler DEX_Dom DEX_Prog.



  Set Implicit Arguments.
  Section DEX_instr.
(*  Variable throwableAt : Method -> PC -> list ClassName.
  Variable throwableBy : ShortMethodSignature -> list ClassName.

  Inductive ExceptionStep (p:Program) : Method -> IntraNormalState -> IntraExceptionState -> Prop :=
  | athrow : forall h m pc s l loc cn,

    instructionAt m pc = Some Athrow ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    subclass_name p cn javaLangThrowable ->
    In cn (throwableAt m pc) -> (* Specific hypothesis here *)
    ExceptionStep p m (pc,(h,(Ref loc::s),l)) (h,loc)


  | jvm_exception : forall h m pc s l h' loc (e:ShortClassName),

    JVMExceptionStep p m (pc,(h,s,l)) e ->
    Heap.new h p (Heap.LocationObject (javaLang,e)) = Some (loc,h') ->
    In (javaLang,e) (throwableAt m pc) -> (* Specific hypothesis here *)

    ExceptionStep p m (pc,(h,s,l)) (h',loc).
*)
  Inductive DEX_exec_intra (p:DEX_Program) (m:DEX_Method) : option DEX_ClassName -> DEX_IntraNormalState -> DEX_IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
    DEX_NormalStep p m s1 s2 ->
    DEX_exec_intra p m None s1 s2
(*  | exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc' e,
    ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
    CaughtException p m (pc1,h2,loc2) pc' ->
    Heap.typeof h2 loc2 = Some (Heap.LocationObject e) ->
    exec_intra p m (Some e) (pc1,(h1,s1,l1)) (pc',(h2,Ref loc2::OperandStack.empty,l1))
*)
.

  Inductive DEX_exec_return (p:DEX_Program) (m:DEX_Method) : option DEX_ClassName -> DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     DEX_ReturnStep p m s (h,Normal ov) ->
     DEX_exec_return p m None s (h,Normal ov)
(*  | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1 e,
     ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
     UnCaughtException  p m (pc1,h2,loc2) ->
     Heap.typeof h2 loc2 = Some (Heap.LocationObject e) ->
     exec_return p m (Some e) (pc1,(h1,s1,l1)) (h2,Exception loc2)
*)
.

(* DEX Method
  Inductive DEX_exec_call (p:DEX_Program)  (m:DEX_Method) : option DEX_ClassName ->
   DEX_IntraNormalState -> DEX_ReturnState -> DEX_Method  -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState  -> Prop :=
 | exec_call_normal : forall m2 pc1 pc1' h1 l1 l1' l2 h2 bm2 ov,
     DEX_CallStep p m (pc1,(h1, l1 )) (m2,l2) ->
     DEX_METHOD.body m2 = Some bm2 ->
     next m pc1 = Some pc1' ->
     compat_op (Some ov) (DEX_METHODSIGNATURE.result (DEX_METHOD.signature m2)) ->
     l1' = DEX_Registers.update l1 DEX_Registers.ret ov ->
     DEX_exec_call p m None
        (pc1,(h1, l1))
        (h2,Normal (Some ov))
        m2
        (DEX_BYTECODEMETHOD.firstAddress bm2,(h1, l2))
        (inl _ (pc1',(h2, l1)))
(*
 | exec_call_caught : forall m2 pc1 pc1' h1 s1 l1 os l2 h2 loc bm2 cn,
     CallStep p m (pc1,(h1,s1,l1 )) (m2,(os,l2)) ->
     METHOD.body m2 = Some bm2 ->
     CaughtException p m (pc1, h2, loc) pc1' ->

     Heap.typeof h2 loc = Some (Heap.LocationObject cn) ->
     In cn (throwableBy (METHOD.signature m2)) -> (* Specific hypothesis here *)

     exec_call p m (Some cn)
        (pc1,(h1,s1,l1))
        (h2,Exception loc)
        m2
        (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2))
        (inl _(pc1',(h2,Ref loc::nil,l1)))
 | exec_call_uncaught : forall m2 pc1 h1 s1 l1 os l2 h2 loc bm2 cn,
     CallStep p m (pc1,(h1,s1,l1 )) (m2,(os,l2)) ->
     METHOD.body m2 = Some bm2 ->
     UnCaughtException p m (pc1, h2, loc)  ->

     Heap.typeof h2 loc = Some (Heap.LocationObject cn) ->
     In cn (throwableBy (METHOD.signature m2)) -> (* Specific hypothesis here *)

     exec_call p m (Some cn)
       (pc1,(h1,s1,l1))
       (h2,Exception loc)
       m2
       (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2))
       (inr _ (h2,Exception loc))
*)
.
*)

 Inductive DEX_IntraStep (p:DEX_Program) : 
    DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop :=
  | IntraStep_res :forall m s ret tau,
     DEX_exec_return p m tau s ret ->
     DEX_IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2 tau,
     DEX_exec_intra p m tau s1 s2 ->
     DEX_IntraStep p m s1 (inl _ s2) 
(* DEX Method
  | IntraStep_call :forall m m' s1 s' ret' r tau,
     DEX_exec_call p m tau s1 ret' m' s' r ->
     TransStep_l (DEX_IntraStep p m') s' (inr _ ret') ->
     DEX_IntraStep p m s1 r
*).
 
 Definition DEX_IntraStepStar p m s r := TransStep_l (DEX_IntraStep p m) s r.

 Definition DEX_IntraStepStar_intra p m s s' := DEX_IntraStepStar p m s (inl _ s').

 Definition DEX_BigStep  p m s ret := DEX_IntraStepStar p m s (inr _ ret).


  Lemma DEX_IntraStep_ind_ : 
      forall (p:DEX_Program) 
        (P:DEX_Method->DEX_IntraNormalState->DEX_IntraNormalState+DEX_ReturnState->Prop),
         (forall m s, P m s (inl _ s)) ->
         (forall m tau s r, DEX_exec_return p m tau s r -> P m s (inr _ r)) ->
         (forall m tau s s' , DEX_exec_intra p m tau s s' -> 
            forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
            P m s r) ->
(* DEX Method
         (forall m tau s s' ret m' r, 
            DEX_exec_call p m tau s ret m' s' (inr _ r) ->
            DEX_IntraStepStar p m' s' (inr _ ret) ->
            P m' s' (inr _ ret) ->
            P m s (inr _ r)) ->
         (forall m tau s s' ret m' s'' r, 
            DEX_exec_call p m tau s ret m' s' (inl _ s'') ->
            DEX_IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
            DEX_IntraStepStar p m s'' r -> P m s'' r ->
            P m s r) ->
*)
      forall m s r, DEX_IntraStep p m s r -> 
        match r with
        | inr r' => P m s (inr _ r')
        | inl s' => forall r', DEX_IntraStepStar p m s' r' -> P m s' r' -> P m s r'
        end.
     Proof.
       intros prg Q H0 Hr Hi Hcr Hc.
       fix intra (*4*)2;intros (*m s*) r Hs;case Hs;clear (*m s*) r Hs;intros.
       eapply Hr; eauto.
       apply Hi with tau s2;trivial. 
     Qed.
(* DEX Method
       assert (Q m' s' (inr DEX_IntraNormalState ret')).
       generalize s' (inr DEX_IntraNormalState ret') H1;clear H1 H m s1 s' ret' r.
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
*)

  Lemma DEX_IntraStepStar_ind : 
    forall (p:DEX_Program) 
     (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop),
       (forall m s, P m s (inl _ s)) ->
       (forall m tau s r, DEX_exec_return p m tau s r -> P m s (inr _ r)) ->
       (forall m tau s s' , DEX_exec_intra p m tau s s' -> 
          forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
          P m s r) ->
(* DEX Method
       (forall m tau s s' ret m' r, 
          DEX_exec_call p m tau s ret m' s' (inr _ r) ->
          DEX_IntraStepStar p m' s' (inr _ ret) ->
          P m' s' (inr _ ret) ->
          P m s (inr _ r)) ->
       (forall m tau s s' ret m' s'' r, 
          DEX_exec_call p m tau s ret m' s' (inl _ s'') ->
          DEX_IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
          DEX_IntraStepStar p m s'' r -> P m s'' r ->
          P m s r) ->
*)
    forall m s r, DEX_IntraStepStar p m s r -> P m s r.
   Proof.
     intros p Q H0 Hr Hi (*Hcr Hc*).
     fix fixp 4;intros m s' s Ht;case Ht;clear Ht s' s;intros.
     apply H0.
     generalize (DEX_IntraStep_ind_ Q H0 Hr Hi (*Hcr Hc*) H).
     case r;intros;trivial.
     apply H1;trivial. 
     constructor.
     assert (HH:=DEX_IntraStep_ind_ Q H0 Hr Hi (*Hcr Hc*) H);simpl in HH.
     apply HH;trivial.   
     apply fixp;trivial.
   Qed.

End DEX_instr.
 
End DEX_BigStepAnnot.