(** BigStepAnnot.v: We constrain the Bicolano bigstep semantics to handle only the executions where exception thrown at a given point are in a predefined set. Such a set could be computed for example with a CHA static analysis. *)
Require Export List.
Require Export ZArith.
Require Export LoadBicolano.

Inductive compat_op (A B:Set) : option A -> option B -> Prop :=
  compat_op_none : compat_op A B None None
| compat_op_some : forall k v, compat_op A B (Some k) (Some v).
Implicit Arguments compat_op [A B].


Module BigStepAnnot.

Import BigStep.BigStep StaticHandler.StaticHandler Dom Prog.



  Set Implicit Arguments.
  Section instr.
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
  Inductive exec_intra (p:Program) (m:Method) : option ClassName -> IntraNormalState -> IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
    NormalStep p m s1 s2 ->
    exec_intra p m None s1 s2
(*  | exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc' e,
    ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
    CaughtException p m (pc1,h2,loc2) pc' ->
    Heap.typeof h2 loc2 = Some (Heap.LocationObject e) ->
    exec_intra p m (Some e) (pc1,(h1,s1,l1)) (pc',(h2,Ref loc2::OperandStack.empty,l1))
*)
.

  Inductive exec_return (p:Program) (m:Method) : option ClassName -> IntraNormalState -> ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     ReturnStep p m s (h,Normal ov) ->
     exec_return p m None s (h,Normal ov)
(*  | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1 e,
     ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
     UnCaughtException  p m (pc1,h2,loc2) ->
     Heap.typeof h2 loc2 = Some (Heap.LocationObject e) ->
     exec_return p m (Some e) (pc1,(h1,s1,l1)) (h2,Exception loc2)
*)
.

  Inductive exec_call (p:Program)  (m:Method) : option ClassName ->
   IntraNormalState -> ReturnState -> Method  -> IntraNormalState -> IntraNormalState + ReturnState  -> Prop :=
 | exec_call_normal : forall m2 pc1 pc1' h1 l1 l1' l2 h2 bm2 ov,
     CallStep p m (pc1,(h1, l1 )) (m2,l2) ->
     METHOD.body m2 = Some bm2 ->
     next m pc1 = Some pc1' ->
     compat_op (Some ov) (METHODSIGNATURE.result (METHOD.signature m2)) ->
     l1' = LocalVar.update l1 LocalVar.ret ov ->
     exec_call p m None
        (pc1,(h1, l1))
        (h2,Normal (Some ov))
        m2
        (BYTECODEMETHOD.firstAddress bm2,(h1, l2))
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

 Inductive IntraStep (p:Program) : 
    Method -> IntraNormalState -> IntraNormalState + ReturnState -> Prop :=
  | IntraStep_res :forall m s ret tau,
     exec_return p m tau s ret ->
     IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2 tau,
     exec_intra p m tau s1 s2 ->
     IntraStep p m s1 (inl _ s2) 
  | IntraStep_call :forall m m' s1 s' ret' r tau,
     exec_call p m tau s1 ret' m' s' r ->
     TransStep_l (IntraStep p m') s' (inr _ ret') ->
     IntraStep p m s1 r.
 
 Definition IntraStepStar p m s r := TransStep_l (IntraStep p m) s r.

 Definition IntraStepStar_intra p m s s' := IntraStepStar p m s (inl _ s').

 Definition BigStep  p m s ret := IntraStepStar p m s (inr _ ret).


  Lemma IntraStep_ind_ : 
      forall (p:Program) 
        (P:Method->IntraNormalState->IntraNormalState+ReturnState->Prop),
         (forall m s, P m s (inl _ s)) ->
         (forall m tau s r, exec_return p m tau s r -> P m s (inr _ r)) ->
         (forall m tau s s' , exec_intra p m tau s s' -> 
            forall r, IntraStepStar p m s' r -> P m s' r ->
            P m s r) ->
         (forall m tau s s' ret m' r, 
            exec_call p m tau s ret m' s' (inr _ r) ->
            IntraStepStar p m' s' (inr _ ret) ->
            P m' s' (inr _ ret) ->
            P m s (inr _ r)) ->
         (forall m tau s s' ret m' s'' r, 
            exec_call p m tau s ret m' s' (inl _ s'') ->
            IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
            IntraStepStar p m s'' r -> P m s'' r ->
            P m s r) ->
      forall m s r, IntraStep p m s r -> 
        match r with
        | inr r' => P m s (inr _ r')
        | inl s' => forall r', IntraStepStar p m s' r' -> P m s' r' -> P m s r'
        end.
     Proof.
       intros prg Q H0 Hr Hi Hcr Hc.
       fix intra 4;intros m s r Hs;case Hs;clear m s r Hs;intros.
       eapply Hr; eauto.
       apply Hi with tau s2;trivial. 
       assert (Q m' s' (inr IntraNormalState ret')).
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
       (forall m tau s r, exec_return p m tau s r -> P m s (inr _ r)) ->
       (forall m tau s s' , exec_intra p m tau s s' -> 
          forall r, IntraStepStar p m s' r -> P m s' r ->
          P m s r) ->
       (forall m tau s s' ret m' r, 
          exec_call p m tau s ret m' s' (inr _ r) ->
          IntraStepStar p m' s' (inr _ ret) ->
          P m' s' (inr _ ret) ->
          P m s (inr _ r)) ->
       (forall m tau s s' ret m' s'' r, 
          exec_call p m tau s ret m' s' (inl _ s'') ->
          IntraStepStar p m' s' (inr _ ret) -> P m' s' (inr _ ret) ->
          IntraStepStar p m s'' r -> P m s'' r ->
          P m s r) ->
    forall m s r, IntraStepStar p m s r -> P m s r.
   Proof.
     intros p Q H0 Hr Hi Hcr Hc.
     fix fixp 4;intros m s' s Ht;case Ht;clear Ht s' s;intros.
     apply H0.
     generalize (IntraStep_ind_ Q H0 Hr Hi Hcr Hc H).
     case r;intros;trivial.
     apply H1;trivial. 
     constructor.
     assert (HH:=IntraStep_ind_ Q H0 Hr Hi Hcr Hc H);simpl in HH.
     apply HH;trivial.   
     apply fixp;trivial.
   Qed.

End instr.
 
End BigStepAnnot.