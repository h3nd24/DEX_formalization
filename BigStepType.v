(** * Bicolano: Big step (interface only) *)

(* <Insert License Here>

    $Id: BigStep.v 68 2006-02-02 15:06:27Z davidpichardie $ *)

(** Big step semantics.

 @author Benjamin Gregoire *)

Require Export Domain.

Set Implicit Arguments.
Definition cons_option (A:Set) (o:option A) (l:list A) := 
   match o with 
   | None => l
   | Some e => e::l
   end.
Unset Implicit Arguments.

Section TRANS.
 Set Implicit Arguments.
 Variable A B :Type.
 Variable R : A -> A + B -> Prop.

 Inductive TransStep_l : A -> A + B -> Prop :=
   | TransStep_l_refl : forall a,
       TransStep_l a (inl _ a)
   | TransStep_l_one : forall a r,
        R a r -> TransStep_l a r
   | TransStep_l_trans : forall a1 a2 r,
       R a1 (inl _ a2) -> 
       TransStep_l a2 r ->
       TransStep_l a1 r.

 Variable R' : A -> A -> Prop.

 Inductive ClosReflTrans : A -> A -> Prop :=
   | ClosReflTrans_refl : forall a, ClosReflTrans a a
   | ClosReflTrans_trans : forall a a' a'',
       R' a a' ->
       ClosReflTrans a' a'' ->
       ClosReflTrans a a''.

 Unset Implicit Arguments.

End TRANS.

Open Scope type_scope.

Module Type BIGSTEP.

 Declare Module Dom : SEMANTIC_DOMAIN.

 Load "BigStepLoad.v".

  Parameter IntraStepStar_ind : 
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

  Parameter IntraStepStar_intra_ind : 
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
  
  Parameter BigStep_ind : 
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

  Parameter ReachableStar_ind : 
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
       CallStep p m (pc,(h, l)) (m', l') ->
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

End BIGSTEP.




