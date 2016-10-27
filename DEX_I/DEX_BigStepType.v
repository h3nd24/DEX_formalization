(** * Bicolano: Big step (interface only) *)

(* <Insert License Here>

    $Id: BigStep.v 68 2006-02-02 15:06:27Z davidpichardie $ *)

(** Big step semantics.

 @author Benjamin Gregoire *)
(* Hendra : - Modified to suit DEX program. 
            - Also trim the system to contain only Arithmetic *)

Require Export DEX_Domain.

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

Module Type DEX_BIGSTEP.

 Declare Module DEX_Dom : DEX_SEMANTIC_DOMAIN.

 Load "DEX_BigStepLoad.v".

  Parameter IntraStepStar_ind : 
   forall (p:DEX_Program) 
    (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop),
      (forall m s, P m s (inl _ s)) ->
      (forall m s r, DEX_exec_return p m s r -> P m s (inr _ r)) ->
      (forall m s s' , DEX_exec_intra p m s s' -> 
         forall r, DEX_IntraStepStar p m s' r -> P m s' r ->
         P m s r) ->
   forall m s r, DEX_IntraStepStar p m s r -> P m s r.

  Parameter IntraStepStar_intra_ind : 
   forall (p:DEX_Program) 
    (P : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState -> Prop),
      (forall m s, P m s s) ->
      (forall m s s', DEX_exec_intra p m s s' -> 
         forall s'', DEX_IntraStepStar_intra p m s' s'' -> P m s' s'' ->
         P m s s'') ->
   forall m s s', DEX_IntraStepStar_intra p m s s' -> P m s s'.
  
  Parameter BigStep_ind : 
   forall (p:DEX_Program) 
    (P : DEX_Method -> DEX_IntraNormalState -> DEX_ReturnState -> Prop),
      (forall m s r, DEX_exec_return p m s r -> P m s r) ->
      (forall m s s' , DEX_exec_intra p m s s' -> 
         forall r, DEX_BigStep p m s' r -> P m s' r ->
         P m s r) ->
   forall m s r, DEX_BigStep p m s r -> P m s r.

  Parameter ReachableStar_ind : 
   forall (p:DEX_Program) 
    (P : (DEX_Method * DEX_IntraNormalState) -> (DEX_Method * DEX_IntraNormalState) -> Prop),
      (forall m s, P (m,s) (m,s)) ->
      (forall m s s', DEX_exec_intra p m s s' -> 
         forall m' s'', ClosReflTrans (DEX_ReachableStep p) (m,s') (m',s'') -> 
         P (m,s') (m',s'') ->
         P (m,s) (m',s'')) ->
   forall ms ms', 
      ClosReflTrans (DEX_ReachableStep p) ms ms' -> P ms ms'.

End DEX_BIGSTEP.