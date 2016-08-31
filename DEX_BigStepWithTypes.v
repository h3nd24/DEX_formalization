(** BigStepWithTypes.v: Intermediate bigstep semantics where we mixed semantic and typing rules (used only as an intermediate step in the proof) *)
Require Export ZArith.
Require Export DEX_IndistRelations.

Module DEX_BigStepWithTypes.

  Open Scope type_scope.

  Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog .

  Section p.
    Variable kobs: L.t.
    Variable p : DEX_ExtendedProgram.
    (*Notation ft := (ft p).*)

    Section annot.
      Variable se : DEX_PC -> L.t.
      Variable region : DEX_PC -> option DEX_ClassName -> DEX_PC -> Prop.
      (* focus on DEX I 
      Definition newb (k:L.t) (b:FFun.t Location) (loc:Location) : FFun.t Location :=
        if L.leql_dec k kobs then (FFun.extends b loc) 
          else b.
      *)

      Infix "<=" := L.leql (at level 70).
      (*Infix "<='" := L.leql' (at level 70).*)
      (*Infix "U'" := L.join' (at level 60, right associativity).*)
      Infix "U" := L.join (at level 60, right associativity).

      Inductive NormalStep_const (k:DEX_ValKind) (reg:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | const : forall (*h*) pc pc' r (*l*) r' rt rt' (*b*),

        next m pc = Some pc' ->
        (*(   (t=DEX_BYTE /\ -2^7 <= z < 2^7)
          \/ (t=DEX_SHORT /\ -2^15 <= z < 2^15)
          \/ (t=DEX_INT /\ -2^31 <= z < 2^31)   )%Z ->*)
        r' = DEX_Registers.update r reg (Num (I (Int.const v))) ->
        rt' = VarMap.update _ rt reg (se pc) ->
        NormalStep_const k reg v m sgn 
          (pc,((*h,*)r)) rt (*b*) (pc',((*h,*)r'(*,l*))) rt' (*L.Simple (se pc)::st*) (*b*).

      Inductive NormalStep_goto (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | goto : forall (*h*) pc r (*l*) rt (*b*),

        NormalStep_goto o m sgn 
        (pc,((*h,*)r(*,l*))) rt (*b*) (DEX_OFFSET.jump pc o,((*h,*)r(*,l*))) rt (*b*).

      Inductive NormalStep_i2b (reg:DEX_Reg) (rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | i2b : forall (*h*) pc pc' r r' (*l*) v k rt rt' (*b*),

        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (b2i (i2b v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_i2b reg rs m sgn 
        (pc,((*h,*)r(*,l*))) rt (*L.Simple k::st) b*) (pc',((*h,*)r'(*,l*))) rt' (*b*).

      Inductive NormalStep_i2s (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | i2s : forall (*h*) pc pc' r r' (*l*) v k rt rt' (*b*),

        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (s2i (i2s v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_i2s reg rs m sgn 
        (pc,((*h,*)r(*,l*))) rt (*L.Simple k::st) b*) (pc',((*h,*)r'(*,l*))) rt' (*b*).

      Inductive NormalStep_ibinop (reg ra rb:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | ibinop : forall (*h*) pc pc' r r' (*l*) i1 i2 k1 k2 rt (*b*) rt' op,

        next m pc = Some pc' ->
        (* Hendra 16082016 exception for division by 0 - op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0%Z) -> 
        st' = (match op with 
                 | DivInt => elift m pc k1 st
                 | RemInt => elift m pc k1 st
                 | _ => st
               end) ->
        (match op with 
           | DivInt => forall j, region pc None j -> k1 <= (se j)
           | RemInt => forall j, region pc None j -> k1 <= (se j)
           | _ => True
         end) -> *)
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i1 i2))) ->
        rt' = VarMap.update _ rt reg (k1 U (k2 U (se pc))) ->
        NormalStep_ibinop reg ra rb m sgn op
          (pc,((*h,*)r)) rt (*b*) (pc',((*h,*)r')) rt' (*b*).

      Inductive NormalStep_ibinopConst (reg ra:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | ibinopConst : forall pc pc' r r' i k rt rt' op,

        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r ra ->
        Some k = VarMap.get _ rt ra ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i (Int.const v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_ibinopConst reg ra v m sgn op (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_ifcmp (cmp:DEX_CompInt) (ra rb:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | ifcmp_jump : forall (*h*) pc r i2 i1 k1 k2 rt (*b*),
        (*instructionAt m pc = Some (DEX_Ifcmp cmp o) ->*)
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn 
        (pc,((*h,*)r)) rt (*b*) (DEX_OFFSET.jump pc o,((*h,*)r)) rt (*b*)
      | ificmp_continue : forall (*h*) pc pc' r i2 i1 k1 k2 rt (*b*),
        next m pc = Some pc' ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn 
        (pc,((*h,*)r)) rt (*b*) (pc',((*h,*)r)) rt (*b*).

      Inductive NormalStep_ifz (cmp:DEX_CompInt) (reg:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | ifz_jump : forall (*h*) pc r i k rt (*b*),
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get _ rt reg ->
        SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc None j -> k <= (se j)) -> 
        NormalStep_ifz cmp reg o m sgn 
        (pc,((*h,*)r)) rt (*b*) (DEX_OFFSET.jump pc o,((*h,*)r)) rt (*b*)
      | ifz_continue : forall (*h*) pc pc' r i k rt (*b*),

        next m pc = Some pc' ->
        Some k = VarMap.get _ rt reg ->
        ~ SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_ifz cmp reg o m sgn 
        (pc,((*h,*)r)) rt (*b*) (pc',((*h,*)r)) rt (*b*).

      Inductive NormalStep_ineg (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | ineg : forall pc r r' pc' v k rt rt',

        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (Int.neg v))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->

        NormalStep_ineg reg rs m sgn (pc,r) rt (pc',r') rt'.

    Inductive NormalStep_inot (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | inot : forall pc r r' pc' v k rt rt',

        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (Int.not v))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->

        NormalStep_inot reg rs m sgn (pc,r) rt (pc',r') rt'.

(*
      Inductive NormalStep_lookupswitch (def:OFFSET.t) (listkey:list (Z*OFFSET.t)) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | lookupswitch1 : forall h pc s l i i' o' k st b,

        List.In (pair i' o')listkey ->
        i' = Int.toZ i ->
        (forall j, region pc None j -> k <= se j) -> 

        NormalStep_lookupswitch def listkey m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc o',(h,s,l)) (lift k st) b
      | lookupswitch2 : forall h pc s l i k st b,

        (forall i' o', List.In (pair i' o')listkey ->  i' <> Int.toZ i) ->
        (forall j, region pc None j -> k <= se j) -> 

        NormalStep_lookupswitch def listkey m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc def,(h,s,l)) (lift k st) b.
*)

      Inductive NormalStep_nop (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | nop : forall pc pc' r rt,

        next m pc = Some pc' ->

        NormalStep_nop m sgn (pc,r) rt (pc',r) rt. 
(*
      Inductive NormalStep_tableswitch (def:OFFSET.t) (low high:Z) (list_offset:list OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | tableswitch1 : forall h pc s l i st b k,

        Z_of_nat (length list_offset) = (high - low + 1)%Z ->
        (Int.toZ i < low \/ high < Int.toZ i)%Z ->
        (forall j, region pc None j -> k <= se j) -> 
        
        NormalStep_tableswitch def low high list_offset m sgn
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc def,(h,s,l)) (lift k st) b
      | tableswitch2 : forall h pc s l n i st b o k,

        Z_of_nat (length list_offset) = (high - low + 1)%Z ->
        (low <= Int.toZ i <= high)%Z ->
        Z_of_nat n = ((Int.toZ i) - low)%Z ->
        nth_error list_offset n = Some o ->
        (forall j, region pc None j -> k <= se j) -> 
        
        NormalStep_tableswitch def low high list_offset m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift k st) b.
*)

      Inductive NormalStep_move (vk:DEX_ValKind) (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | vload : forall pc pc' r r' val rt rt' k,

        instructionAt m pc = Some (DEX_Move vk reg rs) ->
        next m pc = Some pc' ->
        Some val = DEX_Registers.get r rs ->
        DEX_Registers.update r reg val = r' ->
        VarMap.get _ rt rs = Some k ->
        VarMap.update _ rt reg (k U (se pc)) = rt' ->

        NormalStep_move vk reg rs m sgn (pc,r) rt (pc',r') rt'.
      
      Definition NormalStep 
        (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
        match i with
          | DEX_Const k r z => NormalStep_const k r z m sgn
          | DEX_Goto o => NormalStep_goto o m sgn
          | DEX_I2b reg rs => NormalStep_i2b reg rs m sgn
          | DEX_I2s reg rs => NormalStep_i2s reg rs m sgn
          | DEX_Ibinop op reg ra rb => NormalStep_ibinop reg ra rb m sgn op
          | DEX_IbinopConst op reg ra z => NormalStep_ibinopConst reg ra z m sgn op
          | DEX_Ifcmp cmp ra rb o  => NormalStep_ifcmp cmp ra rb o m sgn
          | DEX_Ifz cmp reg o => NormalStep_ifz cmp reg o m sgn
          | DEX_Ineg reg rs => NormalStep_ineg reg rs m sgn
          | DEX_Inot reg rs => NormalStep_inot reg rs m sgn
          (*| Lookupswitch def listkey  => NormalStep_lookupswitch def listkey m sgn*)
          | DEX_Nop => NormalStep_nop m sgn
          | DEX_Return => fun _ _ _ _  => False
(*           | Tableswitch def low high list_offset => NormalStep_tableswitch def low high list_offset m sgn *)
          | DEX_Move k reg rs => NormalStep_move k reg rs m sgn
          | DEX_VReturn k reg => fun _ _ _ _ => False
        end.

      Inductive ReturnStep (m:DEX_Method) (sgn:DEX_sign) : DEX_Instruction ->
        DEX_IntraNormalState -> TypeRegisters -> DEX_ReturnState -> Prop :=
      | void_return : forall pc r rt,
        instructionAt m pc = Some (DEX_Return) ->
        DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = None ->
        sgn.(DEX_resType) = None ->
        ReturnStep m sgn DEX_Return (pc,r) rt (Normal None)
      | vreturn : forall pc r reg val t k k1 rt kr,
        instructionAt m pc = Some (DEX_VReturn k reg) ->
        DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = Some t ->
        Some val = DEX_Registers.get r reg ->
        Some k1 = VarMap.get _ rt reg ->
        assign_compatible p.(DEX_prog) val t ->
        compat_ValKind_value k val ->
        sgn.(DEX_resType) = Some kr ->
        L.leql (k1 U (se pc)) kr ->

        ReturnStep m sgn (DEX_VReturn k reg) (pc,r) rt (Normal (Some val)).

      Inductive exec_intra (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        option DEX_ClassName ->
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) Prop :=
      | exec_intra_normal : forall r1 r2 rt1 rt2,
        NormalStep m sgn i r1 rt1 r2 rt2 ->
        exec_intra m sgn i None r1 rt1 r2 rt2
      (*| exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc' st b1 k b2 e,
        ExceptionStep m sgn i (pc1,(h1,s1,l1)) st b1 (h2,loc2) k b2 e ->
        CaughtException p.(prog) m (pc1,h2,loc2) pc' ->
        (forall j, region pc1 (Some e) j -> k <= (se j)) -> 
        In e (Dom.Prog.throwableAt m pc1) ->
        exec_intra m sgn i (Some e) 
        (pc1,(h1,s1,l1)) st b1
        (pc',(h2,Ref loc2::OperandStack.empty,l1)) (L.Simple k::nil) b2*).

      Inductive exec_return (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        option DEX_ClassName ->
        DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*)
        DEX_ReturnState -> (*FFun.t Location ->*) Prop :=
      | exec_return_normal : forall r ov rt,
        ReturnStep m sgn i r rt (Normal ov) ->
        exec_return m sgn i None r rt (Normal ov)
      (*| exec_return_exception : forall pc1 h1 h2 loc2 s1 l1 st b1 k b2 e,
        ExceptionStep m sgn i (pc1,(h1,s1,l1)) st b1 (h2,loc2) k b2 e ->
        UnCaughtException p.(prog) m (pc1,h2,loc2) ->
        (forall j, region pc1 (Some e) j -> k <= (se j)) -> 
        In e (Dom.Prog.throwableAt m pc1) ->
        L.leql k (sgn.(resExceptionType) e) ->
        exec_return m sgn i (Some e) (pc1,(h1,s1,l1)) st b1 (h2,Exception loc2) b2*).

      Inductive exec (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) (kd:option DEX_ClassName) : state -> state -> Prop :=
      | exec_intra_case : forall r1 rt1 r2 rt2,
        exec_intra m sgn i kd r1 rt1 r2 rt2 ->
        exec m sgn i kd (intra r1 rt1) (intra r2 rt2)
      | exec_return_case : forall pc1 r1 rt1 v2,
        exec_return m sgn i kd (pc1,r1) rt1 (v2) ->
        exec m sgn i kd (intra (pc1,r1) rt1) (ret v2).

    End annot.
  End p.

End DEX_BigStepWithTypes.

(* Import DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog. *)
Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog .

(* 
Section p.
  Variable p : DEX_ExtendedProgram.

  Lemma NormalStep_instructionAt : forall sgn m se s1 s2,
    DEX_BigStepWithTypes.NormalStep sgn se (* p m *) s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_clear H; simpl; eauto.
  Qed.
(*
  Lemma ExceptionStep_instructionAt : forall m s1 s2,
    BigStepAnnot.ExceptionStep throwableAt p m s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_clear H; simpl.
    eauto.
    inversion_clear H0; eauto.
  Qed.
*)
  Lemma exec_intra_instructionAt : forall m kd s1 s2,
    BigStepAnnot.exec_intra throwableAt p m kd s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_mine H.
    eapply NormalStep_instructionAt; eauto.
    eapply ExceptionStep_instructionAt; eauto.
  Qed.

  Lemma exec_return_instructionAt : forall m kd s r,
    @BigStepAnnot.exec_return throwableAt p m kd s r ->
    exists i, instructionAt m (fst s) = Some i.
  Proof.
    intros.
    inversion_mine H.
    inversion_mine H0; simpl; eauto.
    eapply ExceptionStep_instructionAt; eauto.
  Qed.

End p. *)

