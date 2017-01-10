(** BigStepWithTypes.v: Intermediate bigstep semantics where we mixed semantic and typing rules (used only as an intermediate step in the proof) *)
Require Export ZArith.
Require Export DEX_IndistRelations.

Module DEX_BigStepWithTypes.

  Open Scope type_scope.

  Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog .

  Section p.
    Variable kobs: L.t.
    Variable p : DEX_ExtendedProgram.

    Section annot.
      Variable se : DEX_PC -> L.t.
      Variable region : DEX_PC -> DEX_PC -> Prop.

      Infix "<=" := L.leql (at level 70).
      Infix "U" := L.join (at level 60, right associativity).

      Inductive NormalStep_const (k:DEX_ValKind) (reg:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | const : forall pc pc' r r' rt rt',

        In reg (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        r' = DEX_Registers.update r reg (Num (I (Int.const v))) ->
        rt' = VarMap.update _ rt reg (se pc) ->
        NormalStep_const k reg v m sgn (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_goto (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | goto : forall pc r rt,

        NormalStep_goto o m sgn (pc,r) rt (DEX_OFFSET.jump pc o,r) rt.

      Inductive NormalStep_i2b (reg:DEX_Reg) (rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | i2b : forall pc pc' r r' v k rt rt',

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In rs (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (b2i (i2b v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_i2b reg rs m sgn (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_i2s (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | i2s : forall pc pc' r r' v k rt rt',
  
        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In rs (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (s2i (i2s v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_i2s reg rs m sgn (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_ibinop (reg ra rb:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | ibinop : forall pc pc' r r' i1 i2 k1 k2 rt rt' op,

        In reg (DEX_Registers.dom r) ->
        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In ra (VarMap.dom _ rt) ->
        In rb (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i1 i2))) ->
        rt' = VarMap.update _ rt reg (k1 U (k2 U (se pc))) ->
        NormalStep_ibinop reg ra rb m sgn op (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_ibinopConst (reg ra:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | ibinopConst : forall pc pc' r r' i k rt rt' op,

        In reg (DEX_Registers.dom r) ->
        In ra (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In ra (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r ra ->
        Some k = VarMap.get _ rt ra ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i (Int.const v)))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->
        NormalStep_ibinopConst reg ra v m sgn op (pc,r) rt (pc',r') rt'.

      Inductive NormalStep_ifcmp (cmp:DEX_CompInt) (ra rb:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | ifcmp_jump : forall pc r i2 i1 k1 k2 rt ,

        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In ra (VarMap.dom _ rt) ->
        In rb (VarMap.dom _ rt) ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn (pc,r) rt (DEX_OFFSET.jump pc o,r) rt

      | ificmp_continue : forall pc pc' r i2 i1 k1 k2 rt,

        next m pc = Some pc' ->
        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In ra (VarMap.dom _ rt) ->
        In rb (VarMap.dom _ rt) ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = VarMap.get _ rt ra ->
        Some k2 = VarMap.get _ rt rb ->
        ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn (pc,r) rt (pc',r) rt.

      Inductive NormalStep_ifz (cmp:DEX_CompInt) (reg:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | ifz_jump : forall pc r i k rt,

        In reg (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get _ rt reg ->
        SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc j -> k <= (se j)) -> 

        NormalStep_ifz cmp reg o m sgn (pc,r) rt (DEX_OFFSET.jump pc o,r) rt

      | ifz_continue : forall pc pc' r i k rt,
        In reg (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get _ rt reg ->
        ~ SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc j -> k <= (se j)) -> 

        NormalStep_ifz cmp reg o m sgn (pc,r) rt (pc',r) rt.

      Inductive NormalStep_PackedSwitch (reg:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign) :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | packedSwitch : forall pc r i k rt o n,

        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get L.t rt reg ->
        (firstKey <= Int.toZ i < firstKey + (Z_of_nat size))%Z ->
        Z_of_nat n = ((Int.toZ i) - firstKey)%Z ->
        nth_error l n = Some o ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_PackedSwitch reg firstKey size l m sgn (pc, r) rt (DEX_OFFSET.jump pc o, r) rt

      | packedSwitch_continue : forall pc pc' r i k rt,

        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get L.t rt reg ->
        (Int.toZ i < firstKey)%Z \/ (firstKey + (Z_of_nat size) <= Int.toZ i)%Z ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_PackedSwitch reg firstKey size l m sgn (pc, r) rt (pc', r) rt.

      Inductive NormalStep_SparseSwitch (reg:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)) (m:DEX_Method) (sgn:DEX_sign) :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | sparseSwitch : forall pc r i k rt o,

        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get L.t rt reg ->
        List.In (pair (Int.toZ i) o) l ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_SparseSwitch reg size l m sgn (pc, r) rt (DEX_OFFSET.jump pc o, r) rt

      | sparseSwitch_continue : forall pc pc' r i k rt,

        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = VarMap.get L.t rt reg ->
        (forall i' o', List.In (pair i' o') l ->  i' <> Int.toZ i) ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_SparseSwitch reg size l m sgn (pc, r) rt (pc', r) rt.

      Inductive NormalStep_ineg (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | ineg : forall pc r r' pc' v k rt rt',

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In rs (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = VarMap.get _ rt rs ->
        r' = DEX_Registers.update r reg (Num (I (Int.neg v))) ->
        rt' = VarMap.update _ rt reg (k U (se pc)) ->

        NormalStep_ineg reg rs m sgn (pc,r) rt (pc',r') rt'.

    Inductive NormalStep_inot (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | inot : forall pc r r' pc' v k rt rt',

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In rs (VarMap.dom _ rt) ->
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
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
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
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | vload : forall pc pc' r r' val rt rt' k,

        instructionAt m pc = Some (DEX_Move vk reg rs) ->
        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        In rs (VarMap.dom _ rt) ->
        next m pc = Some pc' ->
        Some val = DEX_Registers.get r rs ->
        DEX_Registers.update r reg val = r' ->
        VarMap.get _ rt rs = Some k ->
        VarMap.update _ rt reg (k U (se pc)) = rt' ->

        NormalStep_move vk reg rs m sgn (pc,r) rt (pc',r') rt'.
      
      Definition NormalStep 
        (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
        match i with
          | DEX_Const k r z => NormalStep_const k r z m sgn
          | DEX_Goto o => NormalStep_goto o m sgn
          | DEX_I2b reg rs => NormalStep_i2b reg rs m sgn
          | DEX_I2s reg rs => NormalStep_i2s reg rs m sgn
          | DEX_Ibinop op reg ra rb => NormalStep_ibinop reg ra rb m sgn op
          | DEX_IbinopConst op reg ra z => NormalStep_ibinopConst reg ra z m sgn op
          | DEX_Ifcmp cmp ra rb o  => NormalStep_ifcmp cmp ra rb o m sgn
          | DEX_Ifz cmp reg o => NormalStep_ifz cmp reg o m sgn
          | DEX_PackedSwitch reg firstKey size l => NormalStep_PackedSwitch reg firstKey size l m sgn
          | DEX_SparseSwitch reg size l => NormalStep_SparseSwitch reg size l m sgn
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
        In reg (DEX_Registers.dom r) ->
        In reg (VarMap.dom _ rt) ->
        DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = Some t ->
        Some val = DEX_Registers.get r reg ->
        Some k1 = VarMap.get _ rt reg ->
        assign_compatible p.(DEX_prog) val t ->
        compat_ValKind_value k val ->
        sgn.(DEX_resType) = Some kr ->
        L.leql (k1 U (se pc)) kr ->

        ReturnStep m sgn (DEX_VReturn k reg) (pc,r) rt (Normal (Some val)).

      Inductive exec_intra (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> DEX_IntraNormalState -> TypeRegisters -> Prop :=
      | exec_intra_normal : forall r1 r2 rt1 rt2,
        NormalStep m sgn i r1 rt1 r2 rt2 ->
        exec_intra m sgn i r1 rt1 r2 rt2.

      Inductive exec_return (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> DEX_ReturnState -> Prop :=
      | exec_return_normal : forall r ov rt,
        ReturnStep m sgn i r rt (Normal ov) ->
        exec_return m sgn i r rt (Normal ov).

      Inductive exec (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) : state -> state -> Prop :=
      | exec_intra_case : forall r1 rt1 r2 rt2,
        exec_intra m sgn i r1 rt1 r2 rt2 ->
        exec m sgn i (intra r1 rt1) (intra r2 rt2)
      | exec_return_case : forall pc1 r1 rt1 v2,
        exec_return m sgn i(pc1,r1) rt1 (v2) ->
        exec m sgn i (intra (pc1,r1) rt1) (ret v2).

    End annot.
  End p.

End DEX_BigStepWithTypes.

Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog .


Section p.
  Variable p : DEX_ExtendedProgram.

  Lemma NormalStep_instructionAt : forall sgn m s1 s2,
    DEX_BigStep.DEX_NormalStep sgn m s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_clear H; simpl; eauto. 
  Qed.

  Lemma exec_intra_instructionAt : forall m s1 s2,
    DEX_BigStepAnnot.DEX_exec_intra p m s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_mine H.
    eapply NormalStep_instructionAt; eauto.
  Qed.

  Lemma exec_return_instructionAt : forall m s r,
    DEX_BigStepAnnot.DEX_exec_return p m s r ->
    exists i, instructionAt m (fst s) = Some i.
  Proof.
    intros.
    inversion_mine H.
    inversion_mine H0; simpl; eauto.
  Qed.

End p.