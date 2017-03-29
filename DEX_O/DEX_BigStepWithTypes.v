(** BigStepWithTypes.v: Intermediate bigstep semantics where we mixed semantic and typing rules (used only as an intermediate step in the proof) *)
Require Export ZArith.
Require Export DEX_IndistRelations.

Module DEX_BigStepWithTypes.

  Open Scope type_scope.

  Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog .

  Section p.
    Variable kobs: L.t.
    Variable p : DEX_ExtendedProgram.
    Notation ft := (DEX_ft p).

    Section annot.
      Variable se : DEX_PC -> L.t.
      Variable region : DEX_PC -> DEX_PC -> Prop.

      Definition newb (k:L.t) (b:FFun.t DEX_Location) (loc:DEX_Location) : FFun.t DEX_Location :=
        if L.leql_dec k kobs then (FFun.extends b loc) 
          else b.

      Infix "<=" := L.leql (at level 70).
      Infix "U" := L.join (at level 60, right associativity).

      Inductive NormalStep_const (k:DEX_ValKind) (reg:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | const : forall pc pc' h r r' rt rt' b,

        In reg (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        next m pc = Some pc' ->
        r' = DEX_Registers.update r reg (Num (I (Int.const v))) ->
        rt' = MapList.update rt reg (se pc) ->
        NormalStep_const k reg v m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_goto (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | goto : forall pc h r rt b,

        NormalStep_goto o m sgn (pc,(h,r)) rt b (DEX_OFFSET.jump pc o,(h,r)) rt b.

      Inductive NormalStep_i2b (reg:DEX_Reg) (rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | i2b : forall pc pc' h r r' v k rt rt' b,

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In rs (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = MapList.get rt rs ->
        r' = DEX_Registers.update r reg (Num (I (b2i (i2b v)))) ->
        rt' = MapList.update rt reg (k U (se pc)) ->
        NormalStep_i2b reg rs m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_i2s (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | i2s : forall pc pc' h r r' v k rt rt' b,
  
        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In rs (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = MapList.get rt rs ->
        r' = DEX_Registers.update r reg (Num (I (s2i (i2s v)))) ->
        rt' = MapList.update rt reg (k U (se pc)) ->
        NormalStep_i2s reg rs m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_ibinop (reg ra rb:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | ibinop : forall pc pc' h r r' i1 i2 k1 k2 rt rt' op b,

        In reg (DEX_Registers.dom r) ->
        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In ra (MapList.dom rt) ->
        In rb (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = MapList.get rt ra ->
        Some k2 = MapList.get rt rb ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i1 i2))) ->
        rt' = MapList.update rt reg (k1 U (k2 U (se pc))) ->
        NormalStep_ibinop reg ra rb m sgn op (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_ibinopConst (reg ra:DEX_Reg) (v:Z) (m:DEX_Method) (sgn:DEX_sign)  : DEX_BinopInt ->
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | ibinopConst : forall pc pc' h r r' i k rt rt' op b,

        In reg (DEX_Registers.dom r) ->
        In ra (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In ra (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r ra ->
        Some k = MapList.get rt ra ->
        r' = DEX_Registers.update r reg (Num (I (SemBinopInt op i (Int.const v)))) ->
        rt' = MapList.update rt reg (k U (se pc)) ->
        NormalStep_ibinopConst reg ra v m sgn op (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_ifcmp (cmp:DEX_CompInt) (ra rb:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location ->
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | ifcmp_jump : forall pc h r i2 i1 k1 k2 rt b,

        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In ra (MapList.dom rt) ->
        In rb (MapList.dom rt) ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = MapList.get rt ra ->
        Some k2 = MapList.get rt rb ->
        SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn (pc,(h,r)) rt b (DEX_OFFSET.jump pc o,(h,r)) rt b

      | ificmp_continue : forall pc pc' h r i2 i1 k1 k2 rt b,

        next m pc = Some pc' ->
        In ra (DEX_Registers.dom r) ->
        In rb (DEX_Registers.dom r) ->
        In ra (MapList.dom rt) ->
        In rb (MapList.dom rt) ->
        Some (Num (I i1)) = DEX_Registers.get r ra ->
        Some (Num (I i2)) = DEX_Registers.get r rb ->
        Some k1 = MapList.get rt ra ->
        Some k2 = MapList.get rt rb ->
        ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_ifcmp cmp ra rb o m sgn (pc,(h,r)) rt b (pc',(h,r)) rt b.

      Inductive NormalStep_ifz (cmp:DEX_CompInt) (reg:DEX_Reg) (o:DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | ifz_jump : forall pc h r i k rt b,

        In reg (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc j -> k <= (se j)) -> 

        NormalStep_ifz cmp reg o m sgn (pc,(h,r)) rt b (DEX_OFFSET.jump pc o,(h,r)) rt b

      | ifz_continue : forall pc pc' h r i k rt b,
        In reg (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        ~ SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc j -> k <= (se j)) -> 

        NormalStep_ifz cmp reg o m sgn (pc,(h,r)) rt b (pc',(h,r)) rt b.

      Inductive NormalStep_PackedSwitch (reg:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t) (m:DEX_Method) (sgn:DEX_sign) :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | packedSwitch : forall pc h r i k rt o n b,

        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        (firstKey <= Int.toZ i < firstKey + (Z_of_nat size))%Z ->
        Z_of_nat n = ((Int.toZ i) - firstKey)%Z ->
        nth_error l n = Some o ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_PackedSwitch reg firstKey size l m sgn (pc, (h,r)) rt b 
          (DEX_OFFSET.jump pc o, (h,r)) rt b

      | packedSwitch_continue : forall pc pc' h r i k rt b,

        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        (Int.toZ i < firstKey)%Z \/ (firstKey + (Z_of_nat size) <= Int.toZ i)%Z ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_PackedSwitch reg firstKey size l m sgn (pc, (h,r)) rt b (pc', (h,r)) rt b.

      Inductive NormalStep_SparseSwitch (reg:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)) (m:DEX_Method) (sgn:DEX_sign) :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | sparseSwitch : forall pc h r i k rt o b,

        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        List.In (pair (Int.toZ i) o) l ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_SparseSwitch reg size l m sgn (pc, (h,r)) rt b
          (DEX_OFFSET.jump pc o, (h,r)) rt b

      | sparseSwitch_continue : forall pc pc' h r i k rt b,

        next m pc = Some pc' ->
        Some (Num (I i)) = DEX_Registers.get r reg ->
        Some k = MapList.get rt reg ->
        (forall i' o', List.In (pair i' o') l ->  i' <> Int.toZ i) ->
        (forall j, region pc j -> k <= (se j)) ->

        NormalStep_SparseSwitch reg size l m sgn (pc, (h,r)) rt b (pc', (h,r)) rt b.

      Inductive NormalStep_ineg (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | ineg : forall pc r r' h pc' v k rt rt' b,

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In rs (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = MapList.get rt rs ->
        r' = DEX_Registers.update r reg (Num (I (Int.neg v))) ->
        rt' = MapList.update rt reg (k U (se pc)) ->

        NormalStep_ineg reg rs m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

    Inductive NormalStep_inot (reg rs:DEX_Reg) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | inot : forall pc r r' pc' h v k rt rt' b,

        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In rs (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Num (I v)) = DEX_Registers.get r rs ->
        Some k = MapList.get rt rs ->
        r' = DEX_Registers.update r reg (Num (I (Int.not v))) ->
        rt' = MapList.update rt reg (k U (se pc)) ->

        NormalStep_inot reg rs m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

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
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | nop : forall pc pc' h r rt b,

        next m pc = Some pc' ->

        NormalStep_nop m sgn (pc,(h,r)) rt b (pc',(h,r)) rt b. 
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
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | vload : forall pc pc' h r r' val rt rt' k b,

        instructionAt m pc = Some (DEX_Move vk reg rs) ->
        In reg (DEX_Registers.dom r) ->
        In rs (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In rs (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some val = DEX_Registers.get r rs ->
        DEX_Registers.update r reg val = r' ->
        MapList.get rt rs = Some k ->
        MapList.update rt reg (k U (se pc)) = rt' ->

        NormalStep_move vk reg rs m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.

      Inductive NormalStep_iget (vk:DEX_type) (reg ro:DEX_Reg) 
        (f:DEX_FieldSignature) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | iget : forall pc pc' h r r' val loc cn rt rt' ko b,

        instructionAt m pc = Some (DEX_Iget vk reg ro f) ->
        In reg (DEX_Registers.dom r) ->
        In ro (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        In ro (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Ref loc) = DEX_Registers.get r ro ->
        DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) -> 
        defined_field p cn f ->
        DEX_Heap.get h (DEX_Heap.DEX_DynamicField loc f) = Some val ->    
        r' = DEX_Registers.update r reg val ->
        MapList.get rt ro = Some ko ->
        MapList.update rt reg (ko U ((se pc) U (ft f))) = rt' ->

        NormalStep_iget vk reg ro f m sgn (pc,(h,r)) rt b (pc',(h,r')) rt' b.
      
      Inductive NormalStep_iput (vk:DEX_type) (rs ro:DEX_Reg) 
        (f:DEX_FieldSignature) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | iput : forall pc pc' h h' r val loc cn rt ks ko b,

        instructionAt m pc = Some (DEX_Iput vk rs ro f) ->
        In rs (DEX_Registers.dom r) ->
        In ro (DEX_Registers.dom r) ->
        In rs (MapList.dom rt) ->
        In ro (MapList.dom rt) ->
        next m pc = Some pc' ->
        Some (Ref loc) = DEX_Registers.get r ro ->
        Some val = DEX_Registers.get r rs ->
        DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) -> 
        defined_field p cn f ->
        assign_compatible p h val (DEX_FIELDSIGNATURE.type (snd f)) ->
        h' = DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) val ->
        MapList.get rt ro = Some ko ->
        MapList.get rt rs = Some ks ->
        ks <= (ft f) -> 
        ko <= (ft f) -> 
        (se pc) <= (ft f) -> 

        NormalStep_iput vk rs ro f m sgn (pc,(h,r)) rt b (pc',(h',r)) rt b.

      Inductive NormalStep_new (reg:DEX_Reg) (c:DEX_ClassName) (m:DEX_Method) (sgn:DEX_sign)  :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> 
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | new : forall pc pc' h h' r r' loc rt rt' b,

        In reg (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        next m pc = Some pc' ->
        DEX_Heap.new h p (DEX_Heap.DEX_LocationObject c) = Some (pair loc h') ->
        r' = DEX_Registers.update r reg (Ref loc) -> 
        rt' = MapList.update rt reg (se pc) ->

        NormalStep_new reg c m sgn (pc,(h,r)) rt b (pc',(h',r')) rt' (newb (se pc) b loc).

      Definition NormalStep 
        (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location ->
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
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
          | DEX_Return => fun _ _ _ _ _ _ => False
(*           | Tableswitch def low high list_offset => NormalStep_tableswitch def low high list_offset m sgn *)
          | DEX_Move k reg rs => NormalStep_move k reg rs m sgn
          | DEX_VReturn k reg => fun _ _ _ _ _ _ => False
          | DEX_New reg c => NormalStep_new reg c m sgn
          | DEX_Iget vk reg ro f => NormalStep_iget vk reg ro f m sgn
          | DEX_Iput vk rs ro f => NormalStep_iput vk rs ro f m sgn
        end.

      Inductive ReturnStep (m:DEX_Method) (sgn:DEX_sign) : DEX_Instruction ->
        DEX_IntraNormalState -> TypeRegisters -> DEX_ReturnState -> Prop :=
      | void_return : forall h pc r rt,
        instructionAt m pc = Some (DEX_Return) ->
        DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = None ->
        sgn.(DEX_resType) = None ->
        ReturnStep m sgn DEX_Return (pc,(h,r)) rt (h, Normal None)
      | vreturn : forall pc h r reg val t k k1 rt kr,
        instructionAt m pc = Some (DEX_VReturn k reg) ->
        In reg (DEX_Registers.dom r) ->
        In reg (MapList.dom rt) ->
        DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = Some t ->
        Some val = DEX_Registers.get r reg ->
        Some k1 = MapList.get rt reg ->
        assign_compatible p.(DEX_prog) h val t ->
        compat_ValKind_value k val ->
        sgn.(DEX_resType) = Some kr ->
        L.leql (k1 U (se pc)) kr ->

        ReturnStep m sgn (DEX_VReturn k reg) (pc,(h,r)) rt (h, Normal (Some val)).

      Inductive exec_intra (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location ->
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location -> Prop :=
      | exec_intra_normal : forall r1 r2 rt1 rt2 b1 b2,
        NormalStep m sgn i r1 rt1 b1 r2 rt2 b2 ->
        exec_intra m sgn i r1 rt1 b1 r2 rt2 b2.

      Inductive exec_return (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) :
        DEX_IntraNormalState -> TypeRegisters -> FFun.t DEX_Location ->
        DEX_ReturnState -> FFun.t DEX_Location -> Prop :=
      | exec_return_normal : forall h r ov rt b,
        ReturnStep m sgn i r rt (h, Normal ov) ->
        exec_return m sgn i r rt b (h, Normal ov) b.

      Inductive exec (m:DEX_Method) (sgn:DEX_sign) (i:DEX_Instruction) : state -> state -> Prop :=
      | exec_intra_case : forall b1 b2 s1 s2 rt1 rt2,
        exec_intra m sgn i s1 rt1 b1 s2 rt2 b2 ->
        exec m sgn i (intra s1 rt1 b1) (intra s2 rt2 b2)
      | exec_return_case : forall b1 h1 pc1 r1 rt1 h2 v2 b2,
        exec_return m sgn i(pc1, (h1, r1)) rt1 b1 (h2, v2) b2 ->
        exec m sgn i (intra (pc1, (h1, r1)) rt1 b1) (ret h2 v2 b2).

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