(* Hendra : DEX big step semantics, looking into BigStepLoad.v as reference *)

  Import DEX_Dom DEX_Prog.

  Open Scope type_scope.
  Definition DEX_InitCallState :=  DEX_Method * DEX_Registers.t.
  Definition DEX_IntraNormalState := DEX_PC * (DEX_Heap.t * DEX_Registers.t).
  Definition DEX_ReturnState := DEX_Heap.t * DEX_ReturnVal.


  Inductive DEX_NormalStep (p:DEX_Program) : 
    DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState  -> Prop :=
  | nop : forall h m pc pc' regs,

    instructionAt m pc = Some DEX_Nop ->
    next m pc = Some pc' ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs))

  | const : forall h m pc pc' regs regs' k rt v,

    instructionAt m pc = Some (DEX_Const k rt v) ->
    In rt (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    (-2^31 <= v < 2^31)%Z ->
    DEX_METHOD.valid_reg m rt ->
    regs' = DEX_Registers.update regs rt (Num (I (Int.const v))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))
  
  | move_step_ok : forall h m pc pc' regs regs' k rt rs v,

    instructionAt m pc = Some (DEX_Move k rt rs) ->
    In rt (DEX_Registers.dom regs) ->
    In rs (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some v = DEX_Registers.get regs rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    regs' = DEX_Registers.update regs rt v ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  | goto_step_ok : forall h m pc regs o,

    instructionAt m pc = Some (DEX_Goto o) ->

    DEX_NormalStep p m (pc, (h, regs)) ((DEX_OFFSET.jump pc o), (h, regs))
  
  | packedswitch_step_ok1 : forall h m pc l v r firstKey size list_offset n o,
    
    instructionAt m pc = Some (DEX_PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    (firstKey <= Int.toZ v < firstKey + (Z_of_nat size))%Z ->
    length list_offset = size ->
    Z_of_nat n = ((Int.toZ v) - firstKey)%Z ->
    nth_error list_offset n = Some o ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | packedswitch_step_ok2 : forall h m pc pc' l v r firstKey size list_offset,
    
    instructionAt m pc = Some (DEX_PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    length list_offset = size ->
    (Int.toZ v < firstKey \/ firstKey + (Z_of_nat size) <= Int.toZ v)%Z ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m r ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))
  
  | sparseswitch_step_ok1 : forall h m pc l v v' o r size listkey,
    
    instructionAt m pc = Some (DEX_SparseSwitch r size listkey) ->
    length listkey = size ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    List.In (pair v' o) listkey ->
    v' = Int.toZ v ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | sparseswitch_step_ok2 : forall h m pc pc' l v r size listkey,

    instructionAt m pc = Some (DEX_SparseSwitch r size listkey) ->
    length listkey = size ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    (forall v' o, List.In (pair v' o) listkey ->  v' <> Int.toZ v) ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m r ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))

  | ifcmp_step_jump : forall h m pc regs va vb cmp ra rb o,

    instructionAt m pc = Some (DEX_Ifcmp cmp ra rb o) ->
    In ra (DEX_Registers.dom regs) ->
    In rb (DEX_Registers.dom regs) ->
    Some (Num (I va)) = DEX_Registers.get regs ra ->
    Some (Num (I vb)) = DEX_Registers.get regs rb ->
    SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->
    
    DEX_NormalStep p m (pc, (h, regs)) ((DEX_OFFSET.jump pc o), (h, regs))

  | ifcmp_step_continue : forall h m pc pc' regs va vb cmp ra rb o,
    
    instructionAt m pc = Some (DEX_Ifcmp cmp ra rb o) ->
    In ra (DEX_Registers.dom regs) ->
    In rb (DEX_Registers.dom regs) ->
    Some (Num (I va)) = DEX_Registers.get regs ra ->
    Some (Num (I vb)) = DEX_Registers.get regs rb ->
    ~SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs))

  | ifz_step_jump : forall h m pc regs v cmp r o,

    instructionAt m pc = Some (DEX_Ifz cmp r o) ->
    In r (DEX_Registers.dom regs) ->
    Some (Num (I v)) = DEX_Registers.get regs r ->
    SemCompInt cmp (Int.toZ v) (0) ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, regs)) ((DEX_OFFSET.jump pc o), (h, regs))

  | ifz_step_continue : forall h m pc pc' regs v cmp r o,
    
    instructionAt m pc = Some (DEX_Ifz cmp r o) ->
    In r (DEX_Registers.dom regs) ->
    Some (Num (I v)) = DEX_Registers.get regs r ->
    ~SemCompInt cmp (Int.toZ v) (0) ->
    next m pc = Some pc' ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs))

  (** <addlink>ineg</addlink>: Negate [int] *)
  | ineg_step : forall h m pc regs regs' pc' rt rs v,

    instructionAt m pc = Some (DEX_Ineg rt rs) ->
    In rt (DEX_Registers.dom regs) ->
    In rs (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get regs rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    regs' = DEX_Registers.update regs rt (Num (I (Int.neg v))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  (** <addlink>ineg</addlink>: Not [int] (one's complement) *)
  | inot_step : forall h m pc regs regs' pc' rt rs v,

    instructionAt m pc = Some (DEX_Inot rt rs) ->
    In rt (DEX_Registers.dom regs) ->
    In rs (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get regs rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    regs' = DEX_Registers.update regs rt (Num (I (Int.not v))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  (** <addlink>i2b</addlink>: Convert [int] to [byte] *)
  | i2b_step_ok : forall h m pc pc' regs regs' rt rs v,

    instructionAt m pc = Some (DEX_I2b rt rs) ->
    In rt (DEX_Registers.dom regs) ->
    In rs (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get regs rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    regs' = DEX_Registers.update regs rt (Num (I (b2i (i2b v)))) ->
    
    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

 (** <addlink>i2s</addlink>: Convert [int] to [short] *)
  | i2s_step_ok : forall h m pc pc' regs regs' rt rs v,

    instructionAt m pc = Some (DEX_I2s rt rs) ->
    In rt (DEX_Registers.dom regs) ->
    In rs (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get regs rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    regs' = DEX_Registers.update regs rt (Num (I (s2i (i2s v)))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  | ibinop_step_ok : forall h m pc pc' regs regs' op rt ra rb va vb,

    instructionAt m pc = Some (DEX_Ibinop op rt ra rb) ->
    In rt (DEX_Registers.dom regs) ->
    In ra (DEX_Registers.dom regs) ->
    In rb (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = DEX_Registers.get regs ra ->
    Some (Num (I vb)) = DEX_Registers.get regs rb ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->
    regs' = DEX_Registers.update regs rt (Num (I (SemBinopInt op va vb))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  | ibinopconst_step_ok : forall h m pc pc' regs regs' op rt r va v,

    instructionAt m pc = Some (DEX_IbinopConst op rt r v) ->
    In r (DEX_Registers.dom regs) ->
    In rt (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = DEX_Registers.get regs r ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m r ->
    regs' = DEX_Registers.update regs rt (Num (I (SemBinopInt op va (Int.const v)))) ->

    DEX_NormalStep p m (pc, (h, regs)) (pc', (h, regs'))

  | new : forall h m pc pc' regs regs' c rt loc h',

    instructionAt m pc = Some (DEX_New rt c) ->
    In rt (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    DEX_Heap.new h p (DEX_Heap.DEX_LocationObject c) = Some (pair loc h') ->
    regs' = DEX_Registers.update regs rt (Ref loc) -> 

    DEX_NormalStep p m (pc,(h,regs)) (pc',(h',regs'))

  | iput : forall h m pc pc' regs f rs ro loc cn k v,

    instructionAt m pc = Some (DEX_Iput k rs ro f) ->
    In rs (DEX_Registers.dom regs) ->
    In ro (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get regs ro ->
    Some v = DEX_Registers.get regs rs ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) -> 
    defined_field p cn f ->
    assign_compatible p h v (DEX_FIELDSIGNATURE.type (snd f)) ->

    DEX_NormalStep p m (pc,(h,regs)) 
      (pc',(DEX_Heap.update h (DEX_Heap.DEX_DynamicField loc f) v, regs))

  | getfield : forall h m pc pc' regs regs' rt ro loc f k v cn,

    instructionAt m pc = Some (DEX_Iget k rt ro f) ->
    In rt (DEX_Registers.dom regs) ->
    In ro (DEX_Registers.dom regs) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get regs ro ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) -> 
    defined_field p cn f ->
    DEX_Heap.get h (DEX_Heap.DEX_DynamicField loc f) = Some v ->    
    regs' = DEX_Registers.update regs rt v ->

    DEX_NormalStep p m (pc,(h, regs)) (pc',(h, regs'))
.

  Inductive DEX_ReturnStep (p:DEX_Program) : DEX_Method -> DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | void_return : forall h m pc regs,

    instructionAt m pc = Some DEX_Return -> 
    DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = None ->

    DEX_ReturnStep p m (pc, (h, regs)) (h, Normal None)

  | vreturn : forall h m pc regs val t k rs,
    (* Implicit in the assumption is that the register has a value in it *)
    instructionAt m pc = Some (DEX_VReturn k rs) ->
    In rs (DEX_Registers.dom regs) ->
    DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->
    Some val = DEX_Registers.get regs rs ->

    DEX_ReturnStep p m (pc, (h, regs)) (h, Normal (Some val))
.

  Inductive DEX_exec_intra (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
     DEX_NormalStep p m s1 s2 ->
     DEX_exec_intra p m s1 s2.

  Inductive DEX_exec_return (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     DEX_ReturnStep p m s (h, Normal ov) ->
     DEX_exec_return p m s (h, Normal ov)
.

 Inductive DEX_IntraStep (p:DEX_Program) : 
    DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop :=
  | IntraStep_res :forall m s ret,
     DEX_exec_return p m s ret ->
     DEX_IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2,
     DEX_exec_intra p m s1 s2 ->
     DEX_IntraStep p m s1 (inl _ s2) .
 
 Definition DEX_IntraStepStar p m s r := TransStep_l (DEX_IntraStep p m) s r.

 Definition DEX_IntraStepStar_intra p m s s' := DEX_IntraStepStar p m s (inl _ s').

 Definition DEX_BigStep  p m s ret := DEX_IntraStepStar p m s (inr _ ret).

 Inductive DEX_ReachableStep (P:DEX_Program) : 
      (DEX_Method*DEX_IntraNormalState)->(DEX_Method*DEX_IntraNormalState) ->Prop :=
   | ReachableIntra : forall M s s', 
       DEX_IntraStep P M s (inl _ s') ->
       DEX_ReachableStep P (M,s) (M,s').

 Definition DEX_Reachable P M s s' := 
   exists M',  ClosReflTrans (DEX_ReachableStep P) (M,s) (M',s').