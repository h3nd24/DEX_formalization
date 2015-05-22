
  Import DEX_Dom DEX_Prog.

  Open Scope type_scope.
  Definition DEX_InitCallState :=  DEX_Method * DEX_Registers.t.
  Definition DEX_IntraNormalState := DEX_PC * (DEX_Heap.t * DEX_Registers.t).
(*  Definition IntraExceptionState := Heap.t * Location. *)
  Definition DEX_ReturnState := DEX_Heap.t * DEX_ReturnVal.


  Inductive DEX_NormalStep (p:DEX_Program) : DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState  -> Prop :=
  | nop : forall h m pc pc' l,

    instructionAt m pc = Some Nop ->
    next m pc = Some pc' ->

    DEX_NormalStep p m (pc,(h, l)) (pc',(h, l))

  | const : forall h m pc pc' l l' k rt v,

    instructionAt m pc = Some (Const k rt v) ->
    next m pc = Some pc' ->
    (-2^31 <= v < 2^31)%Z ->
    DEX_METHOD.valid_reg m rt ->
    l' = DEX_Registers.update l rt (Num (I (Int.const v))) ->

    DEX_NormalStep p m (pc,(h, l)) (pc',(h, l'))
  
  | move_step_ok : forall h m pc pc' l l' k rt rs v,

    instructionAt m pc = Some (Move k rt rs) ->
    next m pc = Some pc' ->
    Some v = DEX_Registers.get l rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt v ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  | moveresult_step_ok : forall h m pc pc' l l' k rt v,

    instructionAt m pc = Some (MoveResult k rt) ->
    next m pc = Some pc' ->
    Some v = DEX_Registers.get l DEX_Registers.ret ->
    DEX_METHOD.valid_reg m rt ->
    l' = DEX_Registers.update l rt v ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

 (** <addlink>instanceof</addlink>: Determine if object is of given type *)
  | instanceof_step_ok1 : forall h m pc pc' l loc rt r t l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l r ->
    assign_compatible p h (Ref loc) (DEX_ReferenceType t) ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m r ->
    l' = DEX_Registers.update l' rt (Num (I (Int.const 1))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))
 (** <addlink>instanceof</addlink>: with object == null *)
  | instanceof_step_ok2 : forall h m pc pc' l rt r t v l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some v = DEX_Registers.get l r ->
    isReference v ->
    (~ assign_compatible p h v (DEX_ReferenceType t) \/ v=Null) ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m r ->
    l' = DEX_Registers.update l' rt (Num (I (Int.const 0))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  (** <addlink>arraylength</addlink>: Get length of array *)
  | arraylength_step_ok : forall h m pc pc' l l' loc length tp a rt rs,

    instructionAt m pc = Some (ArrayLength rt rs)->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l rs ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationArray length tp a) ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt (Num (I length)) ->
    
    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>new</addlink>: Create new object *)
  | new_step_ok : forall h m pc pc' l l' c loc h' rt,

    instructionAt m pc = Some (New rt (DEX_ClassType c)) ->
    next m pc = Some pc' ->
    DEX_Heap.new h p (DEX_Heap.LocationObject c) = Some (pair loc h') ->
    DEX_METHOD.valid_reg m rt ->
    l' = DEX_Registers.update l rt (Ref loc) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h', l'))

 (** Create new array (<addlink>anewarray</addlink>, <addlink>newarray</addlink>) *)
 (** OutOfMemory is not considered in Bicolano *)
  | newarray_step_ok : forall h m pc pc' l l' i t loc h_new rt rl,

    instructionAt m pc = Some (NewArray rt rl t) ->
    next m pc = Some pc' ->
    DEX_Heap.new h p (DEX_Heap.LocationArray i t (m,pc)) = Some (pair loc h_new) ->
    Some (Num (I i)) = DEX_Registers.get l rl ->
    (0 <= Int.toZ i)%Z ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rl ->
    l' = DEX_Registers.update l rt (Ref loc) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h_new, l'))

  | goto_step_ok : forall h m pc l o,

    instructionAt m pc = Some (Goto o) ->

    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))
  
  | packedswitch_step_ok1 : forall h m pc l v r firstKey size list_offset n o,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    (firstKey <= Int.toZ v < firstKey + size)%Z ->
    Z_of_nat (length list_offset) = size ->
    Z_of_nat n = ((Int.toZ v) - firstKey)%Z ->
    nth_error list_offset n = Some o ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | packedswitch_step_ok2 : forall h m pc pc' l v r firstKey size list_offset,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    Z_of_nat (length list_offset) = size ->
    (Int.toZ v < firstKey \/ firstKey + size <= Int.toZ v)%Z ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m r ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))
  
  | sparseswitch_step_ok1 : forall h m pc l v v' o r size listkey,
    
    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    List.In (pair v' o) listkey ->
    v' = Int.toZ v ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | sparseswitch_step_ok2 : forall h m pc pc' l v r size listkey,

    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    (forall v' o, List.In (pair v' o) listkey ->  v' <> Int.toZ v) ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m r ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))

  | ifcmp_step_jump : forall h m pc l va vb cmp ra rb o,

    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = DEX_Registers.get l ra ->
    Some (Num (I vb)) = DEX_Registers.get l rb ->
    SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | ifcmp_step_continue : forall h m pc pc' l va vb cmp ra rb o,
    
    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = DEX_Registers.get l ra ->
    Some (Num (I vb)) = DEX_Registers.get l rb ->
    ~SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    next m pc = Some pc' ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))

  | ifz_step_jump : forall h m pc l v cmp r o,

    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    SemCompInt cmp (Int.toZ v) (0) ->
    DEX_METHOD.valid_reg m r ->
    
    DEX_NormalStep p m (pc, (h, l)) ((DEX_OFFSET.jump pc o), (h, l))

  | ifz_step_continue : forall h m pc pc' l v cmp r o,
    
    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = DEX_Registers.get l r ->
    ~SemCompInt cmp (Int.toZ v) (0) ->
    next m pc = Some pc' ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l))

   (** Load value from array *)
  | aget_step_ok : forall h m pc pc' l l' loc val i length t a k rt ra ri,

    instructionAt m pc = Some (Aget k rt ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l ra ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    Some (Num (I i)) = DEX_Registers.get l ri ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    DEX_Heap.get h (DEX_Heap.ArrayElement loc (Int.toZ i)) = Some val ->
    compat_ArrayKind_value k val ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m ri ->
    l' = DEX_Registers.update l rt (conv_for_stack val) -> 

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** Store into array *)
  | aput_step_ok : forall h m pc pc' l loc val i length tp k a rs ra ri, 

    instructionAt m pc = Some (Aput k rs ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l ra ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationArray length tp a) ->
    Some val = DEX_Registers.get l rs ->
    assign_compatible p h val tp ->
    Some (Num (I i)) = DEX_Registers.get l ri ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->
    DEX_METHOD.valid_reg m rs ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m ri ->

    DEX_NormalStep p m (pc, (h, l))
                   (pc',((DEX_Heap.update h (DEX_Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val tp)), l))

  (** <addlink>iget</addlink>: Fetch field from object *)
  | iget_step_ok : forall h m pc pc' l l' loc f v cn k rt ro,

    instructionAt m pc = Some (Iget k rt ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l ro ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationObject cn) -> 
    defined_field p cn f ->
    DEX_Heap.get h (DEX_Heap.DynamicField loc f) = Some v ->    
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m ro ->
    l' = DEX_Registers.update l rt v ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  (** <addlink>iput</addlink>: Set field in object *)
  | iput_step_ok : forall h m pc pc' l f loc cn v k rs ro,

    instructionAt m pc = Some (Iput k rs ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = DEX_Registers.get l ro ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Some v = DEX_Registers.get l rs ->
    assign_compatible p h v (DEX_FIELDSIGNATURE.type (snd f)) ->
    DEX_METHOD.valid_reg m rs ->
    DEX_METHOD.valid_reg m ro ->

    DEX_NormalStep p m (pc, (h, l))
           (pc, ((DEX_Heap.update h (DEX_Heap.DynamicField loc f) v), l))

  (* TODO : Invokevirtual *)
  (* TODO : Invokesuper *)
  (* TODO : Invokedirect *)
  (* TODO : Invokestatic *)
  (* TODO : Invokeinterface *)

  (** <addlink>ineg</addlink>: Negate [int] *)
  | ineg_step : forall h m pc l l' pc' rt rs v,

    instructionAt m pc = Some (Ineg rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get l rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt (Num (I (Int.neg v))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>ineg</addlink>: Not [int] (one's complement) *)
  | inot_step : forall h m pc l l' pc' rt rs v,

    instructionAt m pc = Some (Inot rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get l rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt (Num (I (Int.not v))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>i2b</addlink>: Convert [int] to [byte] *)
  | i2b_step_ok : forall h m pc pc' l l' rt rs v,

    instructionAt m pc = Some (I2b rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get l rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt (Num (I (b2i (i2b v)))) ->
    
    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

 (** <addlink>i2s</addlink>: Convert [int] to [short] *)
  | i2s_step_ok : forall h m pc pc' l l' rt rs v,

    instructionAt m pc = Some (I2s rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = DEX_Registers.get l rs ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m rs ->
    l' = DEX_Registers.update l rt (Num (I (s2i (i2s v)))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  | ibinop_step_ok : forall h m pc pc' l l' op rt ra rb va vb,

    instructionAt m pc = Some (Ibinop op rt ra rb) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = DEX_Registers.get l ra ->
    Some (Num (I vb)) = DEX_Registers.get l rb ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m ra ->
    DEX_METHOD.valid_reg m rb ->
    l' = DEX_Registers.update l rt (Num (I (SemBinopInt op va vb))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))

  | ibinopconst_step_ok : forall h m pc pc' l l' op rt r va v,

    instructionAt m pc = Some (IbinopConst op rt r v) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = DEX_Registers.get l r ->
    DEX_METHOD.valid_reg m rt ->
    DEX_METHOD.valid_reg m r ->
    l' = DEX_Registers.update l rt (Num (I (SemBinopInt op va (Int.const v)))) ->

    DEX_NormalStep p m (pc, (h, l)) (pc', (h, l'))
.


(*  Inductive JVMExceptionStep  (p:Program) : Method -> IntraNormalState -> ShortClassName -> Prop :=
  | arraylength_NullPointerException : forall h m pc s l,

    instructionAt m pc = Some Arraylength ->

    JVMExceptionStep p m (pc,(h,(Null::s),l))  NullPointerException

  | athrow_NullPointerException : forall h m pc s l,

    instructionAt m pc = Some Athrow ->

    JVMExceptionStep p m (pc,(h,(Null::s),l)) NullPointerException

  | checkcast_ClassCastException : forall h m pc s l loc t,

    instructionAt m pc = Some (Checkcast t) ->
    ~ assign_compatible p h (Ref loc) (ReferenceType t) ->

    JVMExceptionStep p m (pc,(h,(Ref loc::s),l)) ClassCastException

  | getfield_NullPointerException : forall h m pc s l f ,

    instructionAt m pc = Some (Getfield f) ->

    JVMExceptionStep p m (pc,(h,(Null::s),l)) NullPointerException

 | ibinop_ArithmeticException : forall h m pc s l op i1 i2,

    instructionAt m pc = Some (Ibinop op) ->
    op = DivInt \/ op = RemInt ->
    Int.toZ i2 = 0%Z ->

    JVMExceptionStep p m (pc,(h,(Num (I i2)::Num (I i1)::s),l)) ArithmeticException

  | invokevirtual_NullPointerException : forall h m pc s l mid args,

    instructionAt m pc = Some (Invokevirtual mid) ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->

    JVMExceptionStep p m (pc,(h,(args++Null::s),l)) NullPointerException

  | newarray_NegativeArraySizeException : forall h m pc s l t i,

    instructionAt m pc = Some (Newarray t) ->
    (~ 0 <= Int.toZ i)%Z ->

    JVMExceptionStep p m (pc,(h,(Num (I i)::s),l)) NegativeArraySizeException

  | putfield_NullPointerException : forall h m pc s l f v,

    instructionAt m pc = Some (Putfield f) ->
   
    JVMExceptionStep p m (pc,(h,(v::Null::s),l)) NullPointerException

  | vaload_NullPointerException : forall h m pc s l i k,

    instructionAt m pc = Some (Vaload k) ->

    JVMExceptionStep p m (pc,(h,((Num (I i))::Null::s),l)) NullPointerException

  | vaload_ArrayIndexOutOfBoundsException : forall h m pc s l loc i length t k a,

    instructionAt m pc = Some (Vaload k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    (~ 0 <= Int.toZ i < Int.toZ length)%Z ->

    JVMExceptionStep p m (pc,(h,((Num (I i))::(Ref loc)::s),l)) ArrayIndexOutOfBoundsException

  | vastore_NullPointerException : forall h m pc s l val i k,

    instructionAt m pc = Some (Vastore k) ->
    compat_ArrayKind_value k val ->

    JVMExceptionStep p m (pc,(h,(val::(Num (I i))::Null::s),l)) NullPointerException

  | vastore_ArrayIndexOutOfBoundsException : forall h m pc s l loc val i t length k a,

    instructionAt m pc = Some (Vastore k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    (~ 0 <= Int.toZ i < Int.toZ length)%Z ->
    compat_ArrayKind_type k t ->
    compat_ArrayKind_value k val ->

    JVMExceptionStep p m (pc,(h,(val::(Num (I i))::(Ref loc)::s),l)) ArrayIndexOutOfBoundsException

  | vastore_ArrayStoreException : forall h m pc s l loc val i t k length a,

    instructionAt m pc = Some (Vastore k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    ~ assign_compatible p h val t ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    compat_ArrayKind_type k t ->
    compat_ArrayKind_value k val ->

    JVMExceptionStep p m (pc,(h,(val::(Num (I i))::(Ref loc)::s),l)) ArrayStoreException
.






  Inductive ExceptionStep (p:Program) : Method -> IntraNormalState -> IntraExceptionState -> Prop :=
  | athrow : forall h m pc s l loc cn,

    instructionAt m pc = Some Athrow ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    subclass_name p cn javaLangThrowable ->
    ExceptionStep p m (pc,(h,(Ref loc::s),l)) (h,loc)

  | jvm_exception : forall h m pc s l h' loc (e:ShortClassName),

    JVMExceptionStep p m (pc,(h,s,l)) e ->
    Heap.new h p (Heap.LocationObject (javaLang,e)) = Some (loc,h') ->

    ExceptionStep p m (pc,(h,s,l)) (h',loc).
*)


  Inductive DEX_CallStep (p:DEX_Program) : DEX_Method -> DEX_IntraNormalState -> DEX_InitCallState -> Prop :=
  | invokestatic : forall h m pc l mid M args bM n,

    instructionAt m pc = Some (Invokestatic mid n args) ->
    findMethod p mid = Some M ->
    DEX_METHOD.isNative M = false ->
    length args = length (DEX_METHODSIGNATURE.parameters (snd mid)) ->
    DEX_METHOD.body M = Some bM ->
    DEX_METHOD.isStatic M = true ->
    
    DEX_CallStep p m (pc,(h, l)) (M, (listreg2regs l (length args) args))

  | invokevirtual : forall h m pc l mid M args loc bM n,

    instructionAt m pc = Some (Invokevirtual mid n args) ->
    (*lookup p cn mid (pair cl M) ->*)
    findMethod p mid = Some M ->
    DEX_Heap.typeof h loc = Some (DEX_Heap.LocationObject (fst mid)) ->
    length args = length (DEX_METHODSIGNATURE.parameters (snd mid)) ->
    DEX_METHOD.body M = Some bM ->
    DEX_METHOD.isStatic M = false ->
 
    DEX_CallStep p m (pc,(h, l)) (M,(listreg2regs l (length args) args))
  .

  Inductive DEX_ReturnStep (p:DEX_Program) : DEX_Method -> DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | void_return : forall h m pc l,

    instructionAt m pc = Some Return -> 
    DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = None ->

    DEX_ReturnStep p m (pc, (h, l)) (h, Normal None)

  | vreturn : forall h m pc l val t k rs,
    (* Implicit in the assumption is that the register has a value in it *)
    instructionAt m pc = Some (VReturn k rs) ->
    DEX_METHODSIGNATURE.result (DEX_METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->
    Some val = DEX_Registers.get l rs ->

    DEX_ReturnStep p m (pc, (h, l)) (h, Normal (Some val))
.


  Inductive DEX_call_and_return : DEX_Method -> DEX_IntraNormalState -> DEX_InitCallState -> DEX_IntraNormalState -> DEX_ReturnState -> DEX_IntraNormalState -> Prop :=
  | call_and_return_void : forall m pc h l m' l' bm' h'' pc',
      next m pc = Some pc' -> 
      DEX_METHOD.body m' = Some bm' ->
      DEX_call_and_return
                 m
                 (pc, (h,l))
                 (m', l')
                  (DEX_BYTECODEMETHOD.firstAddress bm',(h, l'))
                 (h'', Normal None) 
                 (pc',(h'', l))
  | call_and_return_value : forall m pc h l m' l' bm' h'' v pc' l'',
      next m pc = Some pc' -> 
      DEX_METHOD.body m' = Some bm' ->
      l'' = DEX_Registers.update l DEX_Registers.ret v ->
      DEX_call_and_return
                 m
                 (pc, (h, l))
                 (m', l')
                 (DEX_BYTECODEMETHOD.firstAddress bm',(h, l'))
                 (h'', Normal (Some v)) 
                 (pc',(h'', l'')).



(*
  Inductive call_and_return_exception : Method -> IntraNormalState -> InitCallState -> IntraNormalState -> ReturnState -> IntraExceptionState -> Prop :=
  | call_and_return_exception_def : forall m pc h s l m' l' bm' h'' s' loc,
      METHOD.body m' = Some bm' ->
      call_and_return_exception
                 m
                 (pc,(h,s,l))
                 (m',(s',l'))
                 (BYTECODEMETHOD.firstAddress bm',(h,OperandStack.empty,l'))
                 (h'',Exception loc) 
                 (h'',loc).
*)
  Inductive DEX_exec_intra (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
     DEX_NormalStep p m s1 s2 ->
     DEX_exec_intra p m s1 s2
  (*| exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc',
   ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
   CaughtException p m (pc1,h2,loc2) pc' ->
   exec_intra p m (pc1,(h1,s1,l1)) (pc',(h2,Ref loc2::OperandStack.empty,l1))*)
.

  Inductive DEX_exec_return (p:DEX_Program) (m:DEX_Method) : DEX_IntraNormalState -> DEX_ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     DEX_ReturnStep p m s (h,Normal ov) ->
     DEX_exec_return p m s (h,Normal ov)
(*  | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1,
     ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
     UnCaughtException  p m (pc1,h2,loc2) ->
     exec_return p m (pc1,(h1,s1,l1)) (h2,Exception loc2)*)
.

  Inductive DEX_exec_call (p:DEX_Program) (m:DEX_Method) :
   DEX_IntraNormalState -> DEX_ReturnState -> DEX_Method  -> DEX_IntraNormalState -> DEX_IntraNormalState+DEX_ReturnState -> Prop :=
 | exec_call_normal : forall m2 pc1 pc1' h1 l1 l2 h2 bm2 ov l1',
     DEX_CallStep p m (pc1,(h1, l1 )) (m2, l2) ->
     DEX_METHOD.body m2 = Some bm2 ->
     next m pc1 = Some pc1' ->
     l1' = DEX_Registers.update l1 DEX_Registers.ret ov ->
     DEX_exec_call p m
        (pc1,(h1, l1))
        (h2,Normal (Some ov))
        m2
        (DEX_BYTECODEMETHOD.firstAddress bm2, (h1, l2))
        (inl _ (pc1',(h2, l1')))
(*
 | exec_call_caught : forall m2 pc1 pc1' h1 s1 l1 os l2 h2 loc bm2,
     CallStep p m (pc1,(h1,s1,l1 )) (m2,(os,l2)) ->
     METHOD.body m2 = Some bm2 ->
     CaughtException p m (pc1, h2, loc) pc1' ->
     exec_call p m
        (pc1,(h1,s1,l1))
        (h2,Exception loc)
        m2
        (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2))
        (inl _(pc1',(h2,Ref loc::nil,l1)))
 | exec_call_uncaught : forall m2 pc1 h1 s1 l1 os l2 h2 loc bm2,
     CallStep p m (pc1,(h1,s1,l1 )) (m2,(os,l2)) ->
     METHOD.body m2 = Some bm2 ->
     UnCaughtException p m (pc1, h2, loc)  ->
     exec_call p m
       (pc1,(h1,s1,l1))
       (h2,Exception loc)
       m2
       (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2))
       (inr _ (h2,Exception loc))*).

 Inductive DEX_IntraStep (p:DEX_Program) : 
    DEX_Method -> DEX_IntraNormalState -> DEX_IntraNormalState + DEX_ReturnState -> Prop :=
  | IntraStep_res :forall m s ret,
     DEX_exec_return p m s ret ->
     DEX_IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2,
     DEX_exec_intra p m s1 s2 ->
     DEX_IntraStep p m s1 (inl _ s2) 
  | IntraStep_call :forall m m' s1 s' ret' r,
     DEX_exec_call p m s1 ret' m' s' r ->
     TransStep_l (DEX_IntraStep p m') s' (inr _ ret') ->
     DEX_IntraStep p m s1 r.
 
 Definition DEX_IntraStepStar p m s r := TransStep_l (DEX_IntraStep p m) s r.

 Definition DEX_IntraStepStar_intra p m s s' := DEX_IntraStepStar p m s (inl _ s').

 Definition DEX_BigStep  p m s ret := DEX_IntraStepStar p m s (inr _ ret).

 Inductive DEX_ReachableStep (P:DEX_Program) : 
      (DEX_Method*DEX_IntraNormalState)->(DEX_Method*DEX_IntraNormalState) ->Prop :=
   | ReachableIntra : forall M s s', 
       DEX_IntraStep P M s (inl _ s') ->
       DEX_ReachableStep P (M,s) (M,s')
   | Reachable_invS : forall M pc h l M' l' bm',
       DEX_CallStep P M (pc,(h, l)) (M', l') ->
       DEX_METHOD.body M' = Some bm' ->
       DEX_ReachableStep P (M, (pc,(h, l)))
         (M', (DEX_BYTECODEMETHOD.firstAddress bm',(h, l'))).

 Definition DEX_Reachable P M s s' := 
   exists M',  ClosReflTrans (DEX_ReachableStep P) (M,s) (M',s').
