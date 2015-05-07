
  Import Dom Prog.

  Open Scope type_scope.
  Definition InitCallState :=  Method * LocalVar.t.
  Definition IntraNormalState := PC * (Heap.t * LocalVar.t).
(*  Definition IntraExceptionState := Heap.t * Location. *)
  Definition ReturnState := Heap.t * ReturnVal.


  Inductive NormalStep (p:Program) : Method -> IntraNormalState -> IntraNormalState  -> Prop :=
  | nop : forall h m pc pc' l,

    instructionAt m pc = Some Nop ->
    next m pc = Some pc' ->

    NormalStep p m (pc,(h, l)) (pc',(h, l))

  | const : forall h m pc pc' l l' k rt v,

    instructionAt m pc = Some (Const k rt v) ->
    next m pc = Some pc' ->
    (-2^31 <= v < 2^31)%Z ->
    METHOD.valid_var m rt ->
    l' = LocalVar.update l rt (Num (I (Int.const v))) ->

    NormalStep p m (pc,(h, l)) (pc',(h, l'))
  
  | move_step_ok : forall h m pc pc' l l' k rt rs v,

    instructionAt m pc = Some (Move k rt rs) ->
    next m pc = Some pc' ->
    Some v = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt v ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  | moveresult_step_ok : forall h m pc pc' l l' k rt v,

    instructionAt m pc = Some (MoveResult k rt) ->
    next m pc = Some pc' ->
    Some v = LocalVar.get l LocalVar.ret ->
    METHOD.valid_var m rt ->
    l' = LocalVar.update l rt v ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

 (** <addlink>instanceof</addlink>: Determine if object is of given type *)
  | instanceof_step_ok1 : forall h m pc pc' l loc rt r t l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l r ->
    assign_compatible p h (Ref loc) (ReferenceType t) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l' rt (Num (I (Int.const 1))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))
 (** <addlink>instanceof</addlink>: with object == null *)
  | instanceof_step_ok2 : forall h m pc pc' l rt r t v l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some v = LocalVar.get l r ->
    isReference v ->
    (~ assign_compatible p h v (ReferenceType t) \/ v=Null) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l' rt (Num (I (Int.const 0))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  (** <addlink>arraylength</addlink>: Get length of array *)
  | arraylength_step_ok : forall h m pc pc' l l' loc length tp a rt rs,

    instructionAt m pc = Some (ArrayLength rt rs)->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l rs ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Num (I length)) ->
    
    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>new</addlink>: Create new object *)
  | new_step_ok : forall h m pc pc' l l' c loc h' rt,

    instructionAt m pc = Some (New rt (ClassType c)) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc h') ->
    METHOD.valid_var m rt ->
    l' = LocalVar.update l rt (Ref loc) ->

    NormalStep p m (pc, (h, l)) (pc', (h', l'))

 (** Create new array (<addlink>anewarray</addlink>, <addlink>newarray</addlink>) *)
 (** OutOfMemory is not considered in Bicolano *)
  | newarray_step_ok : forall h m pc pc' l l' i t loc h_new rt rl,

    instructionAt m pc = Some (NewArray rt rl t) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationArray i t (m,pc)) = Some (pair loc h_new) ->
    Some (Num (I i)) = LocalVar.get l rl ->
    (0 <= Int.toZ i)%Z ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rl ->
    l' = LocalVar.update l rt (Ref loc) ->

    NormalStep p m (pc, (h, l)) (pc', (h_new, l'))

  | goto_step_ok : forall h m pc l o,

    instructionAt m pc = Some (Goto o) ->

    NormalStep p m (pc, (h, l)) ((OFFSET.jump pc o), (h, l))
  
  | packedswitch_step_ok1 : forall h m pc l v r firstKey size list_offset n o,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = LocalVar.get l r ->
    (firstKey <= Int.toZ v < firstKey + size)%Z ->
    Z_of_nat (length list_offset) = size ->
    Z_of_nat n = ((Int.toZ v) - firstKey)%Z ->
    nth_error list_offset n = Some o ->
    METHOD.valid_var m r ->
    
    NormalStep p m (pc, (h, l)) ((OFFSET.jump pc o), (h, l))

  | packedswitch_step_ok2 : forall h m pc pc' l v r firstKey size list_offset,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = LocalVar.get l r ->
    Z_of_nat (length list_offset) = size ->
    (Int.toZ v < firstKey \/ firstKey + size <= Int.toZ v)%Z ->
    next m pc = Some pc' ->
    METHOD.valid_var m r ->

    NormalStep p m (pc, (h, l)) (pc', (h, l))
  
  | sparseswitch_step_ok1 : forall h m pc l v v' o r size listkey,
    
    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = LocalVar.get l r ->
    List.In (pair v' o) listkey ->
    v' = Int.toZ v ->
    METHOD.valid_var m r ->
    
    NormalStep p m (pc, (h, l)) ((OFFSET.jump pc o), (h, l))

  | sparseswitch_step_ok2 : forall h m pc pc' l v r size listkey,

    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = LocalVar.get l r ->
    (forall v' o, List.In (pair v' o) listkey ->  v' <> Int.toZ v) ->
    next m pc = Some pc' ->
    METHOD.valid_var m r ->

    NormalStep p m (pc, (h, l)) (pc', (h, l))

  | ifcmp_step_jump : forall h m pc l va vb cmp ra rb o,

    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->
    
    NormalStep p m (pc, (h, l)) ((OFFSET.jump pc o), (h, l))

  | ifcmp_step_continue : forall h m pc pc' l va vb cmp ra rb o,
    
    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    ~SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    next m pc = Some pc' ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->

    NormalStep p m (pc, (h, l)) (pc', (h, l))

  | ifz_step_jump : forall h m pc l v cmp r o,

    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = LocalVar.get l r ->
    SemCompInt cmp (Int.toZ v) (0) ->
    METHOD.valid_var m r ->
    
    NormalStep p m (pc, (h, l)) ((OFFSET.jump pc o), (h, l))

  | ifz_step_continue : forall h m pc pc' l v cmp r o,
    
    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = LocalVar.get l r ->
    ~SemCompInt cmp (Int.toZ v) (0) ->
    next m pc = Some pc' ->

    NormalStep p m (pc, (h, l)) (pc', (h, l))

   (** Load value from array *)
  | aget_step_ok : forall h m pc pc' l l' loc val i length t a k rt ra ri,

    instructionAt m pc = Some (Aget k rt ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ra ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    Some (Num (I i)) = LocalVar.get l ri ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    Heap.get h (Heap.ArrayElement loc (Int.toZ i)) = Some val ->
    compat_ArrayKind_value k val ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m ri ->
    l' = LocalVar.update l rt (conv_for_stack val) -> 

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** Store into array *)
  | aput_step_ok : forall h m pc pc' l loc val i length tp k a rs ra ri, 

    instructionAt m pc = Some (Aput k rs ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ra ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    Some val = LocalVar.get l rs ->
    assign_compatible p h val tp ->
    Some (Num (I i)) = LocalVar.get l ri ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->
    METHOD.valid_var m rs ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m ri ->

    NormalStep p m (pc, (h, l))
                   (pc',((Heap.update h (Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val tp)), l))

  (** <addlink>iget</addlink>: Fetch field from object *)
  | iget_step_ok : forall h m pc pc' l l' loc f v cn k rt ro,

    instructionAt m pc = Some (Iget k rt ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ro ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Heap.get h (Heap.DynamicField loc f) = Some v ->    
    METHOD.valid_var m rt ->
    METHOD.valid_var m ro ->
    l' = LocalVar.update l rt v ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))
  
  (** <addlink>iput</addlink>: Set field in object *)
  | iput_step_ok : forall h m pc pc' l f loc cn v k rs ro,

    instructionAt m pc = Some (Iput k rs ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ro ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Some v = LocalVar.get l rs ->
    assign_compatible p h v (FIELDSIGNATURE.type (snd f)) ->
    METHOD.valid_var m rs ->
    METHOD.valid_var m ro ->

    NormalStep p m (pc, (h, l))
           (pc, ((Heap.update h (Heap.DynamicField loc f) v), l))

  (* TODO : Invokevirtual *)
  (* TODO : Invokesuper *)
  (* TODO : Invokedirect *)
  (* TODO : Invokestatic *)
  (* TODO : Invokeinterface *)

  (** <addlink>ineg</addlink>: Negate [int] *)
  | ineg_step : forall h m pc l l' pc' rt rs v,

    instructionAt m pc = Some (Ineg rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Num (I (Int.neg v))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>ineg</addlink>: Not [int] (one's complement) *)
  | inot_step : forall h m pc l l' pc' rt rs v,

    instructionAt m pc = Some (Inot rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Num (I (Int.not v))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  (** <addlink>i2b</addlink>: Convert [int] to [byte] *)
  | i2b_step_ok : forall h m pc pc' l l' rt rs v,

    instructionAt m pc = Some (I2b rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Num (I (b2i (i2b v)))) ->
    
    NormalStep p m (pc, (h, l)) (pc', (h, l'))

 (** <addlink>i2s</addlink>: Convert [int] to [short] *)
  | i2s_step_ok : forall h m pc pc' l l' rt rs v,

    instructionAt m pc = Some (I2s rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Num (I (s2i (i2s v)))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  | ibinop_step_ok : forall h m pc pc' l l' op rt ra rb va vb,

    instructionAt m pc = Some (Ibinop op rt ra rb) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->
    l' = LocalVar.update l rt (Num (I (SemBinopInt op va vb))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))

  | ibinopconst_step_ok : forall h m pc pc' l l' op rt r va v,

    instructionAt m pc = Some (IbinopConst op rt r v) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = LocalVar.get l r ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l rt (Num (I (SemBinopInt op va (Int.const v)))) ->

    NormalStep p m (pc, (h, l)) (pc', (h, l'))
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


  Inductive CallStep (p:Program) : Method -> IntraNormalState -> InitCallState -> Prop :=
  | invokestatic : forall h m pc l mid M args bM n,

    instructionAt m pc = Some (Invokestatic mid n args) ->
    findMethod p mid = Some M ->
    METHOD.isNative M = false ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    METHOD.body M = Some bM ->
    METHOD.isStatic M = true ->
    
    CallStep p m (pc,(h, l)) (M, (listvar2localvar l (length args) args))

  | invokevirtual : forall h m pc l mid M args loc bM n,

    instructionAt m pc = Some (Invokevirtual mid n args) ->
    (*lookup p cn mid (pair cl M) ->*)
    findMethod p mid = Some M ->
    Heap.typeof h loc = Some (Heap.LocationObject (fst mid)) ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    METHOD.body M = Some bM ->
    METHOD.isStatic M = false ->
 
    CallStep p m (pc,(h, l)) (M,(listvar2localvar l (length args) args))
  .

  Inductive ReturnStep (p:Program) : Method -> IntraNormalState -> ReturnState -> Prop :=
  | void_return : forall h m pc l,

    instructionAt m pc = Some Return -> 
    METHODSIGNATURE.result (METHOD.signature m) = None ->

    ReturnStep p m (pc, (h, l)) (h, Normal None)

  | vreturn : forall h m pc l val t k rs,
    (* Implicit in the assumption is that the register has a value in it *)
    instructionAt m pc = Some (VReturn k rs) ->
    METHODSIGNATURE.result (METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->
    Some val = LocalVar.get l rs ->

    ReturnStep p m (pc, (h, l)) (h, Normal (Some val))
.


  Inductive call_and_return : Method -> IntraNormalState -> InitCallState -> IntraNormalState -> ReturnState -> IntraNormalState -> Prop :=
  | call_and_return_void : forall m pc h l m' l' bm' h'' pc',
      next m pc = Some pc' -> 
      METHOD.body m' = Some bm' ->
      call_and_return
                 m
                 (pc, (h,l))
                 (m', l')
                  (BYTECODEMETHOD.firstAddress bm',(h, l'))
                 (h'', Normal None) 
                 (pc',(h'', l))
  | call_and_return_value : forall m pc h l m' l' bm' h'' v pc' l'',
      next m pc = Some pc' -> 
      METHOD.body m' = Some bm' ->
      l'' = LocalVar.update l LocalVar.ret v ->
      call_and_return
                 m
                 (pc, (h, l))
                 (m', l')
                 (BYTECODEMETHOD.firstAddress bm',(h, l'))
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
  Inductive exec_intra (p:Program) (m:Method) : IntraNormalState -> IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
     NormalStep p m s1 s2 ->
     exec_intra p m s1 s2
  (*| exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc',
   ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
   CaughtException p m (pc1,h2,loc2) pc' ->
   exec_intra p m (pc1,(h1,s1,l1)) (pc',(h2,Ref loc2::OperandStack.empty,l1))*)
.

  Inductive exec_return (p:Program) (m:Method) : IntraNormalState -> ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     ReturnStep p m s (h,Normal ov) ->
     exec_return p m s (h,Normal ov)
(*  | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1,
     ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
     UnCaughtException  p m (pc1,h2,loc2) ->
     exec_return p m (pc1,(h1,s1,l1)) (h2,Exception loc2)*)
.

  Inductive exec_call (p:Program) (m:Method) :
   IntraNormalState -> ReturnState -> Method  -> IntraNormalState -> IntraNormalState+ReturnState -> Prop :=
 | exec_call_normal : forall m2 pc1 pc1' h1 l1 l2 h2 bm2 ov l1',
     CallStep p m (pc1,(h1, l1 )) (m2, l2) ->
     METHOD.body m2 = Some bm2 ->
     next m pc1 = Some pc1' ->
     l1' = LocalVar.update l1 LocalVar.ret ov ->
     exec_call p m
        (pc1,(h1, l1))
        (h2,Normal (Some ov))
        m2
        (BYTECODEMETHOD.firstAddress bm2, (h1, l2))
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

 Inductive IntraStep (p:Program) : 
    Method -> IntraNormalState -> IntraNormalState + ReturnState -> Prop :=
  | IntraStep_res :forall m s ret,
     exec_return p m s ret ->
     IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2,
     exec_intra p m s1 s2 ->
     IntraStep p m s1 (inl _ s2) 
  | IntraStep_call :forall m m' s1 s' ret' r,
     exec_call p m s1 ret' m' s' r ->
     TransStep_l (IntraStep p m') s' (inr _ ret') ->
     IntraStep p m s1 r.
 
 Definition IntraStepStar p m s r := TransStep_l (IntraStep p m) s r.

 Definition IntraStepStar_intra p m s s' := IntraStepStar p m s (inl _ s').

 Definition BigStep  p m s ret := IntraStepStar p m s (inr _ ret).

 Inductive ReachableStep (P:Program) : 
      (Method*IntraNormalState)->(Method*IntraNormalState) ->Prop :=
   | ReachableIntra : forall M s s', 
       IntraStep P M s (inl _ s') ->
       ReachableStep P (M,s) (M,s')
   | Reachable_invS : forall M pc h l M' l' bm',
       CallStep P M (pc,(h, l)) (M', l') ->
       METHOD.body M' = Some bm' ->
       ReachableStep P (M, (pc,(h, l)))
         (M', (BYTECODEMETHOD.firstAddress bm',(h, l'))).

 Definition Reachable P M s s' := 
   exists M',  ClosReflTrans (ReachableStep P) (M,s) (M',s').
