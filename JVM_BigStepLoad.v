
  Import JVM_Dom JVM_Prog.

  Open Scope type_scope.
  Definition JVM_InitCallState :=  JVM_Method * (JVM_OperandStack.t * JVM_LocalVar.t).
  Definition JVM_IntraNormalState := JVM_PC * (JVM_Heap.t * JVM_OperandStack.t * JVM_LocalVar.t).
(* DEX  Definition JVM_IntraExceptionState := JVM_Heap.t * JVM_Location. *)
  Definition JVM_ReturnState := JVM_Heap.t * JVM_ReturnVal.


  Inductive JVM_NormalStep (p:JVM_Program) : JVM_Method -> JVM_IntraNormalState -> JVM_IntraNormalState  -> Prop :=
  | aconst_null : forall h m pc pc' s l,

    instructionAt m pc = Some (JVM_Aconst_null) ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,s,l)) (pc',(h,(Null::s),l))

  | arraylength : forall h m pc pc' s l loc length tp a, 

    instructionAt m pc = Some (JVM_Arraylength) ->
    next m pc = Some pc' ->
    JVM_Heap.typeof  h loc = Some (JVM_Heap.LocationArray length tp a) ->

   JVM_NormalStep p m  (pc,(h,(Ref loc::s),l)) (pc',(h,(Num (I length)::s),l))
(*
 | checkcast1 : forall h m pc pc' s l val t,

    instructionAt m pc = Some (JVM_Checkcast t) ->
    next m pc = Some pc' ->
    assign_compatible p h val (JVM_ReferenceType t) ->

   JVM_NormalStep p m (pc,(h,(val::s),l))  (pc',(h,(val::s),l))
*)
  | const : forall h m pc pc' s l t z,

    instructionAt m pc = Some (JVM_Const t z) ->
    next m pc = Some pc' ->
    (   (t=JVM_BYTE /\ -2^7 <= z < 2^7)%Z
     \/ (t=JVM_SHORT /\ -2^15 <= z < 2^15)%Z
     \/ (t=JVM_INT /\ -2^31 <= z < 2^31)%Z   ) ->

   JVM_NormalStep p m (pc,(h,s,l)) (pc',(h,(Num (I (Int.const z))::s),l))

  | dup : forall h m pc pc' s l v,

    instructionAt m pc = Some (JVM_Dup) ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v::s),l))  (pc',(h,(v::v::s),l))

  | dup_x1 : forall h m pc pc' s l v1 v2,

    instructionAt m pc = Some JVM_Dup_x1 ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::s),l)) (pc',(h,(v1::v2::v1::s),l))

  | dup_x2 : forall h m pc pc' s l v1 v2 v3,

    instructionAt m pc = Some JVM_Dup_x2 ->
    next m pc = Some pc' ->

   JVM_NormalStep p  m (pc,(h,(v1::v2::v3::s),l))  (pc',(h,(v1::v2::v3::v1::s),l))

  | dup2 : forall h m pc pc' s l v1 v2,

    instructionAt m pc = Some JVM_Dup2 ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::s),l)) (pc',(h,(v1::v2::v1::v2::s),l))

  | dup2_x1 : forall h m pc pc' s l v1 v2 v3,

    instructionAt m pc = Some JVM_Dup2_x1 ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::v3::s),l)) (pc',(h,(v1::v2::v3::v1::v2::s),l))

  | dup2_x2 : forall h m pc pc' s l v1 v2 v3 v4,

    instructionAt m pc = Some JVM_Dup2_x2 ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::v3::v4::s),l)) (pc',(h,(v1::v2::v3::v4::v1::v2::s),l))

  | getfield : forall h m pc pc' s l loc f v cn,

    instructionAt m pc = Some (JVM_Getfield f) ->
    next m pc = Some pc' ->
    JVM_Heap.typeof h loc = Some (JVM_Heap.LocationObject cn) -> 
    defined_field p cn f ->
    JVM_Heap.get h (JVM_Heap.DynamicField loc f) = Some v ->    

   JVM_NormalStep p m (pc,(h,(Ref loc::s),l)) (pc',(h,(v::s),l))

  | goto : forall h m pc s l o,

    instructionAt m pc = Some (JVM_Goto o) ->

   JVM_NormalStep p m (pc,(h,s,l)) (JVM_OFFSET.jump pc o,(h,s,l))

  | i2b : forall h m pc pc' s l i,

    instructionAt m pc = Some JVM_I2b ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (pc',(h,(Num (I (b2i (i2b i)))::s),l))

  | i2s : forall h m pc pc' s l i,

    instructionAt m pc = Some JVM_I2s ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l))  (pc',(h,(Num (I (s2i (i2s i)))::s),l))

  | ibinop : forall h m pc pc' s l op i1 i2,

    instructionAt m pc = Some (JVM_Ibinop op) ->
    next m pc = Some pc' ->
    (* DEX (op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0%Z) -> *)

   JVM_NormalStep p m (pc,(h,(Num (I i2)::Num (I i1)::s),l))
                          (pc',(h,(Num (I (SemBinopInt op i1 i2))::s),l))

  | if_acmp_step_jump : forall h m pc s l val2 val1 o cmp,
      instructionAt m pc = Some (JVM_If_acmp cmp o) ->
      SemCompRef cmp val1 val2 ->
  (******************************************************************)
     JVM_NormalStep p m (pc,(h,(val2:: val1::s),l))
                                   (JVM_OFFSET.jump pc o,(h,s,l))

  | if_acmp_step_continue : forall h m pc pc' s l val2 val1 o cmp,
      instructionAt m pc = Some (JVM_If_acmp cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompRef cmp val1 val2 ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(val2::val1::s),l)) (pc',(h,s,l))

  | if_icmp_step_jump : forall h m pc s l cmp i2 i1 o,
      instructionAt m pc = Some (JVM_If_icmp cmp o) ->
      SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(Num(I i2)::Num(I i1)::s),l))
                                  (JVM_OFFSET.jump pc o,(h,s,l))

  | if_icmpeq_step_continue : forall h m pc pc' s l cmp i2 i1 o,
      instructionAt m pc = Some (JVM_If_icmp cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(Num(I i2)::Num(I i1)::s),l))
                                  (pc',(h,s,l))

  | ifeq_step_jump : forall h m pc s l cmp i o,
      instructionAt m pc = Some (JVM_If0 cmp o) ->
      SemCompInt cmp (Int.toZ i) 0 ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(Num(I i)::s),l))
                                  (JVM_OFFSET.jump pc o,(h,s,l))

  | ifeq_step_continue : forall h m pc pc' s l cmp i o,
      instructionAt m pc = Some (JVM_If0 cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompInt cmp (Int.toZ i) 0 ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(Num(I i)::s),l)) (pc',(h,s,l))

  | ifnull_step_jump : forall h m pc s l loc o cmp,
      instructionAt m pc = Some (JVM_Ifnull cmp o) ->
      SemCompRef cmp loc Null ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(loc::s),l))
                                  (JVM_OFFSET.jump pc o,(h,s,l))

  | ifnull_step_continue : forall h m pc pc' s l o loc cmp,
    instructionAt m pc = Some (JVM_Ifnull cmp o) ->
    next m pc = Some pc' ->
    ~ SemCompRef cmp loc Null ->
  (******************************************************************)
    JVM_NormalStep p m (pc,(h,(loc::s),l)) (pc',(h,s,l))


  | iinc_step : forall h m pc s l pc' x z i,
    instructionAt m pc = Some (JVM_Iinc x z) ->

    next m pc = Some pc' ->
    (-2^7 <= z < 2^7)%Z ->
    JVM_METHOD.valid_var m x ->
    JVM_LocalVar.get l x = Some (Num (I i)) ->

   JVM_NormalStep p m (pc,(h,s,l))
                (pc',(h,s,(JVM_LocalVar.update l x (Num (I (Int.add i (Int.const z)))))))

  | ineg_step : forall h m pc s l pc' i,
    instructionAt m pc = Some JVM_Ineg ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (pc',(h,(Num (I (Int.neg i))::s),l))

  | instanceof1 : forall h m pc pc' s l loc t,

    instructionAt m pc = Some (JVM_Instanceof t) ->
    next m pc = Some pc' ->
    assign_compatible p h (Ref loc) (JVM_ReferenceType t) ->

   JVM_NormalStep p m (pc,(h,(Ref loc::s),l)) (pc',(h,(Num (I (Int.const 1))::s),l))


  | instanceof2 : forall h m pc pc' s l t v,

    instructionAt m pc = Some (JVM_Instanceof t) ->
    next m pc = Some pc' ->
    isReference v ->
    (~ assign_compatible p h v (JVM_ReferenceType t) \/ v=Null) ->

   JVM_NormalStep p m (pc,(h,(v::s),l)) (pc',(h,(Num (I (Int.const 0))::s),l))


  | lookupswitch1 : forall h m pc s l def listkey i i' o',

    instructionAt m pc = Some (JVM_Lookupswitch def listkey) ->

    List.In (pair i' o')listkey ->
    i' = Int.toZ i ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (JVM_OFFSET.jump pc o',(h,s,l))

  | lookupswitch2 : forall h m pc s l def listkey i,

    instructionAt m pc = Some (JVM_Lookupswitch def listkey) ->
    (forall i' o', List.In (pair i' o')listkey ->  i' <> Int.toZ i) ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (JVM_OFFSET.jump pc def,(h,s,l))

  | new : forall h m pc pc' s l c loc h',

    instructionAt m pc = Some (JVM_New c) ->
    next m pc = Some pc' ->
    JVM_Heap.new h p (JVM_Heap.LocationObject c) = Some (pair loc h') ->

   JVM_NormalStep p m (pc,(h,s,l))
                      (pc',(h',(Ref loc::s),l))

  | newarray : forall h m pc pc' s l t i loc h',

    instructionAt m pc = Some (JVM_Newarray t) ->
    next m pc = Some pc' ->
    (0 <= Int.toZ i)%Z -> 
    JVM_Heap.new h p (JVM_Heap.LocationArray i t (m,pc)) = Some (pair loc h') ->

   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l))
                            (pc',(h',(Ref loc::s),l))

  | nop : forall h m pc pc' s l,

    instructionAt m pc = Some JVM_Nop ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,s,l)) (pc',(h,s,l))

  | pop : forall h m pc pc' s l v,

    instructionAt m pc = Some JVM_Pop ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v::s),l)) (pc',(h,s,l))

  | pop2 : forall h m pc pc' s l v1 v2,

    instructionAt m pc = Some JVM_Pop2 ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::s),l)) (pc',(h,s,l))

  | putfield : forall h m pc pc' s l f loc cn v,

    instructionAt m pc = Some (JVM_Putfield f) ->
    next m pc = Some pc' ->
    JVM_Heap.typeof h loc = Some (JVM_Heap.LocationObject cn) -> 
    defined_field p cn f ->
    assign_compatible p h v (JVM_FIELDSIGNATURE.type (snd f)) ->

   JVM_NormalStep p m(pc,(h,(v::(Ref loc)::s),l))
                           (pc',(JVM_Heap.update h (JVM_Heap.DynamicField loc f) v,s,l))

  | swap : forall h m pc pc' s l v1 v2,

    instructionAt m pc = Some JVM_Swap ->
    next m pc = Some pc' ->

   JVM_NormalStep p m (pc,(h,(v1::v2::s),l)) (pc',(h,(v2::v1::s),l))

  | tableswitch1 : forall h m pc s l i def low high list_offset,

    instructionAt m pc = Some (JVM_Tableswitch def low high list_offset) ->
    Z_of_nat (length list_offset) = (high - low + 1)%Z ->
    (Int.toZ i < low \/ high < Int.toZ i)%Z ->
   
   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (JVM_OFFSET.jump pc def,(h,s,l))

  | tableswitch2 : forall h m pc s l n o i def low high list_offset,

    instructionAt m pc = Some (JVM_Tableswitch def low high list_offset) ->
    Z_of_nat (length list_offset) = (high - low + 1)%Z ->
    (low <= Int.toZ i <= high)%Z ->
    (Z_of_nat n = (Int.toZ i) - low)%Z ->
    nth_error list_offset n = Some o ->
   
   JVM_NormalStep p m (pc,(h,(Num (I i)::s),l)) (JVM_OFFSET.jump pc o,(h,s,l))

  | vaload : forall h m pc pc' s l loc val i length t k a,

    instructionAt m pc = Some (JVM_Vaload k) ->
    next m pc = Some pc' ->
    JVM_Heap.typeof h loc = Some (JVM_Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    JVM_Heap.get h (JVM_Heap.ArrayElement loc (Int.toZ i)) = Some val ->
    compat_ArrayKind_value k val ->

    JVM_NormalStep p m 
          (pc,(h,((Num (I i))::(Ref loc)::s),l))
          (pc',(h,(conv_for_stack val::s),l))

  | vastore : forall h m pc pc' s l loc val i length t k a,

    instructionAt m pc = Some (JVM_Vastore k) ->
    next m pc = Some pc' ->
    JVM_Heap.typeof h loc = Some (JVM_Heap.LocationArray length t a) ->
    assign_compatible p h val t ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    compat_ArrayKind_type k t ->
    compat_ArrayKind_value k val ->

    JVM_NormalStep p m
         (pc,(h,(val::(Num (I i))::(Ref loc)::s),l))
         (pc',(JVM_Heap.update h (JVM_Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val t),s,l))

  | vload : forall h m pc pc' s l x val k,

    instructionAt m pc = Some (JVM_Vload k x) ->
    next m pc = Some pc' ->
    JVM_METHOD.valid_var m x ->
    JVM_LocalVar.get l x = Some val ->
    compat_ValKind_value k val -> 

    JVM_NormalStep p m (pc,(h,s,l)) (pc',(h,(val::s),l))
 
  | vstore : forall h m pc pc' s l l' x v k,

    instructionAt m pc = Some (JVM_Vstore k x) ->
    next m pc = Some pc' ->
    JVM_METHOD.valid_var m x ->
    l' = JVM_LocalVar.update l x v ->
    compat_ValKind_value k v ->

   JVM_NormalStep p m  (pc,(h,(v::s),l)) (pc',(h,s,l'))
.

(* DEX
  Inductive JVMExceptionStep  (p:Program) : Method -> IntraNormalState -> ShortClassName -> Prop :=
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






  Inductive JVM_CallStep (p:JVM_Program) : JVM_Method -> JVM_IntraNormalState -> JVM_InitCallState -> Prop :=
  | invokestatic : forall h m pc s l mid M args bM,

    instructionAt m pc = Some (JVM_Invokestatic mid) ->
    findMethod p mid = Some M ->
    JVM_METHOD.isNative M = false ->
    length args = length (JVM_METHODSIGNATURE.parameters (snd mid)) ->
    JVM_METHOD.body M = Some bM ->
    JVM_METHOD.isStatic M = true ->
    
    JVM_CallStep p m (pc,(h,(args++s),l)) (M,(s,(stack2localvar (args++s) (length args))))

  | invokevirtual : forall h m pc s l mid cn M args loc cl bM,

    instructionAt m pc = Some (JVM_Invokevirtual (cn,mid)) ->
    lookup p cn mid (pair cl M) ->
    JVM_Heap.typeof h loc = Some (JVM_Heap.LocationObject cn) ->
    length args = length (JVM_METHODSIGNATURE.parameters mid) ->
    JVM_METHOD.body M = Some bM ->
    JVM_METHOD.isStatic M = false ->
 
    JVM_CallStep p m (pc,(h,(args++(Ref loc)::s),l)) (M,(s,stack2localvar (args++(Ref loc)::s)  (1+(length args)))).



  Inductive JVM_ReturnStep (p:JVM_Program) : JVM_Method -> JVM_IntraNormalState -> JVM_ReturnState -> Prop :=
  | void_return : forall h m pc s l,

    instructionAt m pc = Some JVM_Return ->
    JVM_METHODSIGNATURE.result (JVM_METHOD.signature m) = None ->

    JVM_ReturnStep p m  (pc,(h,s,l)) (h, Normal None)
  | vreturn : forall h m pc s l val t k,

    instructionAt m pc = Some (JVM_Vreturn k) ->
    JVM_METHODSIGNATURE.result (JVM_METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->

    JVM_ReturnStep p m (pc,(h,(val::s),l)) (h,Normal (Some val))
.






  Inductive JVM_call_and_return : 
    JVM_Method -> JVM_IntraNormalState -> JVM_InitCallState -> JVM_IntraNormalState -> JVM_ReturnState -> JVM_IntraNormalState -> Prop :=
  | call_and_return_void : forall m pc h s l m' l' bm' h'' s' pc',
      next m pc = Some pc' -> 
      JVM_METHOD.body m' = Some bm' ->
      JVM_call_and_return
                 m
                 (pc,(h,s,l))
                 (m',(s',l'))
                  (JVM_BYTECODEMETHOD.firstAddress bm',(h,JVM_OperandStack.empty,l'))
                 (h'', Normal None) 
                 (pc',(h'',s',l))
  | call_and_return_value : forall m pc h s l m' l' bm' h'' v s' pc',
      next m pc = Some pc' -> 
      JVM_METHOD.body m' = Some bm' ->
      JVM_call_and_return
                 m
                 (pc,(h,s,l))
                 (m',(s',l') )
                 (JVM_BYTECODEMETHOD.firstAddress bm',(h,JVM_OperandStack.empty,l'))
                 (h'', Normal (Some v)) 
                 (pc',(h'',v::s',l)).




(* DEX
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
  Inductive JVM_exec_intra (p:JVM_Program) (m:JVM_Method) : JVM_IntraNormalState -> JVM_IntraNormalState -> Prop :=
  | exec_intra_normal : forall s1 s2,
     JVM_NormalStep p m s1 s2 ->
     JVM_exec_intra p m s1 s2
(* DEX  | exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc',
   ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
   CaughtException p m (pc1,h2,loc2) pc' ->
   exec_intra p m (pc1,(h1,s1,l1)) (pc',(h2,Ref loc2::OperandStack.empty,l1))*).

  Inductive JVM_exec_return (p:JVM_Program) (m:JVM_Method) : JVM_IntraNormalState -> JVM_ReturnState -> Prop :=
  | exec_return_normal : forall s h ov,
     JVM_ReturnStep p m s (h,Normal ov) ->
     JVM_exec_return p m s (h,Normal ov)
  (* DEX | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1,
     ExceptionStep p m (pc1,(h1,s1,l1)) (h2,loc2) ->
     UnCaughtException  p m (pc1,h2,loc2) ->
     exec_return p m (pc1,(h1,s1,l1)) (h2,Exception loc2)*).

  Inductive JVM_exec_call (p:JVM_Program) (m:JVM_Method) :
   JVM_IntraNormalState -> JVM_ReturnState -> JVM_Method  -> JVM_IntraNormalState -> JVM_IntraNormalState+JVM_ReturnState -> Prop :=
 | exec_call_normal : forall m2 pc1 pc1' h1 s1 l1 os l2 h2 bm2 ov,
     JVM_CallStep p m (pc1,(h1,s1,l1 )) (m2,(os,l2)) ->
     JVM_METHOD.body m2 = Some bm2 ->
     next m pc1 = Some pc1' ->
     JVM_exec_call p m
        (pc1,(h1,s1,l1))
        (h2,Normal ov)
        m2
        (JVM_BYTECODEMETHOD.firstAddress bm2,(h1,JVM_OperandStack.empty,l2))
        (inl _ (pc1',(h2,cons_option ov os,l1)))
(* DEX
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
       (inr _ (h2,Exception loc))*) .

 Inductive JVM_IntraStep (p:JVM_Program) : 
    JVM_Method -> JVM_IntraNormalState -> JVM_IntraNormalState + JVM_ReturnState -> Prop :=
  | IntraStep_res :forall m s ret,
     JVM_exec_return p m s ret ->
     JVM_IntraStep p m s (inr _ ret)
  | IntraStep_intra_step:forall m s1 s2,
     JVM_exec_intra p m s1 s2 ->
     JVM_IntraStep p m s1 (inl _ s2) 
  | IntraStep_call :forall m m' s1 s' ret' r,
     JVM_exec_call p m s1 ret' m' s' r ->
     TransStep_l (JVM_IntraStep p m') s' (inr _ ret') ->
     JVM_IntraStep p m s1 r.
 
 Definition JVM_IntraStepStar p m s r := TransStep_l (JVM_IntraStep p m) s r.

 Definition JVM_IntraStepStar_intra p m s s' := JVM_IntraStepStar p m s (inl _ s').

 Definition JVM_BigStep  p m s ret := JVM_IntraStepStar p m s (inr _ ret).

 Inductive JVM_ReachableStep (P:JVM_Program) : 
      (JVM_Method*JVM_IntraNormalState)->(JVM_Method*JVM_IntraNormalState) ->Prop :=
   | ReachableIntra : forall M s s', 
       JVM_IntraStep P M s (inl _ s') ->
       JVM_ReachableStep P (M,s) (M,s')
   | Reachable_invS : forall M pc h os l M' os' l' bm',
       JVM_CallStep P M (pc,(h,os,l)) (M',(os',l')) ->
       JVM_METHOD.body M' = Some bm' ->
       JVM_ReachableStep P (M, (pc,(h,os,l)))
         (M', (JVM_BYTECODEMETHOD.firstAddress bm',(h,JVM_OperandStack.empty,l'))).

 Definition JVM_Reachable P M s s' := 
   exists M',  ClosReflTrans (JVM_ReachableStep P) (M,s) (M',s').
