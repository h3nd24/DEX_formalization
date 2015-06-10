(** * Bicolano: Semantic domains *)

(* <Insert License Here>

    $Id: Domain.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

(** Formalization of Java semantic domain.
 Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
  Tim Lindholm, Frank Yellin"

 @author David Pichardie, ...  *)

Require Export JVM_Program.
Require Export Numeric.
Require Export List.
Open Scope Z_scope.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module Type JVM_SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Declare Module JVM_Prog : JVM_PROGRAM. Import JVM_Prog.

 Declare Module Byte  : NUMERIC with Definition power := 7%nat.
 Declare Module Short : NUMERIC with Definition power := 15%nat.
 Declare Module Int   : NUMERIC with Definition power := 31%nat.

 (** conversion *)
 Parameter b2i : Byte.t -> Int.t.
 Parameter s2i : Short.t -> Int.t.
 Parameter i2b : Int.t -> Byte.t.
 Parameter i2s : Int.t -> Short.t.
 Parameter i2bool : Int.t -> Byte.t.

 Inductive JVM_num : Set :=
   | I : Int.t -> JVM_num
   | B : Byte.t -> JVM_num
   | Sh : Short.t -> JVM_num.
 
 (** Location is the domain of adresses in the heap *)
 Parameter JVM_Location : Set.
 Parameter JVM_Location_dec : forall loc1 loc2:JVM_Location,{loc1=loc2}+{~loc1=loc2}.

 Inductive JVM_value : Set :=
   | Num : JVM_num -> JVM_value
   | Ref: JVM_Location -> JVM_value
   | Null : JVM_value.

 Definition init_value (t:JVM_type) : JVM_value :=
    match t with
     | JVM_ReferenceType _ => Null
     | JVM_PrimitiveType _ => Num (I (Int.const 0))
    end.

 Definition init_field_value (f:JVM_Field) : JVM_value :=
   match JVM_FIELD.initValue f with
    | JVM_FIELD.Int z => Num (I (Int.const z))
    | JVM_FIELD.NULL => Null
    | JVM_FIELD.UNDEF => init_value (JVM_FIELDSIGNATURE.type (JVM_FIELD.signature f))
  end.
 
 (** Domain of local variables *)
 Module Type JVM_LOCALVAR.
   Parameter t : Type.
   Parameter get : t-> JVM_Var -> option JVM_value.
   Parameter update : t -> JVM_Var -> JVM_value -> t.
   Parameter get_update_new : forall l x v, get (update l x v) x = Some v.
   Parameter get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
 End JVM_LOCALVAR.
 Declare Module JVM_LocalVar : JVM_LOCALVAR.


 (* Domain of operand stacks *) 
 Module Type JVM_OPERANDSTACK.
   Definition t : Set := list JVM_value.
   Definition empty : t := nil.
   Definition push : JVM_value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option JVM_value := fun s n => nth_error s n.
 End JVM_OPERANDSTACK.
 Declare Module JVM_OperandStack : JVM_OPERANDSTACK.

 (** Transfert fonction between operand stack and local variables necessary for invoke instructions *)
 Parameter stack2localvar : JVM_OperandStack.t -> nat -> JVM_LocalVar.t.
 Parameter stack2locvar_prop1 :
   forall s n x, (n <= Var_toN x)%nat -> JVM_LocalVar.get (stack2localvar s n) x = None.
 Parameter stack2locvar_prop2 :
   forall s n x, (Var_toN x < n)%nat ->
     JVM_LocalVar.get (stack2localvar s n) x = JVM_OperandStack.get_nth s (n-(Var_toN x)-1)%nat.
 (** %%nat is a coq command for the notation system *)

 Module Type JVM_HEAP.
   Parameter t : Type.

   Inductive JVM_AdressingMode : Set :=
     | StaticField : JVM_FieldSignature -> JVM_AdressingMode
     | DynamicField : JVM_Location -> JVM_FieldSignature -> JVM_AdressingMode
     | ArrayElement : JVM_Location -> Z -> JVM_AdressingMode.

   Inductive JVM_LocationType : Type :=
     | LocationObject : JVM_ClassName -> JVM_LocationType  
     | LocationArray : Int.t -> JVM_type -> JVM_Method*JVM_PC -> JVM_LocationType.
   (** (LocationArray length element_type) *)

   Parameter get : t -> JVM_AdressingMode -> option JVM_value.
   Parameter update : t -> JVM_AdressingMode -> JVM_value -> t.
   Parameter typeof : t -> JVM_Location -> option JVM_LocationType.   
     (** typeof h loc = None -> no object, no array allocated at location loc *)
   Parameter new : t -> JVM_Program -> JVM_LocationType -> option (JVM_Location * t).
     (** program is required to compute the size of the allocated element, i.e. to know
        the Class associated with a ClassName  *)

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : JVM_AdressingMode -> Prop :=
     | CompatStatic : forall f,
         Compat h (StaticField f)
     | CompatObject : forall cn loc f,
         typeof h loc = Some (LocationObject cn) ->
         Compat h (DynamicField loc f)
     | CompatArray : forall length tp loc i a,
         0 <= i < Int.toZ length ->
         typeof h loc = Some (LocationArray length tp a) ->
         Compat h (ArrayElement loc i).

   Parameter get_update_same : forall h am v, Compat h am ->  get (update h am v) am = Some v.
   Parameter get_update_old : forall h am1 am2 v, am1<>am2 -> get (update h am1 v) am2 = get h am2.
   Parameter get_uncompat : forall h am, ~ Compat h am -> get h am = None.

   Parameter typeof_update_same : forall h loc am v,
     typeof (update h am v) loc = typeof h loc.

   Parameter new_fresh_location : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc:JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.

   Parameter new_typeof : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc:JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.

   Parameter new_typeof_old : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc loc':JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.

   Parameter new_defined_object_field : forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (fs:JVM_FieldSignature) (f:JVM_Field) (loc:JVM_Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DynamicField loc fs) = Some (init_field_value f).

   Parameter new_undefined_object_field : forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (fs:JVM_FieldSignature) (loc:JVM_Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DynamicField loc fs) = None.
 
  Parameter new_object_no_change : 
     forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:JVM_FieldSignature), am <> (DynamicField loc fs)) ->
     get h' am = get h am.

  Parameter new_valid_array_index : forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (i:Z) (loc:JVM_Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = Some (init_value tp).

  Parameter new_unvalid_array_index : forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (i:Z) (loc:JVM_Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     ~ 0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = None.

  Parameter new_array_no_change : 
     forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     (forall (i:Z), am <> (ArrayElement loc i)) ->
     get h' am = get h am.

(* These properties should be useless
   Parameter get_static_some : forall (h:t) (p:Program) (fs:FieldSignature),
     isStatic p fs ->
     exists v, get h (StaticField fs) = Some v.

   Parameter get_static_some : forall (h:t) (p:Program) (fs:FieldSignature),
     ~ isStatic p fs ->
     exists v, get h (StaticField fs) = None.
*)

 End JVM_HEAP.
 Declare Module JVM_Heap : JVM_HEAP.

  Inductive JVM_ReturnVal : Set :=
   | Normal : option JVM_value -> JVM_ReturnVal
   | Exception : JVM_Location -> JVM_ReturnVal.

 (** Domain of frames *)
 Module Type JVM_FRAME.
   Inductive t : Type := 
      make : JVM_Method -> JVM_PC -> JVM_OperandStack.t -> JVM_LocalVar.t -> t.
 End JVM_FRAME.
 Declare Module JVM_Frame : JVM_FRAME.

 (** Domain of call stacks *)
 Module Type JVM_CALLSTACK.
   Definition t : Type := list JVM_Frame.t.
 End JVM_CALLSTACK.
 Declare Module JVM_CallStack : JVM_CALLSTACK.
(* DEX
 Module Type EXCEPTION_FRAME.
   Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
 End EXCEPTION_FRAME.
 Declare Module ExceptionFrame : EXCEPTION_FRAME.
*)
 (** Domain of states *)
 Module Type JVM_STATE.
   Inductive t : Type := 
      normal : JVM_Heap.t -> JVM_Frame.t -> JVM_CallStack.t -> t
    (* DEX | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t*).
   Definition get_sf (s:t) : JVM_CallStack.t :=
     match s with
       normal _ _ sf => sf
     (* DEX | exception _ _ sf => sf *)
     end.
   Definition get_m (s:t) : JVM_Method :=
     match s with
       normal _ (JVM_Frame.make m _ _ _)_ => m
     (* DEX | exception _ (ExceptionFrame.make m _ _ _) _ => m *)
     end.
 End JVM_STATE.
 Declare Module JVM_State : JVM_STATE.
 
 (** Some notations *)
 Notation St := JVM_State.normal.
(* DEX Notation StE := State.exception. *)
 Notation Fr := JVM_Frame.make.
(* DEX Notation FrE := ExceptionFrame.make. *)

  (** compatibility between ArrayKind and type *) 
  Inductive compat_ArrayKind_type : JVM_ArrayKind -> JVM_type -> Prop :=
    | compat_ArrayKind_type_ref : forall rt,
        compat_ArrayKind_type JVM_Aarray (JVM_ReferenceType rt)
    | compat_ArrayKind_type_int : 
        compat_ArrayKind_type JVM_Iarray (JVM_PrimitiveType JVM_INT)
    | compat_ArrayKind_type_byte : 
        compat_ArrayKind_type JVM_Barray (JVM_PrimitiveType JVM_BYTE)
    | compat_ArrayKind_type_bool : 
        compat_ArrayKind_type JVM_Barray (JVM_PrimitiveType JVM_BOOLEAN)
    | compat_ArrayKind_type_short : 
        compat_ArrayKind_type JVM_Sarray (JVM_PrimitiveType JVM_SHORT).

  Inductive isReference : JVM_value -> Prop :=
  | isReference_null : isReference Null
  | isReference_ref : forall loc, isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : JVM_ValKind -> JVM_value -> Prop :=
    | compat_ValKind_value_ref : forall v,
        isReference v -> compat_ValKind_value JVM_Aval v
    | compat_ValKind_value_int : forall n,
        compat_ValKind_value JVM_Ival (Num (I n)).

  (** compatibility between ArrayKind and value *) 
  Inductive compat_ArrayKind_value : JVM_ArrayKind -> JVM_value -> Prop :=
    | compat_ArrayKind_value_ref : forall v,
        isReference v -> compat_ArrayKind_value JVM_Aarray v
    | compat_ArrayKind_value_int : forall n,
        compat_ArrayKind_value JVM_Iarray (Num (I n))
    | compat_ArrayKind_value_byte : forall n,
        compat_ArrayKind_value JVM_Barray (Num (B n))
    | compat_ArrayKind_value_short : forall n,
        compat_ArrayKind_value JVM_Sarray (Num (Sh n)).

  (* convert a value to be pushed on the stack *)
  Definition conv_for_stack (v:JVM_value) : JVM_value :=
    match v with
    | Num (B b) => Num (I (b2i b))
    | Num (Sh s) => Num (I (s2i s))
    | _ => v
    end.

  (* convert a value to be store in an array *)
  Definition conv_for_array (v:JVM_value) (t:JVM_type) : JVM_value :=
    match v with
    | Ref loc => v
    | Num (I i) =>
       match t with
         JVM_ReferenceType _ => v (* impossible case *)
       | JVM_PrimitiveType JVM_INT => v
       | JVM_PrimitiveType JVM_BOOLEAN => Num (B (i2bool i))
       | JVM_PrimitiveType JVM_BYTE => Num (B (i2b i))
       | JVM_PrimitiveType JVM_SHORT => Num (Sh (i2s i))         
       end
    | _ => v (* impossible case *)
    end.

  (** [assign_compatible_num source target] holds if a numeric value [source] can be 
    assigned to a variable of type [target]. This point is not clear in the JVM spec. *)
  Inductive assign_compatible_num : JVM_num -> JVM_primitiveType -> Prop :=
   | assign_compatible_int_int : forall i, assign_compatible_num (I i) JVM_INT
   | assign_compatible_short_int : forall sh, assign_compatible_num (Sh sh) JVM_INT
   | assign_compatible_byte_int : forall b, assign_compatible_num (B b) JVM_INT
   | assign_compatible_short_short : forall sh, assign_compatible_num (Sh sh) JVM_SHORT
   | assign_compatible_byte_byte : forall b, assign_compatible_num (B b) JVM_BYTE
   | assign_compatible_byte_boolean : forall b, assign_compatible_num (B b) JVM_BOOLEAN.

  (** [assign_compatible h source target] holds if a value [source] can be 
    assigned to a variable of type [target] *)
  Inductive assign_compatible (p:JVM_Program) (h:JVM_Heap.t) : JVM_value -> JVM_type -> Prop :=
   | assign_compatible_null : forall t, assign_compatible p h Null (JVM_ReferenceType t)
   | assign_compatible_ref_object_val : forall (loc:JVM_Location) (t:JVM_refType) (cn:JVM_ClassName), 
       JVM_Heap.typeof h loc = Some (JVM_Heap.LocationObject cn) ->
       compat_refType p (JVM_ClassType cn) t ->
       assign_compatible p h (Ref loc) (JVM_ReferenceType t)
   | assign_compatible_ref_array_val : forall (loc:JVM_Location) (t:JVM_refType) (length:Int.t) (tp:JVM_type) a, 
       JVM_Heap.typeof h loc = Some (JVM_Heap.LocationArray length tp a) ->
       compat_refType p (JVM_ArrayType tp) t ->
       assign_compatible p h (Ref loc) (JVM_ReferenceType t)
   | assign_compatible_num_val : forall (n:JVM_num) (t:JVM_primitiveType),
       assign_compatible_num n t -> assign_compatible p h (Num n) (JVM_PrimitiveType t).

  Inductive SemCompRef : JVM_CompRef -> JVM_value -> JVM_value -> Prop :=
  | SemCompRef_eq : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 = v2 ->
     (****************************************************)
          SemCompRef JVM_EqRef v1 v2
  | SemCompRef_ne : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 <> v2 ->
     (****************************************************)
          SemCompRef JVM_NeRef v1 v2.

  Definition SemCompInt (cmp:JVM_CompInt) (z1 z2: Z) : Prop :=
    match cmp with
      JVM_EqInt =>  z1=z2
    | JVM_NeInt => z1<>z2
    | JVM_LtInt => z1<z2
    | JVM_LeInt => z1<=z2
    | JVM_GtInt => z1>z2
    | JVM_GeInt => z1>=z2
    end.

  Definition SemBinopInt (op:JVM_BinopInt) (i1 i2:Int.t) : Int.t :=
    match op with 
    | JVM_AddInt => Int.add i1 i2
    | JVM_AndInt => Int.and i1 i2
    | JVM_DivInt => Int.div i1 i2
    | JVM_MulInt => Int.mul i1 i2
    | JVM_OrInt => Int.or i1 i2
    | JVM_RemInt => Int.rem i1 i2
    | JVM_ShlInt => Int.shl i1 i2
    | JVM_ShrInt => Int.shr i1 i2
    | JVM_SubInt => Int.sub i1 i2
    | JVM_UshrInt => Int.ushr i1 i2
    | JVM_XorInt => Int.xor i1 i2
    end.

  (** Lookup in the callstack if one frame catches the thrown exception *)
  (* If an handler can catch the exception then the control flow is transferred 
     to the beginning of the handler and the exception caught is the only element 
     of the operand stack *)
  (* If lookup in the topmost frame fails, the frame is popped and the lookup 
     continues in the next frame *)
  (* FIXME: Check that the object pointed by loc is an instance of Throwable? - gd *)

(* DEX
  Inductive CaughtException (p:JVM_Program) : JVM_Method -> JVM_PC*JVM_Heap.t*JVM_Location -> JVM_PC -> Prop :=
    CaughtException_def : forall m pc h loc bm pc' e,
      METHOD.body m = Some bm ->
      Heap.typeof h loc = Some (Heap.LocationObject e) ->
      lookup_handlers p (BYTECODEMETHOD.exceptionHandlers bm) pc e pc' ->
      CaughtException p m (pc,h,loc) pc'.

  Inductive UnCaughtException (p:Program) : Method -> PC*Heap.t*Location -> Prop :=
    UnCaughtException_def : forall m pc h loc bm e,
      METHOD.body m = Some bm ->
      Heap.typeof h loc = Some (Heap.LocationObject e) ->
      (forall pc', ~ lookup_handlers p (BYTECODEMETHOD.exceptionHandlers bm) pc e pc') ->
      UnCaughtException p m (pc,h,loc).
*)

End JVM_SEMANTIC_DOMAIN.