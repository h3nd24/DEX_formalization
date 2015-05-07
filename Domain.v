(** * Bicolano: Semantic domains *)

(* <Insert License Here>

    $Id: Domain.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

(** Formalization of Java semantic domain.
 Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
  Tim Lindholm, Frank Yellin"

 @author David Pichardie, ...  *)

Require Export Program.
Require Export Numeric.
Require Export List.
Open Scope Z_scope.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module Type SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Declare Module Prog : PROGRAM. Import Prog.

 Declare Module Byte  : NUMERIC with Definition power := 7%nat.
 Declare Module Short : NUMERIC with Definition power := 15%nat.
 Declare Module Int   : NUMERIC with Definition power := 31%nat.

 (** conversion *)
 Parameter b2i : Byte.t -> Int.t.
 Parameter s2i : Short.t -> Int.t. 
 Parameter i2b : Int.t -> Byte.t. 
 Parameter i2s : Int.t -> Short.t.
 Parameter i2bool : Int.t -> Byte.t.

 Inductive num : Set :=
   | I : Int.t -> num
   | B : Byte.t -> num
   | Sh : Short.t -> num.
 
 (** Location is the domain of adresses in the heap *)
 Parameter Location : Set.
 Parameter Location_dec : forall loc1 loc2:Location,{loc1=loc2}+{~loc1=loc2}.

 Inductive value : Set :=
   | Num : num -> value
   | Ref: Location -> value
   | Null : value.

 Definition init_value (t:type) : value :=
    match t with
     | ReferenceType _ => Null
     | PrimitiveType _ => Num (I (Int.const 0))
    end.

 Definition init_field_value (f:Field) : value :=
   match FIELD.initValue f with
    | FIELD.Int z => Num (I (Int.const z))
    | FIELD.NULL => Null
    | FIELD.UNDEF => init_value (FIELDSIGNATURE.type (FIELD.signature f))
  end.
 
 (** Domain of local variables *)
 Module Type LOCALVAR.
   Parameter t : Type.
   Parameter get : t-> Var -> option value.
   Parameter update : t -> Var -> value -> t.
   Parameter ret : Var.
   Parameter ex : Var.
   Parameter get_update_new : forall l x v, get (update l x v) x = Some v.
   Parameter get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
 End LOCALVAR.
 Declare Module LocalVar : LOCALVAR.

 Parameter listvar2localvar : LocalVar.t -> nat -> list Var -> LocalVar.t.

(* 290415 - Some Notes
- According to verified DEX bytecode, every registers have
  to have a value before used. This means we can safely assume
  that we don't need the update to be option anymore because
  the only possible case where it updates empty value is when
  the source is empty, which has been taken care by the assumption
- The special register ret and ex are assigned the number
  65536 and 65537 respectively (in binary) because we know
  that the maximum number of registers is 65535.
*)

(*
 (* Domain of operand stacks *) 
 Module Type OPERANDSTACK.
   Definition t : Set := list value.
   Definition empty : t := nil.
   Definition push : value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option value := fun s n => nth_error s n.
 End OPERANDSTACK.
 Declare Module OperandStack : OPERANDSTACK.

 (** Transfert fonction between operand stack and local variables necessary for invoke instructions *)
 Parameter stack2localvar : OperandStack.t -> nat -> LocalVar.t.
 Parameter stack2locvar_prop1 :
   forall s n x, (n <= Var_toN x)%nat -> LocalVar.get (stack2localvar s n) x = None.
 Parameter stack2locvar_prop2 :
   forall s n x, (Var_toN x < n)%nat ->
     LocalVar.get (stack2localvar s n) x = OperandStack.get_nth s (n-(Var_toN x)-1)%nat.
 (** %%nat is a coq command for the notation system *)
*)
 Module Type HEAP.
   Parameter t : Type.

   Inductive AdressingMode : Set :=
     | StaticField : FieldSignature -> AdressingMode
     | DynamicField : Location -> FieldSignature -> AdressingMode
     | ArrayElement : Location -> Z -> AdressingMode.

   Inductive LocationType : Type :=
     | LocationObject : ClassName -> LocationType  
     | LocationArray : Int.t -> type -> Method*PC -> LocationType.
   (** (LocationArray length element_type) *)

   Parameter get : t -> AdressingMode -> option value.
   Parameter update : t -> AdressingMode -> value -> t.
   Parameter typeof : t -> Location -> option LocationType.   
     (** typeof h loc = None -> no object, no array allocated at location loc *)
   Parameter new : t -> Program -> LocationType -> option (Location * t).
     (** program is required to compute the size of the allocated element, i.e. to know
        the Class associated with a ClassName  *)

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : AdressingMode -> Prop :=
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

   Parameter new_fresh_location : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.

   Parameter new_typeof : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.

   Parameter new_typeof_old : forall (h:t) (p:Program) (lt:LocationType) (loc loc':Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.

   Parameter new_defined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (f:Field) (loc:Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DynamicField loc fs) = Some (init_field_value f).

   Parameter new_undefined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (loc:Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DynamicField loc fs) = None.
 
  Parameter new_object_no_change : 
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:FieldSignature), am <> (DynamicField loc fs)) ->
     get h' am = get h am.

  Parameter new_valid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = Some (init_value tp).

  Parameter new_unvalid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     ~ 0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = None.

  Parameter new_array_no_change : 
     forall (h:t) (p:Program) (length:Int.t) (tp:type) a (loc:Location) (h':t) (am:AdressingMode),
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

 End HEAP.
 Declare Module Heap : HEAP.

  Inductive ReturnVal : Set :=
   | Normal : option value -> ReturnVal
   | Exception : Location -> ReturnVal.

 (** Domain of frames *)
 Module Type FRAME.
   Inductive t : Type := 
      (*make : Method -> PC -> OperandStack.t -> LocalVar.t -> t.*)
      make : Method -> PC -> LocalVar.t -> t.
 End FRAME.
 Declare Module Frame : FRAME.

 (** Domain of call stacks *)
 Module Type CALLSTACK.
   Definition t : Type := list Frame.t.
 End CALLSTACK.
 Declare Module CallStack : CALLSTACK.

 Module Type EXCEPTION_FRAME.
   Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
 End EXCEPTION_FRAME.
 Declare Module ExceptionFrame : EXCEPTION_FRAME.

 (** Domain of states *)
 Module Type STATE.
   Inductive t : Type := 
      normal : Heap.t -> Frame.t -> CallStack.t -> t
    | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t.
   Definition get_sf (s:t) : CallStack.t :=
     match s with
       normal _ _ sf => sf
     | exception _ _ sf => sf
     end.
   Definition get_m (s:t) : Method :=
     match s with
       normal _ (Frame.make m _ _)_ => m
     | exception _ (ExceptionFrame.make m _ _ _) _ => m
     end.
 End STATE.
 Declare Module State : STATE.
 
 (** Some notations *)
 Notation St := State.normal.
 Notation StE := State.exception.
 Notation Fr := Frame.make.
 Notation FrE := ExceptionFrame.make.

  (** compatibility between ArrayKind and type *) 
  Inductive compat_ArrayKind_type : ArrayKind -> type -> Prop :=
    | compat_ArrayKind_type_ref : forall rt,
        compat_ArrayKind_type Aarray (ReferenceType rt)
    | compat_ArrayKind_type_int : 
        compat_ArrayKind_type Iarray (PrimitiveType INT)
    | compat_ArrayKind_type_byte : 
        compat_ArrayKind_type Barray (PrimitiveType BYTE)
    | compat_ArrayKind_type_bool : 
        compat_ArrayKind_type Barray (PrimitiveType BOOLEAN)
    | compat_ArrayKind_type_short : 
        compat_ArrayKind_type Sarray (PrimitiveType SHORT).

  Inductive isReference : value -> Prop :=
  | isReference_null : isReference Null
  | isReference_ref : forall loc, isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : ValKind -> value -> Prop :=
    | compat_ValKind_value_ref : forall v,
        isReference v -> compat_ValKind_value Aval v
    | compat_ValKind_value_int : forall n,
        compat_ValKind_value Ival (Num (I n)).

  (** compatibility between ArrayKind and value *) 
  Inductive compat_ArrayKind_value : ArrayKind -> value -> Prop :=
    | compat_ArrayKind_value_ref : forall v,
        isReference v -> compat_ArrayKind_value Aarray v
    | compat_ArrayKind_value_int : forall n,
        compat_ArrayKind_value Iarray (Num (I n))
    | compat_ArrayKind_value_byte : forall n,
        compat_ArrayKind_value Barray (Num (B n))
    | compat_ArrayKind_value_short : forall n,
        compat_ArrayKind_value Sarray (Num (Sh n)).

  (* convert a value to be pushed on the stack *)
  Definition conv_for_stack (v:value) : value :=
    match v with
    | Num (B b) => Num (I (b2i b))
    | Num (Sh s) => Num (I (s2i s))
    | _ => v
    end.

  (* convert a value to be store in an array *)
  Definition conv_for_array (v:value) (t:type) : value :=
    match v with
    | Ref loc => v
    | Num (I i) =>
       match t with
         ReferenceType _ => v (* impossible case *)
       | PrimitiveType INT => v
       | PrimitiveType BOOLEAN => Num (B (i2bool i))
       | PrimitiveType BYTE => Num (B (i2b i))
       | PrimitiveType SHORT => Num (Sh (i2s i))         
       end
    | _ => v (* impossible case *)
    end.

  (** [assign_compatible_num source target] holds if a numeric value [source] can be 
    assigned to a variable of type [target]. This point is not clear in the JVM spec. *)
  Inductive assign_compatible_num : num -> primitiveType -> Prop :=
   | assign_compatible_int_int : forall i, assign_compatible_num (I i) INT
   | assign_compatible_short_int : forall sh, assign_compatible_num (Sh sh) INT
   | assign_compatible_byte_int : forall b, assign_compatible_num (B b) INT
   | assign_compatible_short_short : forall sh, assign_compatible_num (Sh sh) SHORT
   | assign_compatible_byte_byte : forall b, assign_compatible_num (B b) BYTE
   | assign_compatible_byte_boolean : forall b, assign_compatible_num (B b) BOOLEAN.

  (** [assign_compatible h source target] holds if a value [source] can be 
    assigned to a variable of type [target] *)
  Inductive assign_compatible (p:Program) (h:Heap.t) : value -> type -> Prop :=
   | assign_compatible_null : forall t, assign_compatible p h Null (ReferenceType t)
   | assign_compatible_ref_object_val : forall (loc:Location) (t:refType) (cn:ClassName), 
       Heap.typeof h loc = Some (Heap.LocationObject cn) ->
       compat_refType p (ClassType cn) t ->
       assign_compatible p h (Ref loc) (ReferenceType t)
   | assign_compatible_ref_array_val : forall (loc:Location) (t:refType) (length:Int.t) (tp:type) a, 
       Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
       compat_refType p (ArrayType tp) t ->
       assign_compatible p h (Ref loc) (ReferenceType t)
   | assign_compatible_num_val : forall (n:num) (t:primitiveType),
       assign_compatible_num n t -> assign_compatible p h (Num n) (PrimitiveType t).

  Inductive SemCompRef : CompRef -> value -> value -> Prop :=
  | SemCompRef_eq : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 = v2 ->
     (****************************************************)
          SemCompRef EqRef v1 v2
  | SemCompRef_ne : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 <> v2 ->
     (****************************************************)
          SemCompRef NeRef v1 v2.

  Definition SemCompInt (cmp:CompInt) (z1 z2: Z) : Prop :=
    match cmp with
      EqInt =>  z1=z2
    | NeInt => z1<>z2
    | LtInt => z1<z2
    | LeInt => z1<=z2
    | GtInt => z1>z2
    | GeInt => z1>=z2
    end.

  Definition SemBinopInt (op:BinopInt) (i1 i2:Int.t) : Int.t :=
    match op with 
    | AddInt => Int.add i1 i2
    | AndInt => Int.and i1 i2
    | DivInt => Int.div i1 i2
    | MulInt => Int.mul i1 i2
    | OrInt => Int.or i1 i2
    | RemInt => Int.rem i1 i2
    | ShlInt => Int.shl i1 i2
    | ShrInt => Int.shr i1 i2
    | SubInt => Int.sub i1 i2
    | UshrInt => Int.ushr i1 i2
    | XorInt => Int.xor i1 i2
    end.

  (** Lookup in the callstack if one frame catches the thrown exception *)
  (* If an handler can catch the exception then the control flow is transferred 
     to the beginning of the handler and the exception caught is the only element 
     of the operand stack *)
  (* If lookup in the topmost frame fails, the frame is popped and the lookup 
     continues in the next frame *)
  (* FIXME: Check that the object pointed by loc is an instance of Throwable? - gd *)

(*  Inductive CaughtException (p:Program) : Method -> PC*Heap.t*Location -> PC -> Prop :=
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
      UnCaughtException p m (pc,h,loc). *)


End SEMANTIC_DOMAIN.
