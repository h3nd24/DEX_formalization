(** * Bicolano: Semantic domains *)

(* <Insert License Here>

    $Id: Domain.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

(** Formalization of Java semantic domain.
 Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
  Tim Lindholm, Frank Yellin"

 @author David Pichardie, ...  *)
(* Hendra : - Modified to suit DEX program (removed operand stack).
            - Removed reference comparison 
            - Also trim the system to contain only Arithmetic *)

Require Export DEX_Program.
Require Export Numeric.
Require Export List.
Open Scope Z_scope.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module Type DEX_SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Declare Module DEX_Prog : DEX_PROGRAM. Import DEX_Prog.

 Declare Module Byte  : NUMERIC with Definition power := 7%nat.
 Declare Module Short : NUMERIC with Definition power := 15%nat.
 Declare Module Int   : NUMERIC with Definition power := 31%nat.

 (** conversion *)
 Parameter b2i : Byte.t -> Int.t.
 Parameter s2i : Short.t -> Int.t. 
 Parameter i2b : Int.t -> Byte.t. 
 Parameter i2s : Int.t -> Short.t.
 Parameter i2bool : Int.t -> Byte.t.

 Inductive DEX_num : Set :=
   | I : Int.t -> DEX_num
   | B : Byte.t -> DEX_num
   | Sh : Short.t -> DEX_num.

 (** Location is the domain of adresses in the heap *)
 Parameter DEX_Location : Set.
 Parameter DEX_Location_dec : forall loc1 loc2:DEX_Location,{loc1=loc2}+{~loc1=loc2}.

 Inductive DEX_value : Set :=
   | Num : DEX_num -> DEX_value
   | Ref: DEX_Location -> DEX_value
   | Null : DEX_value.

 Definition init_value (t:DEX_type) : DEX_value :=
    match t with
     | DEX_PrimitiveType _ => Num (I (Int.const 0))
     | DEX_ReferenceType _ => Null
    end.

 Definition init_field_value (f:DEX_Field) : DEX_value :=
   match DEX_FIELD.initValue f with
    | DEX_FIELD.Int z => Num (I (Int.const z))
    | DEX_FIELD.NULL => Null
    | DEX_FIELD.UNDEF => init_value (DEX_FIELDSIGNATURE.type (DEX_FIELD.signature f))
  end.
 
 (** Domain of local variables *)
 Module Type DEX_REGISTERS.
   Parameter t : Type.
   Parameter get : t-> DEX_Reg -> option DEX_value.
   Parameter update : t -> DEX_Reg -> DEX_value -> t.
   Parameter dom : t -> list DEX_Reg.
   Parameter get_update_new : forall l x v, get (update l x v) x = Some v.
   Parameter get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
 End DEX_REGISTERS.
 Declare Module DEX_Registers : DEX_REGISTERS.

 Parameter listreg2regs : DEX_Registers.t -> nat -> list DEX_Reg -> DEX_Registers.t.

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

 Module Type DEX_HEAP.
   Parameter t : Type.

   Inductive DEX_AdressingMode : Set :=
     (*| StaticField : FieldSignature -> AdressingMode*)
     | DEX_DynamicField : DEX_Location -> DEX_FieldSignature -> DEX_AdressingMode
     (*| ArrayElement : Location -> Z -> AdressingMode*).

   Inductive DEX_LocationType : Type :=
     | DEX_LocationObject : DEX_ClassName -> DEX_LocationType  
     (*| LocationArray : Int.t -> type -> Method*PC -> LocationType*).
   (** (LocationArray length element_type) *)

   Parameter get : t -> DEX_AdressingMode -> option DEX_value.
   Parameter update : t -> DEX_AdressingMode -> DEX_value -> t.
   Parameter typeof : t -> DEX_Location -> option DEX_LocationType.   
     (** typeof h loc = None -> no object, no array allocated at location loc *)
   Parameter new : t -> DEX_Program -> DEX_LocationType -> option (DEX_Location * t).
     (** program is required to compute the size of the allocated element, i.e. to know
        the Class associated with a ClassName  *)

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : DEX_AdressingMode -> Prop :=
     (*| CompatStatic : forall f,
         Compat h (StaticField f)*)
     | CompatObject : forall cn loc f,
         typeof h loc = Some (DEX_LocationObject cn) ->
         Compat h (DEX_DynamicField loc f)
   (*  | CompatArray : forall length tp loc i a,
         0 <= i < Int.toZ length ->
         typeof h loc = Some (LocationArray length tp a) ->
         Compat h (ArrayElement loc i)*).

   Parameter get_update_same : forall h am v, Compat h am ->  get (update h am v) am = Some v.
   Parameter get_update_old : forall h am1 am2 v, am1<>am2 -> get (update h am1 v) am2 = get h am2.
   Parameter get_uncompat : forall h am, ~ Compat h am -> get h am = None.

   Parameter typeof_update_same : forall h loc am v,
     typeof (update h am v) loc = typeof h loc.

   Parameter new_fresh_location : forall (h:t) (p:DEX_Program) 
      (lt:DEX_LocationType) (loc:DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.

   Parameter new_typeof : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) (loc:DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.

   Parameter new_typeof_old : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc loc':DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.

   Parameter new_defined_object_field : forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) 
      (fs:DEX_FieldSignature) (f:DEX_Field) (loc:DEX_Location) (h':t),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DEX_DynamicField loc fs) = Some (init_field_value f).

   Parameter new_undefined_object_field : forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) 
      (fs:DEX_FieldSignature) (loc:DEX_Location) (h':t),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DEX_DynamicField loc fs) = None.
 
  Parameter new_object_no_change : 
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     (forall (fs:DEX_FieldSignature), am <> (DEX_DynamicField loc fs)) ->
     get h' am = get h am.

(*  Parameter new_valid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
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
     get h' am = get h am.*)
 End DEX_HEAP.
 Declare Module DEX_Heap : DEX_HEAP.

  Inductive DEX_ReturnVal : Set :=
   | Normal : option DEX_value -> DEX_ReturnVal.

 (** Domain of frames *)
 Module Type DEX_FRAME.
   Inductive t : Type := 
      make : DEX_Method -> DEX_PC -> DEX_Registers.t -> t.
 End DEX_FRAME.
 Declare Module DEX_Frame : DEX_FRAME.

 (** Domain of call stacks *)
 Module Type DEX_CALLSTACK.
   Definition t : Type := list DEX_Frame.t.
 End DEX_CALLSTACK.
 Declare Module DEX_CallStack : DEX_CALLSTACK.

 (** Domain of states *)
 Module Type DEX_STATE.
   Inductive t : Type := 
      normal : DEX_Heap.t -> DEX_Frame.t -> DEX_CallStack.t -> t.
   Definition get_sf (s:t) : DEX_CallStack.t :=
     match s with
       normal _ _ sf => sf
     end.
   Definition get_m (s:t) : DEX_Method :=
     match s with
       normal _ (DEX_Frame.make m _ _)_ => m
     end.
 End DEX_STATE.
 Declare Module DEX_State : DEX_STATE.
 
 (** Some notations *)
 Notation St := DEX_State.normal.
 Notation Fr := DEX_Frame.make.

  Inductive isReference : DEX_value -> Prop :=
  | isReference_null : isReference Null
  | isReference_ref : forall loc, isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : DEX_ValKind -> DEX_value -> Prop :=
    | compat_ValKind_value_ref : forall v,
        isReference v -> compat_ValKind_value DEX_Aval v
    | compat_ValKind_value_int : forall n,
        compat_ValKind_value DEX_Ival (Num (I n)).

  (** [assign_compatible_num source target] holds if a numeric value [source] can be 
    assigned to a variable of type [target]. This point is not clear in the JVM spec. *)
  Inductive assign_compatible_num : DEX_num -> DEX_primitiveType -> Prop :=
   | assign_compatible_int_int : forall i, assign_compatible_num (I i) DEX_INT
   | assign_compatible_short_int : forall sh, assign_compatible_num (Sh sh) DEX_INT
   | assign_compatible_byte_int : forall b, assign_compatible_num (B b) DEX_INT
   | assign_compatible_short_short : forall sh, assign_compatible_num (Sh sh) DEX_SHORT
   | assign_compatible_byte_byte : forall b, assign_compatible_num (B b) DEX_BYTE
   | assign_compatible_byte_boolean : forall b, assign_compatible_num (B b) DEX_BOOLEAN.

  (** [assign_compatible h source target] holds if a value [source] can be 
    assigned to a variable of type [target] *)
  Inductive assign_compatible (p:DEX_Program) (h:DEX_Heap.t) : DEX_value -> DEX_type -> Prop :=
   | assign_compatible_null : forall t, assign_compatible p h Null (DEX_ReferenceType t)
   | assign_compatible_ref_object_val : forall (loc:DEX_Location) (t:DEX_refType) (cn:DEX_ClassName), 
       DEX_Heap.typeof h loc = Some (DEX_Heap.DEX_LocationObject cn) ->
       compat_refType p (DEX_ClassType cn) t ->
       assign_compatible p h (Ref loc) (DEX_ReferenceType t)
   | assign_compatible_num_val : forall (n:DEX_num) (t:DEX_primitiveType),
       assign_compatible_num n t -> assign_compatible p h (Num n) (DEX_PrimitiveType t).

  Definition SemCompInt (cmp:DEX_CompInt) (z1 z2: Z) : Prop :=
    match cmp with
      DEX_EqInt =>  z1=z2
    | DEX_NeInt => z1<>z2
    | DEX_LtInt => z1<z2
    | DEX_LeInt => z1<=z2
    | DEX_GtInt => z1>z2
    | DEX_GeInt => z1>=z2
    end.

  Definition SemBinopInt (op:DEX_BinopInt) (i1 i2:Int.t) : Int.t :=
    match op with 
    | DEX_AddInt => Int.add i1 i2
    | DEX_AndInt => Int.and i1 i2
    | DEX_DivInt => Int.div i1 i2
    | DEX_MulInt => Int.mul i1 i2
    | DEX_OrInt => Int.or i1 i2
    | DEX_RemInt => Int.rem i1 i2
    | DEX_ShlInt => Int.shl i1 i2
    | DEX_ShrInt => Int.shr i1 i2
    | DEX_SubInt => Int.sub i1 i2
    | DEX_UshrInt => Int.ushr i1 i2
    | DEX_XorInt => Int.xor i1 i2
    end.

End DEX_SEMANTIC_DOMAIN.