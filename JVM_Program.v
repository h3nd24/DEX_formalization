(** * Bicolano: Program syntax (interface only) *)

(* <Insert License Here>

    $Id: Program.v 81 2006-03-30 22:27:58Z davidpichardie $ *)

(** Formalization of Java programs.
 Based on the report secsafe-tl-005:
 @see http://www.doc.ic.ac.uk/~siveroni/secsafe/docs/secsafe-tl-005.pdf
 Simplifications have been made with the objective that a straightforward
 classfile parser would implement this API.

 @author Frederic Besson and David Pichardie *)


Require Import List.
Require Import ZArith.
Require Import Relation_Operators.

(*Require Export MapSignatures.*)
Open Local Scope type_scope.

(* Where Lists are used, sometimes Sets would be more adequate.
  However, this would complicate the specification.
*)

Definition distinct (A B:Type) (f:A->B) (l:list A) : Prop :=
  forall x y, In x l -> In y l -> f x = f y -> x = y.
Implicit Arguments distinct.

(** Main module for representing a Java program *)

Module Type JVM_PROGRAM.

  (** Main types to be manipulated by the API *)
  Parameter JVM_Program :Type.
  Parameter JVM_Class : Type.
  Parameter JVM_Interface : Type.
  Parameter JVM_Var : Set.
  Parameter JVM_Field : Set.
  Parameter JVM_Method : Type.
  Parameter JVM_BytecodeMethod : Type.
(* DEX Parameter JVM_ExceptionHandler : Set. *)
  Parameter JVM_ShortMethodSignature : Set.
  Parameter JVM_ShortFieldSignature :Set.
  Parameter JVM_PC : Set.

 (** Variables are indexed by integers *)
  Parameter Var_toN : JVM_Var -> nat.
  Parameter N_toVar : nat -> JVM_Var.
  Parameter Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Parameter Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.


  (** Handling of qualified names *)
  Parameter JVM_PackageName : Set.
  Parameter JVM_ShortClassName : Set.
  Parameter JVM_ShortMethodName : Set.
  Parameter JVM_ShortFieldName : Set.

  (**For example the qualified name [java.lang.String] of the class [String],
      is decomposed into [java.lang] for the package name and [String] for the
       short name.  *)
  Definition JVM_ClassName := JVM_PackageName * JVM_ShortClassName.
  Definition JVM_InterfaceName := JVM_PackageName * JVM_ShortClassName.
  Definition JVM_MethodName := JVM_ClassName * JVM_ShortMethodName.
  Definition JVM_FieldName := JVM_ClassName * JVM_ShortFieldName.
  Definition JVM_MethodSignature := JVM_ClassName * JVM_ShortMethodSignature.
  Definition JVM_FieldSignature := JVM_ClassName * JVM_ShortFieldSignature.
  (** Some constants *)
  Parameter javaLang : JVM_PackageName.
  Parameter object : JVM_ShortClassName.

(* DEX - don't care about exception for now  
  Parameter throwable : ShortClassName.

  (** Native Exceptions *)
  Parameter NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName.
*)
  (** visibility modifiers *)
  Inductive JVM_Visibility : Set :=
    Package | Protected | Private | Public.

  Inductive JVM_type : Set :=
      | JVM_ReferenceType (rt : JVM_refType)
      | JVM_PrimitiveType (pt: JVM_primitiveType)
  with JVM_refType :Set := 
      | JVM_ArrayType (typ:JVM_type) 
      | JVM_ClassType  (ct:JVM_ClassName)
      | JVM_InterfaceType (it:JVM_InterfaceName)
  with  JVM_primitiveType : Set := 
      | JVM_BOOLEAN  | JVM_BYTE | JVM_SHORT | JVM_INT.
      (* + Int64, Float,Double *)
      (* + ReturnAddressType subroutines *)

 
  Inductive JVM_CompInt : Set := 
    JVM_EqInt | JVM_NeInt | JVM_LtInt | JVM_LeInt | JVM_GtInt | JVM_GeInt.
  Inductive JVM_CompRef : Set := JVM_EqRef | JVM_NeRef.

  Inductive JVM_BinopInt : Set := 
    JVM_AddInt | JVM_AndInt | JVM_DivInt | JVM_MulInt | JVM_OrInt | JVM_RemInt 
  | JVM_ShlInt | JVM_ShrInt | JVM_SubInt | JVM_UshrInt | JVM_XorInt.

  (* Type information used for Vaload and Saload *)
  Inductive JVM_ArrayKind : Set :=
    | JVM_Aarray
    | JVM_Iarray
    | JVM_Barray
    | JVM_Sarray.
    
  (* Type information used for Vload, Vstore and Vreturn *)
  Inductive JVM_ValKind : Set :=
    | JVM_Aval
    | JVM_Ival.


  Module Type JVM_OFFSET_TYPE.
    (* The type of address offsets *)
    Parameter t : Set.
     (** Jumps are defined in terms of offsets with respect to the current address. **)
    Parameter jump : JVM_PC -> t -> JVM_PC.
  End JVM_OFFSET_TYPE.
  Declare Module JVM_OFFSET : JVM_OFFSET_TYPE.

  (** Operations on the signatures of fields *)
  Module Type JVM_FIELDSIGNATURE_TYPE.
    Parameter name : JVM_ShortFieldSignature -> JVM_ShortFieldName.
    Parameter type : JVM_ShortFieldSignature -> JVM_type.
    Parameter eq_dec : forall f1 f2:JVM_ShortFieldSignature, f1=f2 \/ ~f1=f2.
  End JVM_FIELDSIGNATURE_TYPE.
  Declare Module JVM_FIELDSIGNATURE : JVM_FIELDSIGNATURE_TYPE.

  (** Content of a method signature *)
  Module Type JVM_METHODSIGNATURE_TYPE.
    (* The method name *)
    Parameter name : JVM_ShortMethodSignature -> JVM_ShortMethodName.
    (** Java types for parameters values *)
    Parameter parameters : JVM_ShortMethodSignature -> list JVM_type.
    (** Java type for return value, the constructor [None] of type option being used for the [Void] type *)
    Parameter result : JVM_ShortMethodSignature -> option JVM_type.

    Parameter eq_dec : 
      forall mid1 mid2:JVM_ShortMethodSignature, mid1=mid2 \/ ~mid1=mid2.
  End JVM_METHODSIGNATURE_TYPE.
  Declare Module JVM_METHODSIGNATURE : JVM_METHODSIGNATURE_TYPE.

    (** Parser translation :

  aaload                --> Vaload Aarray
  aastore               --> Vastore Aarray
  aconst_null           --> Aconst_null
  aload x               --> Vload Aval x
  aload_<n>             --> Vload Aval n
  anewarray t           --> Newarray (ReferenceType t)
  areturn               --> Vreturn Aarray
  arraylength           --> Arraylength
  astore x              --> Vstore Aval x
  astore_<n>            --> Vstore Aval n
  athrow                --> Athrow
  baload                --> Vaload Barray
  bastore               --> Vastore Barray
  bipush c              --> Const BYTE c
  caload                --> char not supported
  castore               --> char not supported
  checkcast t           --> Checkcast t
  d2f                   --> double not supported
  d2i                   --> double not supported
  d2l                   --> double not supported
  dadd                  --> double not supported
  daload                --> double not supported
  dastore               --> double not supported
  dcmp<op>              --> double not supported
  dconst_<d>            --> double not supported
  ddiv                  --> double not supported
  dload                 --> double not supported
  dload_<n>             --> double not supported
  dmul                  --> double not supported
  dneg                  --> double not supported
  drem                  --> double not supported
  dreturn               --> double not supported
  dstore                --> double not supported
  dstore_<n>            --> double not supported
  dsub                  --> double not supported
  dup                   --> Dup
  dup_x1                --> Dup_x1
  dup_x2                --> Dup_x2
  dup2                  --> Dup2
  dup2_x1               --> Dup2_x1
  dup2_x2               --> Dup2_x2
  f2d                   --> float not supported
  f2i                   --> float not supported
  f2l                   --> float not supported
  fadd                  --> float not supported
  faload                --> float not supported
  fastore               --> float not supported
  fcmp<op>              --> float not supported
  fconst_<f>            --> float not supported
  fdiv                  --> float not supported
  fload                 --> float not supported
  fload_<n>             --> float not supported
  fmul                  --> float not supported
  fneg                  --> float not supported
  frem                  --> float not supported
  freturn               --> float not supported
  fstore                --> float not supported
  fstore_<n>            --> float not supported
  fsub                  --> float not supported
  getfield f            --> Getfield f
  getstatic f           --> Getstatic f
  goto o                --> Goto o    
  goto_w o              --> Goto o
  i2b                   --> I2b
  i2c                   --> char not supported
  i2d                   --> double not supported
  i2f                   --> float not supported
  i2l                   --> long not supported
  i2s                   --> I2s
  iadd                  --> Ibinop AddInt
  iaload                --> Vaload Iarray
  iand                  --> Ibinop AndInt
  iastore               --> Vastore Iarray
  iconst_<i>            --> Const i
  idiv                  --> Ibinop DivInt
  if_acmp<cond> o       --> If_acmp cond o
  if_icmp<cond> o       --> If_icmp cond o
  if<cond> o            --> If0 cond o
  ifnonnull o           --> Ifnull NeRef o
  ifnull o              --> Ifnull EqRef o
  iinc x c              --> Iinc x c
  iload x      	        --> Vload Ival x
  iload_<n>    	        --> Vload Ival n
  imul         	        --> Ibinop MulInt
  ineg         	        --> Ineg
  instanceof t          --> Instanceof t
  invokeinterface m     --> Invokeinterface m
  invokespecial m       --> Invokespecial m
  invokestatic m        --> Invokestatic m
  invokevirtual m       --> Invokevirtual m
  ior                   --> Ibinop OrInt
  irem                  --> Ibinop RemInt
  ireturn               --> Vreturn Ival
  ishl                  --> Ibinop ShlInt
  ishr                  --> Ibinop ShrInt
  istore x     	        --> Vstore Ival x
  istore_<n>   	        --> Vstore Ival n
  isub                  --> Ibinop SubInt
  iushr                 --> Ibinop UshrInt
  ixor                  --> Ibinop XorInt
  jsr                   --> subroutines not supported
  jsr_w                 --> subroutines not supported
  l2d                   --> long not supported
  l2f                   --> long not supported
  l2i                   --> long not supported
  ladd                  --> long not supported
  laload                --> long not supported
  land                  --> long not supported
  lastore               --> long not supported
  lcmp                  --> long not supported
  lconst_<l>            --> long not supported
  ldc c                 --> Const c (but strings not supported)
  ldc_w c               --> Const c (but strings not supported)
  ldc2_w c              --> long and double not supported
  ldiv                  --> long not supported
  lload                 --> long not supported
  lload_<n>             --> long not supported
  lmul                  --> long not supported
  lneg                  --> long not supported
  lookupswitch d l      --> Lookupswitch d l
  lor                   --> long not supported
  lrem                  --> long not supported
  lreturn               --> long not supported
  lshl                  --> long not supported
  lshr                  --> long not supported
  lstore                --> long not supported
  lstore_<n>            --> long not supported
  lsub                  --> long not supported
  lushr                 --> long not supported
  lxor                  --> long not supported
  monitorenter          --> multithreading not supported
  monitorexit           --> multithreading not supported
  multianewarray        --> not supported
  new c                 --> New c
  newarray t            --> Newarray (PrimitiveType t)
  nop                   --> Nop
  pop                   --> Pop
  pop2                  --> Pop2
  putfield f            --> Putfield f
  putstatic f           --> Putstatic f
  ret                   --> subroutines not supported
  return                --> Return
  saload                --> Vaload Sarray
  sastore               --> Vastore Sarray
  sipush c              --> Const c
  swap                  --> Swap
  tableswitch d lo hi l --> Tableswitch d lo hi l
   *)

  Inductive JVM_Instruction : Set :=
(* DEX Objects
   | JVM_Aconst_null
   | JVM_Arraylength 
*)
(* DEX Exception  | Athrow
   | Checkcast (t:JVM_refType) *)
   | JVM_Const (t:JVM_primitiveType) (z:Z)
   | JVM_Dup
   | JVM_Dup_x1
   | JVM_Dup_x2
   | JVM_Dup2
   | JVM_Dup2_x1
   | JVM_Dup2_x2

(* DEX
  | JVM_Getfield (f:JVM_FieldSignature)
*)
   | JVM_Goto (o:JVM_OFFSET.t)
   | JVM_I2b
   | JVM_I2s
   | JVM_Ibinop (op:JVM_BinopInt)
(* DEX 
   | JVM_If_acmp (cmp:JVM_CompRef) (o:JVM_OFFSET.t)
*)
   | JVM_If_icmp (cmp:JVM_CompInt) (o:JVM_OFFSET.t) 
   | JVM_If0 (cmp:JVM_CompInt) (o:JVM_OFFSET.t)

(* DEX
   | JVM_Ifnull (cmp:JVM_CompRef) (o:JVM_OFFSET.t)
*)
   | JVM_Iinc (x:JVM_Var) (z:Z)
   | JVM_Ineg 
(* DEX
   | JVM_Instanceof (t:JVM_refType) 
   | JVM_Invokeinterface (m:JVM_MethodSignature)
   | JVM_Invokespecial (m:JVM_MethodSignature)
   | JVM_Invokestatic (m:JVM_MethodSignature)
   | JVM_Invokevirtual (m:JVM_MethodSignature)
*)
   | JVM_Lookupswitch (def:JVM_OFFSET.t) (l:list (Z*JVM_OFFSET.t)) 
(*   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) *)
(* DEX
   | JVM_New (c:JVM_ClassName)
   | JVM_Newarray (t:JVM_type)
*)
   | JVM_Nop
   | JVM_Pop
   | JVM_Pop2
(* DEX
   | JVM_Putfield (f:JVM_FieldSignature)
*)
   | JVM_Return
   | JVM_Swap 
   | JVM_Tableswitch (def:JVM_OFFSET.t) (low high:Z) (l:list JVM_OFFSET.t)
(* DEX
   | JVM_Vaload (k:JVM_ArrayKind) 
   | JVM_Vastore (k:JVM_ArrayKind)
*)
   | JVM_Vload (k:JVM_ValKind) (x:JVM_Var)
   | JVM_Vreturn (k:JVM_ValKind)
   | JVM_Vstore (k:JVM_ValKind) (x:JVM_Var).

(* DEX
  (** Operations on exception handlers *)
  Module Type EXCEPTIONHANDLER_TYPE.
  (** class of the caught exception *)
    (** The constructor [None] of type option being used to implement [finally]. It
    matches any exception *)
    Parameter catchType : ExceptionHandler -> option ClassName.
    (** is the given PC in range of the handler *)
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    (** location of the handler code *) 
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
  Declare Module EXCEPTIONHANDLER : EXCEPTIONHANDLER_TYPE.
*)

  (** Operations on bytecode methods *)
  Module Type JVM_BYTECODEMETHOD_TYPE.
    Parameter firstAddress : JVM_BytecodeMethod -> JVM_PC.
    Parameter nextAddress : JVM_BytecodeMethod -> JVM_PC -> option JVM_PC.
    Parameter instructionAt : JVM_BytecodeMethod -> JVM_PC -> option JVM_Instruction.
(* DEX
    (* The list of exception is supposed to be ordered from the innermost to
       the outermost handler, otherwise the behavior might be unexpected 
       @see JVMS 3.10 *)
    Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.
*)
    (** max number of local variables *)
    Parameter max_locals : JVM_BytecodeMethod -> nat.
    (** max number of elements on the operand stack *)
    Parameter max_operand_stack_size : JVM_BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:JVM_BytecodeMethod) (pc:JVM_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
   
  End JVM_BYTECODEMETHOD_TYPE.
  Declare Module JVM_BYTECODEMETHOD : JVM_BYTECODEMETHOD_TYPE.
 
  (** Content of a method *)
  Module Type JVM_METHOD_TYPE.

    Parameter signature : JVM_Method -> JVM_ShortMethodSignature.
    (** A method that is not abstract has an empty method body *)
    Parameter body : JVM_Method -> option JVM_BytecodeMethod.

    (* modifiers *)
    Parameter isFinal : JVM_Method -> bool.
    Parameter isStatic : JVM_Method -> bool.
    Parameter isNative : JVM_Method -> bool.
    Definition isAbstract (m : JVM_Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.

    Parameter visibility : JVM_Method -> JVM_Visibility.

    Definition valid_var (m:JVM_Method) (x:JVM_Var) : Prop :=
      forall bm, body m = Some bm ->
         (Var_toN x) <= (JVM_BYTECODEMETHOD.max_locals bm).

    Definition valid_stack_size (m:JVM_Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         length <= (JVM_BYTECODEMETHOD.max_operand_stack_size bm).

    End JVM_METHOD_TYPE.
  Declare Module JVM_METHOD : JVM_METHOD_TYPE.

  (** Operations on fields *)
  Module Type JVM_FIELD_TYPE.
    Parameter signature : JVM_Field -> JVM_ShortFieldSignature.    
    Parameter isFinal : JVM_Field -> bool.
    Parameter isStatic : JVM_Field -> bool.

    Parameter visibility : JVM_Field -> JVM_Visibility.

    Inductive value : Set :=
      | Int (v:Z) (* Numeric value *)
(*      | Lst (l:list Z)   Array of nums *)
      | NULL (* reference *)
      | UNDEF (* default value *).

    (** Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : JVM_Field ->  value.

  End JVM_FIELD_TYPE.
  Declare Module JVM_FIELD : JVM_FIELD_TYPE.

  (** Content of a Java class *)
  Module Type JVM_CLASS_TYPE.

    Parameter name : JVM_Class -> JVM_ClassName.
    (** direct superclass *)
    (** All the classes have a superClass except [java.lang.Object]. (see [Wf.v]) *)
    Parameter superClass : JVM_Class -> option JVM_ClassName.
    (** list of implemented interfaces *)
    Parameter superInterfaces : JVM_Class -> list JVM_InterfaceName.

    Parameter field : JVM_Class -> JVM_ShortFieldName -> option JVM_Field.

    Parameter definedFields : JVM_Class -> list JVM_Field.
    Parameter in_definedFields_field_some : forall c f,
      In f (definedFields c) ->
      field c (JVM_FIELDSIGNATURE.name (JVM_FIELD.signature f)) = Some f.
    Parameter field_some_in_definedFields : forall c f sfn,
      field c sfn = Some f -> In f (definedFields c).

    Parameter method : JVM_Class -> JVM_ShortMethodSignature -> option JVM_Method.
    Parameter method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = JVM_METHOD.signature m.
    
    Definition defined_Method (cl:JVM_Class) (m:JVM_Method) :=
      method cl (JVM_METHOD.signature m) = Some m.
    
    (* modifiers *)
    Parameter isFinal : JVM_Class -> bool.
    Parameter isPublic : JVM_Class -> bool.
    Parameter isAbstract : JVM_Class -> bool.

  End JVM_CLASS_TYPE.
  Declare Module JVM_CLASS : JVM_CLASS_TYPE.

  (** Content of a Java interface *)
  Module Type JVM_INTERFACE_TYPE.

    Parameter name : JVM_Interface -> JVM_InterfaceName. 

    Parameter superInterfaces : JVM_Interface -> list JVM_InterfaceName.

    Parameter field : JVM_Interface -> JVM_ShortFieldName -> option JVM_Field.

    Parameter method : JVM_Interface -> JVM_ShortMethodSignature -> option JVM_Method.

   (* modifiers *)
    Parameter isFinal : JVM_Interface -> bool.
    Parameter isPublic : JVM_Interface -> bool.
    Parameter isAbstract : JVM_Interface -> bool.
  End JVM_INTERFACE_TYPE.
  Declare Module JVM_INTERFACE : JVM_INTERFACE_TYPE.

  (** Content of a Java Program *)
  Module Type JVM_PROG_TYPE.
    (** accessor to a class from its qualified name *)
    Parameter class : JVM_Program -> JVM_ClassName -> option JVM_Class.
    Definition defined_Class (p:JVM_Program) (cl:JVM_Class) :=
      class p (JVM_CLASS.name cl) = Some cl.

    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = JVM_CLASS.name cl.

    (** accessor to an interface from its qualified name *)
    Parameter interface : JVM_Program -> JVM_InterfaceName -> option JVM_Interface.
    Definition defined_Interface (p:JVM_Program) (i:JVM_Interface) :=
      interface p (JVM_INTERFACE.name i) = Some i.

    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = JVM_INTERFACE.name cl.

  End JVM_PROG_TYPE.
  Declare Module JVM_PROG : JVM_PROG_TYPE.

(**  
      Definitions on programs 
 
  *)


  Inductive isStatic (p:JVM_Program) (fs: JVM_FieldSignature) : Prop :=
    isStatic_field : forall (cn:JVM_ClassName) (cl:JVM_Class) (f:JVM_Field),
     JVM_PROG.class p (fst fs) = Some cl ->
     JVM_CLASS.field cl (JVM_FIELDSIGNATURE.name (snd fs)) = Some f ->
     JVM_FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : JVM_ClassName := (javaLang,object).
(* DEX
  Definition javaLangThrowable : JVM_ClassName := (javaLang,throwable).
*)
  Inductive direct_subclass (p:JVM_Program) (c:JVM_Class) (s:JVM_Class) : Prop :=
    | direct_subclass1 : 
        JVM_PROG.defined_Class p c -> 
        JVM_PROG.defined_Class p s ->
        JVM_CLASS.superClass c = Some (JVM_CLASS.name s) -> 
        direct_subclass p c s.

  (** [subclass] is the reflexive transitive closure of the [direct_subclass] relation 
    (defined over the classes of the program) *)
  Definition subclass (p:JVM_Program) : JVM_Class -> JVM_Class -> Prop :=
    clos_refl_trans JVM_Class (direct_subclass p).

  Inductive subclass_name (p:JVM_Program) : JVM_ClassName -> JVM_ClassName -> Prop :=
    | subclass_name1 : forall c1 c2, 
       subclass p c1 c2 -> 
       subclass_name p (JVM_CLASS.name c1) (JVM_CLASS.name c2).

  Inductive direct_subclass_name (p:JVM_Program) : JVM_ClassName -> JVM_ClassName -> Prop :=
    | direct_subclass_name1 : forall c s,
       direct_subclass p c s ->
       direct_subclass_name p (JVM_CLASS.name c) (JVM_CLASS.name s).

  (** Similar definitions for interfaces *)
  Inductive direct_subinterface (p:JVM_Program) (c:JVM_Interface) (s:JVM_Interface) : Prop :=
    | direct_subinterface1 : 
      JVM_PROG.defined_Interface p c -> 
      JVM_PROG.defined_Interface p s ->
      In (JVM_INTERFACE.name s) (JVM_INTERFACE.superInterfaces c) -> 
      direct_subinterface p c s.

  (** [subinterface] is the reflexive transitive closure of the [direct_subinterface] 
      relation (defined over the interfaces of the program) *)
  Definition subinterface (p:JVM_Program) : JVM_Interface -> JVM_Interface -> Prop :=
    clos_refl_trans JVM_Interface (direct_subinterface p).

  Inductive subinterface_name (p:JVM_Program) : JVM_InterfaceName -> JVM_InterfaceName -> Prop :=
    | subinterface_name1 : forall c1 c2, 
       subinterface p c1 c2 -> 
       subinterface_name p (JVM_INTERFACE.name c1) (JVM_INTERFACE.name c2).

  Inductive direct_subinterface_name (p:JVM_Program) : JVM_InterfaceName -> JVM_InterfaceName -> Prop :=
    | direct_subinterface_name1 : forall c s,
       direct_subinterface p c s ->
       direct_subinterface_name p (JVM_INTERFACE.name c) (JVM_INTERFACE.name s).

  Inductive class_declares_field (p:JVM_Program) (cn:JVM_ClassName) (fd:JVM_ShortFieldSignature) : JVM_Field -> Prop :=
    | class_decl_field : forall cl f, 
      JVM_PROG.class p cn = Some cl -> 
      JVM_CLASS.field cl (JVM_FIELDSIGNATURE.name fd) = Some f -> 
      class_declares_field p cn fd f.

  Inductive interface_declares_field (p:JVM_Program) (cn:JVM_InterfaceName) (fd:JVM_ShortFieldSignature) : JVM_Field -> Prop :=
    | interface_decl_field : forall cl f, 
      JVM_PROG.interface p cn = Some cl -> 
      JVM_INTERFACE.field cl (JVM_FIELDSIGNATURE.name fd) = Some f -> 
      interface_declares_field p cn fd f.

  (** [defined_field p c fd] holds if the class [c] declares or inherits a field 
      of signature [fd] *)
  Inductive is_defined_field (p:JVM_Program) : JVM_ClassName -> JVM_FieldSignature -> JVM_Field -> Prop :=
    | def_class_field : forall cn fd cn' f,
        subclass_name p cn cn' -> 
        class_declares_field p cn' fd f -> 
        is_defined_field p cn (cn',fd) f
    | def_interface_field : forall cn fd cl i1 i' f, 
        JVM_PROG.class p cn = Some cl -> 
        In i1 (JVM_CLASS.superInterfaces cl) ->
        subinterface_name p i1 i' -> 
        interface_declares_field p i' fd f -> 
        is_defined_field p cn (i',fd) f.

  Definition defined_field (p:JVM_Program) (cn:JVM_ClassName) (fs:JVM_FieldSignature) : Prop :=
    exists f, is_defined_field p cn fs f.

  Definition findMethod (p:JVM_Program) (msig: JVM_MethodSignature) : option JVM_Method :=
    let (cn,smsig) := msig in
      match JVM_PROG.class p cn with
	| None => None
	| Some cl => JVM_CLASS.method cl smsig 
      end.

  Definition findField (p:JVM_Program) (fd: JVM_FieldSignature) : option JVM_Field :=
    let (cn,sfs) := fd in   
      match JVM_PROG.class p cn with
	| None => None
	| Some cl => JVM_CLASS.field cl (JVM_FIELDSIGNATURE.name sfs)
      end.
    

  Definition methodPackage (mname: JVM_MethodName) : JVM_PackageName :=  fst (fst mname).

  (* Relations [check_visibility,check_signature,overrides] are needed
  to define the method [lookup] algorithm **)

  Inductive check_visibility : JVM_Visibility -> JVM_PackageName -> JVM_PackageName ->  Prop :=
    | check_public :  forall p1 p2, check_visibility Public p1 p2
    | check_protected :forall p1 p2, check_visibility Protected p1 p2
    | check_package :forall p, check_visibility Package p p.
	  
  Inductive lookup_here (p:JVM_Program) : JVM_ClassName ->  JVM_ShortMethodSignature -> JVM_Method -> Prop :=
    | lookup_here_c : forall cn msig meth, 
       findMethod p (cn,msig) = Some meth -> 
       lookup_here p cn msig meth.


  Inductive lookup (p:JVM_Program) : JVM_ClassName -> JVM_ShortMethodSignature -> (JVM_ClassName*JVM_Method) -> Prop :=
    | lookup_no_up : forall cn msig meth, lookup_here p cn msig meth -> lookup p cn msig (cn,meth)
    | lookup_up : forall cn  msig, (forall meth, ~ lookup_here p cn msig meth) -> 
      forall super res , direct_subclass_name p cn super -> lookup p super msig res -> lookup p cn msig res.

(* DEX
  Inductive handler_catch (p:Program) : ExceptionHandler -> PC -> ClassName -> Prop :=
  (* The current handler catches all the exceptions in its range *)
  | handler_catch_all : forall pc ex e,
    EXCEPTIONHANDLER.catchType ex = None ->
    EXCEPTIONHANDLER.isPCinRange ex pc = true ->
    handler_catch p ex pc e

  (* The current handler specifies the type of exception it catches *)
  | handler_catch_one : forall pc ex cl1 cl2,
    EXCEPTIONHANDLER.catchType ex = Some cl1 ->
    EXCEPTIONHANDLER.isPCinRange ex pc = true ->
    subclass_name p cl2 cl1 ->
    handler_catch p ex pc cl2.


  (** Lookup in the given list of exception handlers if one of them catches
      the current exception *)

  Inductive lookup_handlers (p:Program) : list ExceptionHandler -> PC -> ClassName -> PC -> Prop :=
  (* The current handler catches the exception *)
  | lookup_handlers_hd_catchAll : forall pc ex exl e,
    handler_catch p ex pc e ->
    lookup_handlers p (ex::exl) pc e (EXCEPTIONHANDLER.handler ex)

  (* Continue with the next handler *)
  | lookup_handlers_tl : forall ex exl pc e pc',
    ~ handler_catch p ex pc e ->
    lookup_handlers p exl pc e pc' ->
    lookup_handlers p (ex::exl) pc e pc'.
*)
  (** Get the next pc *)
  Definition next (m:JVM_Method) (pc:JVM_PC) : option JVM_PC :=
    match JVM_METHOD.body m with
      None => None
    | Some body => JVM_BYTECODEMETHOD.nextAddress body pc
    end.

  (** Get the instruction at the given pc *)
  Definition instructionAt (m:JVM_Method) (pc:JVM_PC) : option JVM_Instruction :=
    match JVM_METHOD.body m with
      None => None
    | Some body => JVM_BYTECODEMETHOD.instructionAt body pc
    end.

  Inductive implements (p:JVM_Program) : JVM_ClassName -> JVM_InterfaceName -> Prop :=
    | implements_def : forall i cl i', 
           JVM_PROG.defined_Interface p i -> 
           JVM_PROG.defined_Class p cl ->
           In (JVM_INTERFACE.name i) (JVM_CLASS.superInterfaces cl) ->
           subinterface_name p (JVM_INTERFACE.name i) i' ->
           implements p (JVM_CLASS.name cl) i'.

  (** [compat_refType source target] holds if a reference value of type [source] can be 
    assigned to a reference variable of type [target]. See 
    #<a href=http://java.sun.com/docs/books/vmspec/2nd-edition/html/Concepts.doc.html##19674>assignment conversion rules</a># *)

  Inductive compat_refType (p:JVM_Program) : JVM_refType -> JVM_refType -> Prop :=
   | compat_refType_class_class : forall clS clT,
       subclass_name p clS clT ->
       compat_refType p (JVM_ClassType clS) (JVM_ClassType clT)
   | compat_refType_class_interface : forall clS clT,
       implements p clS clT ->
       compat_refType p (JVM_ClassType clS) (JVM_ClassType clT)
   | compat_refType_interface_class : forall clS,
       JVM_PROG.defined_Interface p clS ->
       compat_refType p (JVM_ClassType (JVM_INTERFACE.name clS)) (JVM_ClassType javaLangObject)
   | compat_refType_interface_interface : forall clS clT,
       JVM_PROG.defined_Interface p clS ->
       subinterface p clS clT ->
       compat_refType p (JVM_ClassType (JVM_INTERFACE.name clS)) (JVM_ClassType (JVM_INTERFACE.name clT))
   | compat_refType_array_class : forall tpS,       
       compat_refType p (JVM_ArrayType tpS) (JVM_ClassType javaLangObject)
   (* FIXME: array_interface : T must be either Cloneable or java.io.Serializable? - dp *)
   | compat_refType_array_array_primitive_type : forall t,       
       compat_refType p (JVM_ArrayType (JVM_PrimitiveType t)) (JVM_ArrayType (JVM_PrimitiveType t))
   | compat_refType_array_array_reference_type : forall tpS tpT,       
       compat_refType p tpS tpT ->
       compat_refType p (JVM_ArrayType (JVM_ReferenceType tpS)) (JVM_ArrayType (JVM_ReferenceType tpT)).


  (** Extra tools for implementation *)
  Parameter JVM_PC_eq : JVM_PC -> JVM_PC -> bool.
  Parameter JVM_PC_eq_spec : forall p q:JVM_PC, if JVM_PC_eq p q then p=q else p<>q.
  Parameter JVM_PC_eq_dec : forall pc1 pc2:JVM_PC, pc1=pc2 \/ ~pc1=pc2.
  
  Parameter Var_eq_dec : forall x1 x2:JVM_Var, x1=x2 \/ ~x1=x2. 
  Parameter ClassName_eq_dec : forall c1 c2:JVM_ClassName, c1=c2 \/ ~c1=c2.

End JVM_PROGRAM.
    
   
(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
