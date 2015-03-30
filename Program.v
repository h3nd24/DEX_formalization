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

(** Main module for representing a DEX program *)

Module Type PROGRAM.

  (** Main types to be manipulated by the API *)
  Parameter Program :Type.
  Parameter Class : Type.
  Parameter Interface : Type. (*- They are collapsed to class with a special access flag *)
  Parameter Var : Set. (* In DEX, registers are indexed by natural number *)
  Parameter Field : Set.
  Parameter Method : Type.
  Parameter BytecodeMethod : Type.
  Parameter ExceptionHandler : Set.
  Parameter ShortMethodSignature : Set.
  Parameter ShortFieldSignature :Set.
  Parameter PC : Set.

 (** Variables are indexed by integers *)
  Parameter Var_toN : Var -> nat.
  Parameter N_toVar : nat -> Var.
  Parameter Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Parameter Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.


  (** Handling of qualified names *)
  Parameter PackageName : Set.
  Parameter ShortClassName : Set.
  Parameter ShortMethodName : Set.
  Parameter ShortFieldName : Set.

  (**For example the qualified name [java.lang.String] of the class [String],
      is decomposed into [java.lang] for the package name and [String] for the
       short name.  *)
  Definition ClassName := PackageName * ShortClassName.
  Definition InterfaceName := PackageName * ShortClassName.
  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.
  Definition MethodSignature := ClassName * ShortMethodSignature.
  Definition FieldSignature := ClassName * ShortFieldSignature.
  (** Some constants *)
  Parameter javaLang : PackageName.
  Parameter object : ShortClassName.
  Parameter throwable : ShortClassName.

  (** Native Exceptions *)
  Parameter NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName.

  (** visibility modifiers *)
  Inductive Visibility : Set :=
    Package | Protected | Private | Public.

  Inductive type : Set :=
      | ReferenceType (rt : refType)
      | PrimitiveType (pt: primitiveType)
  with refType :Set := 
      | ArrayType (typ:type) 
      | ClassType  (ct:ClassName)
      | InterfaceType (it:InterfaceName)
  with  primitiveType : Set := 
      | BOOLEAN  | BYTE | SHORT | INT.
      (* + Int64, Float,Double *)
      (* + ReturnAddressType subroutines *)

 
  Inductive CompInt : Set := EqInt | NeInt | LtInt | LeInt | GtInt | GeInt.
  Inductive CompRef : Set := EqRef | NeRef.

  Inductive BinopInt : Set := AddInt | AndInt | DivInt | MulInt | OrInt | RemInt 
                            | ShlInt | ShrInt | SubInt | UshrInt | XorInt.

  (* Type information used for Vaload and Saload *)
  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  (* Type information used for Vload, Vstore and Vreturn *)
  Inductive ValKind : Set :=
    | Aval
    | Ival.


  Module Type OFFSET_TYPE.
    (* The type of address offsets *)
    Parameter t : Set.
     (** Jumps are defined in terms of offsets with respect to the current address. **)
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Declare Module OFFSET : OFFSET_TYPE.

  (** Operations on the signatures of fields *)
  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : ShortFieldSignature -> ShortFieldName.
    Parameter type : ShortFieldSignature -> type.
    Parameter eq_dec : forall f1 f2:ShortFieldSignature, f1=f2 \/ ~f1=f2.
  End FIELDSIGNATURE_TYPE.
  Declare Module FIELDSIGNATURE : FIELDSIGNATURE_TYPE.

  (** Content of a method signature *)
  Module Type METHODSIGNATURE_TYPE.
    (* The method name *)
    Parameter name : ShortMethodSignature -> ShortMethodName.
    (** Java types for parameters values *)
    Parameter parameters : ShortMethodSignature -> list type.
    (** Java type for return value, the constructor [None] of type option being used for the [Void] type *)
    Parameter result : ShortMethodSignature -> option type.

    Parameter eq_dec : 
      forall mid1 mid2:ShortMethodSignature, mid1=mid2 \/ ~mid1=mid2.
  End METHODSIGNATURE_TYPE.
  Declare Module METHODSIGNATURE : METHODSIGNATURE_TYPE.

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

  Inductive Instruction : Set :=
   | Aconst_null
   | Arraylength 
   | Athrow
   | Checkcast (t:refType)
   | Const (t:primitiveType) (z:Z)
   | Dup
   | Dup_x1
   | Dup_x2
   | Dup2
   | Dup2_x1
   | Dup2_x2
   | Getfield (f:FieldSignature)
   | Goto (o:OFFSET.t)
   | I2b
   | I2s
   | Ibinop (op:BinopInt)
   | If_acmp (cmp:CompRef) (o:OFFSET.t)
   | If_icmp (cmp:CompInt) (o:OFFSET.t) 
   | If0 (cmp:CompInt) (o:OFFSET.t)
   | Ifnull (cmp:CompRef) (o:OFFSET.t)
   | Iinc (x:Var) (z:Z)
   | Ineg 
   | Instanceof (t:refType) 
   | Invokeinterface (m:MethodSignature)
   | Invokespecial (m:MethodSignature)
   | Invokestatic (m:MethodSignature)
   | Invokevirtual (m:MethodSignature)
   | Lookupswitch (def:OFFSET.t) (l:list (Z*OFFSET.t)) 
(*   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) *)
   | New (c:ClassName)
   | Newarray (t:type)
   | Nop
   | Pop
   | Pop2
   | Putfield (f:FieldSignature)
   | Return
   | Swap 
   | Tableswitch (def:OFFSET.t) (low high:Z) (l:list OFFSET.t)
   | Vaload (k:ArrayKind) 
   | Vastore (k:ArrayKind)
   | Vload (k:ValKind) (x:Var)
   | Vreturn (k:ValKind)
   | Vstore (k:ValKind) (x:Var).

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

  (** Operations on bytecode methods *)
  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    (* The list of exception is supposed to be ordered from the innermost to
       the outermost handler, otherwise the behavior might be unexpected 
       @see JVMS 3.10 *)
    Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.

    (** max number of local variables *)
    Parameter max_locals : BytecodeMethod -> nat.
    (** max number of elements on the operand stack *)
    Parameter max_operand_stack_size : BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
   
  End BYTECODEMETHOD_TYPE.
  Declare Module BYTECODEMETHOD : BYTECODEMETHOD_TYPE.
 
  (** Content of a method *)
  Module Type METHOD_TYPE.

    Parameter signature : Method -> ShortMethodSignature.
    (** A method that is not abstract has an empty method body *)
    Parameter body : Method -> option BytecodeMethod.

    (* modifiers *)
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter isNative : Method -> bool.
    Definition isAbstract (m : Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.

    Parameter visibility : Method -> Visibility.

    Definition valid_var (m:Method) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
         (Var_toN x) <= (BYTECODEMETHOD.max_locals bm).

    Definition valid_stack_size (m:Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         length <= (BYTECODEMETHOD.max_operand_stack_size bm).

    End METHOD_TYPE.
  Declare Module METHOD : METHOD_TYPE.

  (** Operations on fields *)
  Module Type FIELD_TYPE.
    Parameter signature : Field -> ShortFieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter isStatic : Field -> bool.

    Parameter visibility : Field -> Visibility.

    Inductive value : Set :=
      | Int (v:Z) (* Numeric value *)
(*      | Lst (l:list Z)   Array of nums *)
      | NULL (* reference *)
      | UNDEF (* default value *).

    (** Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : Field ->  value.

  End FIELD_TYPE.
  Declare Module FIELD : FIELD_TYPE.

  (** Content of a Java class *)
  Module Type CLASS_TYPE.

    Parameter name : Class -> ClassName.
    (** direct superclass *)
    (** All the classes have a superClass except [java.lang.Object]. (see [Wf.v]) *)
    Parameter superClass : Class -> option ClassName.
    (** list of implemented interfaces *)
    Parameter superInterfaces : Class -> list InterfaceName.

    Parameter field : Class -> ShortFieldName -> option Field.

    Parameter definedFields : Class -> list Field.
    Parameter in_definedFields_field_some : forall c f,
      In f (definedFields c) ->
      field c (FIELDSIGNATURE.name (FIELD.signature f)) = Some f.
    Parameter field_some_in_definedFields : forall c f sfn,
      field c sfn = Some f -> In f (definedFields c).

    Parameter method : Class -> ShortMethodSignature -> option Method.
    Parameter method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    
    Definition defined_Method (cl:Class) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
    
    (* modifiers *)
    Parameter isFinal : Class -> bool.
    Parameter isPublic : Class -> bool.
    Parameter isAbstract : Class -> bool.

  End CLASS_TYPE.
  Declare Module CLASS : CLASS_TYPE.

  (** Content of a Java interface *)
  Module Type INTERFACE_TYPE.

    Parameter name : Interface -> InterfaceName. 

    Parameter superInterfaces : Interface -> list InterfaceName.

    Parameter field : Interface -> ShortFieldName -> option Field.

    Parameter method : Interface -> ShortMethodSignature -> option Method.

   (* modifiers *)
    Parameter isFinal : Interface -> bool.
    Parameter isPublic : Interface -> bool.
    Parameter isAbstract : Interface -> bool.
  End INTERFACE_TYPE.
  Declare Module INTERFACE : INTERFACE_TYPE.

  (** Content of a Java Program *)
  Module Type PROG_TYPE.
    (** accessor to a class from its qualified name *)
    Parameter class : Program -> ClassName -> option Class.
    Definition defined_Class (p:Program) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.

    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.

    (** accessor to an interface from its qualified name *)
    Parameter interface : Program -> InterfaceName -> option Interface.
    Definition defined_Interface (p:Program) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.

    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = INTERFACE.name cl.

  End PROG_TYPE.
  Declare Module PROG : PROG_TYPE.

(**  
      Definitions on programs 
 
  *)


  Inductive isStatic (p:Program) (fs: FieldSignature) : Prop :=
    isStatic_field : forall (cn:ClassName) (cl:Class) (f:Field),
     PROG.class p (fst fs) = Some cl ->
     CLASS.field cl (FIELDSIGNATURE.name (snd fs)) = Some f ->
     FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : ClassName := (javaLang,object).
  Definition javaLangThrowable : ClassName := (javaLang,throwable).

  Inductive direct_subclass (p:Program) (c:Class) (s:Class) : Prop :=
    | direct_subclass1 : 
        PROG.defined_Class p c -> 
        PROG.defined_Class p s ->
        CLASS.superClass c = Some (CLASS.name s) -> 
        direct_subclass p c s.

  (** [subclass] is the reflexive transitive closure of the [direct_subclass] relation 
    (defined over the classes of the program) *)
  Definition subclass (p:Program) : Class -> Class -> Prop :=
    clos_refl_trans Class (direct_subclass p).

  Inductive subclass_name (p:Program) : ClassName -> ClassName -> Prop :=
    | subclass_name1 : forall c1 c2, 
       subclass p c1 c2 -> 
       subclass_name p (CLASS.name c1) (CLASS.name c2).

  Inductive direct_subclass_name (p:Program) : ClassName -> ClassName -> Prop :=
    | direct_subclass_name1 : forall c s,
       direct_subclass p c s ->
       direct_subclass_name p (CLASS.name c) (CLASS.name s).

  (** Similar definitions for interfaces *)
  Inductive direct_subinterface (p:Program) (c:Interface) (s:Interface) : Prop :=
    | direct_subinterface1 : 
      PROG.defined_Interface p c -> 
      PROG.defined_Interface p s ->
      In (INTERFACE.name s) (INTERFACE.superInterfaces c) -> 
      direct_subinterface p c s.

  (** [subinterface] is the reflexive transitive closure of the [direct_subinterface] 
      relation (defined over the interfaces of the program) *)
  Definition subinterface (p:Program) : Interface -> Interface -> Prop :=
    clos_refl_trans Interface (direct_subinterface p).

  Inductive subinterface_name (p:Program) : InterfaceName -> InterfaceName -> Prop :=
    | subinterface_name1 : forall c1 c2, 
       subinterface p c1 c2 -> 
       subinterface_name p (INTERFACE.name c1) (INTERFACE.name c2).

  Inductive direct_subinterface_name (p:Program) : InterfaceName -> InterfaceName -> Prop :=
    | direct_subinterface_name1 : forall c s,
       direct_subinterface p c s ->
       direct_subinterface_name p (INTERFACE.name c) (INTERFACE.name s).

  Inductive class_declares_field (p:Program) (cn:ClassName) (fd:ShortFieldSignature) : Field -> Prop :=
    | class_decl_field : forall cl f, 
      PROG.class p cn = Some cl -> 
      CLASS.field cl (FIELDSIGNATURE.name fd) = Some f -> 
      class_declares_field p cn fd f.

  Inductive interface_declares_field (p:Program) (cn:InterfaceName) (fd:ShortFieldSignature) : Field -> Prop :=
    | interface_decl_field : forall cl f, 
      PROG.interface p cn = Some cl -> 
      INTERFACE.field cl (FIELDSIGNATURE.name fd) = Some f -> 
      interface_declares_field p cn fd f.

  (** [defined_field p c fd] holds if the class [c] declares or inherits a field 
      of signature [fd] *)
  Inductive is_defined_field (p:Program) : ClassName -> FieldSignature -> Field -> Prop :=
    | def_class_field : forall cn fd cn' f,
        subclass_name p cn cn' -> 
        class_declares_field p cn' fd f -> 
        is_defined_field p cn (cn',fd) f
    | def_interface_field : forall cn fd cl i1 i' f, 
        PROG.class p cn = Some cl -> 
        In i1 (CLASS.superInterfaces cl) ->
        subinterface_name p i1 i' -> 
        interface_declares_field p i' fd f -> 
        is_defined_field p cn (i',fd) f.

  Definition defined_field (p:Program) (cn:ClassName) (fs:FieldSignature) : Prop :=
    exists f, is_defined_field p cn fs f.

  Definition findMethod (p:Program) (msig: MethodSignature) : option Method :=
    let (cn,smsig) := msig in
      match PROG.class p cn with
	| None => None
	| Some cl => CLASS.method cl smsig 
      end.

  Definition findField (p:Program) (fd: FieldSignature) : option Field :=
    let (cn,sfs) := fd in   
      match PROG.class p cn with
	| None => None
	| Some cl => CLASS.field cl (FIELDSIGNATURE.name sfs)
      end.
    

  Definition methodPackage (mname: MethodName) : PackageName :=  fst (fst mname).

  (* Relations [check_visibility,check_signature,overrides] are needed
  to define the method [lookup] algorithm **)

  Inductive check_visibility : Visibility -> PackageName -> PackageName ->  Prop :=
    | check_public :  forall p1 p2, check_visibility Public p1 p2
    | check_protected :forall p1 p2, check_visibility Protected p1 p2
    | check_package :forall p, check_visibility Package p p.
	  
  Inductive lookup_here (p:Program) : ClassName ->  ShortMethodSignature -> Method -> Prop :=
    | lookup_here_c : forall cn msig meth, 
       findMethod p (cn,msig) = Some meth -> 
       lookup_here p cn msig meth.


  Inductive lookup (p:Program) : ClassName -> ShortMethodSignature -> (ClassName*Method) -> Prop :=
    | lookup_no_up : forall cn msig meth, lookup_here p cn msig meth -> lookup p cn msig (cn,meth)
    | lookup_up : forall cn  msig, (forall meth, ~ lookup_here p cn msig meth) -> 
      forall super res , direct_subclass_name p cn super -> lookup p super msig res -> lookup p cn msig res.

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

  (** Get the next pc *)
  Definition next (m:Method) (pc:PC) : option PC :=
    match METHOD.body m with
      None => None
    | Some body => BYTECODEMETHOD.nextAddress body pc
    end.

  (** Get the instruction at the given pc *)
  Definition instructionAt (m:Method) (pc:PC) : option Instruction :=
    match METHOD.body m with
      None => None
    | Some body => BYTECODEMETHOD.instructionAt body pc
    end.

  Inductive implements (p:Program) : ClassName -> InterfaceName -> Prop :=
    | implements_def : forall i cl i', 
           PROG.defined_Interface p i -> 
           PROG.defined_Class p cl ->
           In (INTERFACE.name i) (CLASS.superInterfaces cl) ->
           subinterface_name p (INTERFACE.name i) i' ->
           implements p (CLASS.name cl) i'.

  (** [compat_refType source target] holds if a reference value of type [source] can be 
    assigned to a reference variable of type [target]. See 
    #<a href=http://java.sun.com/docs/books/vmspec/2nd-edition/html/Concepts.doc.html##19674>assignment conversion rules</a># *)

  Inductive compat_refType (p:Program) : refType -> refType -> Prop :=
   | compat_refType_class_class : forall clS clT,
       subclass_name p clS clT ->
       compat_refType p (ClassType clS) (ClassType clT)
   | compat_refType_class_interface : forall clS clT,
       implements p clS clT ->
       compat_refType p (ClassType clS) (ClassType clT)
   | compat_refType_interface_class : forall clS,
       PROG.defined_Interface p clS ->
       compat_refType p (ClassType (INTERFACE.name clS)) (ClassType javaLangObject)
   | compat_refType_interface_interface : forall clS clT,
       PROG.defined_Interface p clS ->
       subinterface p clS clT ->
       compat_refType p (ClassType (INTERFACE.name clS)) (ClassType (INTERFACE.name clT))
   | compat_refType_array_class : forall tpS,       
       compat_refType p (ArrayType tpS) (ClassType javaLangObject)
   (* FIXME: array_interface : T must be either Cloneable or java.io.Serializable? - dp *)
   | compat_refType_array_array_primitive_type : forall t,       
       compat_refType p (ArrayType (PrimitiveType t)) (ArrayType (PrimitiveType t))
   | compat_refType_array_array_reference_type : forall tpS tpT,       
       compat_refType p tpS tpT ->
       compat_refType p (ArrayType (ReferenceType tpS)) (ArrayType (ReferenceType tpT)).


  (** Extra tools for implementation *)
  Parameter PC_eq : PC -> PC -> bool.
  Parameter PC_eq_spec : forall p q:PC, if PC_eq p q then p=q else p<>q.
  Parameter PC_eq_dec : forall pc1 pc2:PC, pc1=pc2 \/ ~pc1=pc2.
  
  Parameter Var_eq_dec : forall x1 x2:Var, x1=x2 \/ ~x1=x2. 
  Parameter ClassName_eq_dec : forall c1 c2:ClassName, c1=c2 \/ ~c1=c2.

End PROGRAM.
    
   
(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
