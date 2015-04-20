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
  (*Parameter ExceptionHandler : Set.*)
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
  (*Parameter throwable : ShortClassName.*)

  (** Native Exceptions *)
(*  Parameter NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName. *)

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

(*  Inductive Instruction : Set :=
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
   | Vstore (k:ValKind) (x:Var).*)

(** Parser translation :

  nop                            --> Nop
  move vA, vB                    --> Move (IVal) (rt:Reg) (rs:Reg)
  move/from16 vAA, vBBBB         --> Move (IVal) (rt:Reg) (rs:Reg)
  move/16 vAAAA, vBBBB           --> Move (IVal) (rt:Reg) (rs:Reg)
  move-wide vA, vB               --> wide value not supported
  move-wide/from16 vAA, vBBBB    --> wide value not supported
  move-wide/16 vAAAA, vBBBB      --> wide value not supported
  move-object vA, vB             --> Move (AVal) (rt:Reg) (rs:Reg)
  move-object/from16 vAA, vBBBB  --> Move (AVal) (rt:Reg) (rs:Reg)
  move-object/16 vAAAA, vBBBB    --> Move (AVal) (rt:Reg) (rs:Reg)
  move-result vAA                --> Move-result (IVal) (rt:Reg)
  move-result-wide vAA           --> wide value not supported
  move-result-object vAA         --> Move-result (AVal) (rt:Reg)
  move-exception vAA             --> exception not yet supported
  return-void                    --> Return
  return vAA                     --> Vreturn (IVal) (rs:Reg)
  return-wide vAA                --> wide value not supported
  return-object vAA              --> Vreturn (AVal) (rs:Reg)
  const/4 vA, #+B                --> Const (IVal) (rt:Reg) (v:Z)
  const/16 vAA, #+BBBB           --> Const (IVal) (rt:Reg) (v:Z)
  const vAA, #+BBBBBBBB          --> Const (IVal) (rt:Reg) (v:Z)
  const/high16 vAA, #+BBBB0000   --> Const (IVal) (rt:Reg) (v:Z)
  const-wide/16 vAA, #+BBBB      --> wide value not supported 
  const-wide/32 vAA, #+BBBBBBBB  --> wide value not supported 
  const-wide vAA,                --> wide value not supported
    #+BBBBBBBBBBBBBBBB
  const-string vAA, string@BBBB  --> string value not supported
  const-class vAA, type@BBBB     --> not supported as it is not clear what's the function, 
                                    while the inclusion will bring extra complexity
  monitor-enter vAA              --> multithreading not supported
  monitor-exit vAA               --> multithreading not supported
  check-cast vAA, type@BBBB      --> exception not yet supported
  instance-of vA, vB, type@CCCC  --> InstanceOf (rt:Reg) (r:Reg) (t:refType)
  array-length vA, vB            --> ArrayLength (rt:Reg) (rs:Reg)
  new-instance vAA, type@BBBB    --> New (rt:Reg) (t:refType)
  new-array vA, vB, type@CCCC    --> NewArray (rt:Reg) (rl:Reg) (t:type)
  filled-new-array {vC, vD, vE,  --> not supported
    vF, vG}, type@BBBB
  filled-new-array/range {vCCCC  --> not supported
    ... vNNNN}, type@BBBB
  fill-array-data vAA, +BBBBBBBB --> not supported (yet)
  goto +AA                       --> Goto (o:OFFSET.t)
  goto/16 +AAAA                  --> Goto (o:OFFSET.t)
  goto/32 +AAAAAAAA              --> Goto (o:OFFSET.t)
  packed-switch vAA, +BBBBBBBB   --> PackedSwitch (rt:Reg) (psd:PackedSwitchData)
  sparse-switch vAA, +BBBBBBBB   --> SparseSwitch (rt:Reg) (ssd:SparseSwitchData)
  cmplkind vAA, vBB, vCC
    cmpl-float (lt bias)         --> float not supported
    cmpg-float (gt bias)         --> float not supported
    cmpl-double (lt bias)        --> double not supported
    cmpg-double (gt bias)        --> double not supported
    cmp-long                     --> long not supported
  if-test vA, vB +CCCC           
    if-eq                        --> If (EqInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
    if-ne                        --> If (NeInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
    if-lt                        --> If (LtInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
    if-ge                        --> If (GeInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
    if-gt                        --> If (GtInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
    if-le                        --> If (LeInt) (ra:Reg) (rb:Reg) (o:OFFSET.t)
  if-testz vAA, +BBBB
    if-eq                        --> Ifz (EqInt) (ra:Reg) (o:OFFSET.t)
    if-ne                        --> Ifz (NeInt) (ra:Reg) (o:OFFSET.t)
    if-lt                        --> Ifz (LtInt) (ra:Reg) (o:OFFSET.t)
    if-ge                        --> Ifz (GeInt) (ra:Reg) (o:OFFSET.t)
    if-gt                        --> Ifz (GtInt) (ra:Reg) (o:OFFSET.t)
    if-le                        --> Ifz (LeInt) (ra:Reg) (o:OFFSET.t)
  arrayop vAA, vBB, vCC
    aget                         --> Aget (IVal INT) (rt:Reg) (ra:Reg) (ri:Reg)
    aget-wide                    --> wide value not supported
    aget-object                  --> Aget (AVal) (rt:Reg) (ra:Reg) (ri:Reg)
    aget-boolean                 --> Aget (IVal BOOLEAN) (rt:Reg) (ra:Reg) (ri:Reg)
    aget-byte                    --> Aget (IVal BYTE) (rt:Reg) (ra:Reg) (ri:Reg)
    aget-char                    --> char not supported
    aget-short                   --> Aget (IVal SHORT) (rt:Reg) (ra:Reg) (ri:Reg)
    aput                         --> Aput (IVal) (rt:Reg) (ra:Reg) (ri:Reg)
    aput-wide                    --> wide value not supported
    aput-object                  --> Aput (AVal) (rt:Reg) (ra:Reg) (ri:Reg)
    aput-boolean                 --> Aput (IVal BOOLEAN) (rt:Reg) (ra:Reg) (ri:Reg)
    aput-byte                    --> Aput (IVal Byte) (rt:Reg) (ra:Reg) (ri:Reg)
    aput-char                    --> char not supported
    aput-short                   --> Aput (IVal SHORT) (rt:Reg) (ra:Reg) (ri:Reg)
  iinstanceop vA, vB, field@CCCC
    aget                         --> Aget (IVal INT) (rt:Reg) (ro:Reg) (f:FieldSignature)
    aget-wide                    --> wide value not supported
    aget-object                  --> Aget (AVal) (rt:Reg) (ro:Reg) (f:FieldSignature)
    aget-boolean                 --> Aget (IVal BOOLEAN) (rt:Reg) (ro:Reg) (f:FieldSignature)
    aget-byte                    --> Aget (IVal BYTE) (rt:Reg) (ro:Reg) (f:FieldSignature)
    aget-char                    --> char not supported
    aget-short                   --> Aget (IVal SHORT) (rt:Reg) (ro:Reg) (f:FieldSignature)
    aput                         --> Aput (IVal) (rs:Reg) (ro:Reg) (f:FieldSignature)
    aput-wide                    --> wide value not supported
    aput-object                  --> Aput (AVal) (rs:Reg) (ro:Reg) (f:FieldSignature)
    aput-boolean                 --> Aput (IVal BOOLEAN) (rs:Reg) (ro:Reg) (f:FieldSignature)
    aput-byte                    --> Aput (IVal Byte) (rs:Reg) (ro:Reg) (f:FieldSignature)
    aput-char                    --> char not supported
    aput-short                   --> Aput (IVal SHORT) (rs:Reg) (ro:Reg) (f:FieldSignature)
  sstaticop vAA, field@BBBB
    sget                         --> Sget (IVal INT) (rt:Reg) (f:FieldSignature)
    sget-wide                    --> wide value not supported
    sget-object                  --> Sget (AVal) (rt:Reg) (f:FieldSignature)
    sget-boolean                 --> Sget (IVal BOOLEAN) (rt:Reg) (f:FieldSignature)
    sget-byte                    --> Sget (IVal BYTE) (rt:Reg) (f:FieldSignature)
    sget-char                    --> char not supported
    sget-short                   --> Sget (IVal SHORT) (rt:Reg) (f:FieldSignature)
    sput                         --> Sput (IVal) (rs:Reg) (f:FieldSignature)
    sput-wide                    --> Side value not supported
    sput-object                  --> Sput (AVal) (rs:Reg) (f:FieldSignature)
    sput-boolean                 --> Sput (IVal BOOLEAN) (rs:Reg) (f:FieldSignature)
    sput-byte                    --> Sput (IVal Byte) (rs:Reg) (f:FieldSignature)
    sput-char                    --> char not supported
    sput-short                   --> Sput (IVal SHORT) (rs:Reg) (f:FieldSignature)
  invoke-kind {vC, vD, vE, vF, vG}, meth@BBBB
    invoke-virtual               --> Invokevirtual (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-super                 --> Invokesuper (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-direct                --> Invokedirect (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-static                --> Invokestatic (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-interface             --> Invokeinterface (m:MethodSignature) (n:Z) (p:list Reg)
  invoke-kind/range {vCCCC ... vNNNN}, meth@BBBB
    invoke-virtual/range         --> Invokevirtual (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-super/range           --> Invokesuper (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-direct/range          --> Invokedirect (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-static/range          --> Invokestatic (m:MethodSignature) (n:Z) (p:list Reg)
    invoke-interface/range       --> Invokeinterface (m:MethodSignature) (n:Z) (p:list Reg)    
  unop vA, vB
    neg-int                      --> Ineg (rt:Reg) (rs:Reg)
    not-int                      --> Inot (rt:Reg) (rs:Reg) **doubt we need this
    neg-long                     --> long not supported
    not-long                     --> long not supported
    neg-float                    --> float not supported
    neg-double                   --> double not supported
    int-to-long                  --> long not supported
    int-to-float                 --> float not supported
    long-to-float                --> float / long not supported
    long-to-double               --> double / long not supported
    float-to-int                 --> float not supported
    float-to-double              --> double / float not supported
    double-to-int                --> double not supported
    double-to-long               --> double / long not supported
    double-to-float              --> double / float not supported
    int-to-byte                  --> I2b (rt:Reg) (rs:Reg)
    int-to-char                  --> char not supported
    int-to-short                 --> I2s (rt:Reg) (rs:Reg)
  binop vAA, vBB, vCC
    add-int                      --> Ibinop (AddInt) (rt:Reg) (ra:Reg) (rb:Reg)
    sub-int                      --> Ibinop (SubInt) (rt:Reg) (ra:Reg) (rb:Reg)
    mul-int                      --> Ibinop (MulInt) (rt:Reg) (ra:Reg) (rb:Reg)
    div-int                      --> Ibinop (DivInt) (rt:Reg) (ra:Reg) (rb:Reg)
    rem-int                      --> Ibinop (RemInt) (rt:Reg) (ra:Reg) (rb:Reg)
    and-int                      --> Ibinop (AndInt) (rt:Reg) (ra:Reg) (rb:Reg)
    or-int                       --> Ibinop (OrInt) (rt:Reg) (ra:Reg) (rb:Reg)
    xor-int                      --> Ibinop (XorInt) (rt:Reg) (ra:Reg) (rb:Reg)
    shl-int                      --> Ibinop (ShlInt) (rt:Reg) (ra:Reg) (rb:Reg)
    shr-int                      --> Ibinop (ShrInt) (rt:Reg) (ra:Reg) (rb:Reg)
    ushr-int                     --> Ibinop (UshrInt) (rt:Reg) (ra:Reg) (rb:Reg)
    add-long                     --> long not supported
    sub-long                     --> long not supported
    mul-long                     --> long not supported
    div-long                     --> long not supported
    rem-long                     --> long not supported
    and-long                     --> long not supported
    or-long                      --> long not supported
    xor-long                     --> long not supported
    shl-long                     --> long not supported
    shr-long                     --> long not supported
    ushr-long                    --> long not supported
    add-float                    --> float not supported
    sub-float                    --> float not supported
    mul-float                    --> float not supported
    div-float                    --> float not supported
    rem-float                    --> float not supported    
    add-double                   --> double not supported
    sub-double                   --> double not supported
    mul-double                   --> double not supported
    div-double                   --> double not supported
    rem-double                   --> double not supported
  binop/2addr vA, vB
    add-int/2addr                --> Ibinop (AddInt) (ra:Reg) (ra:Reg) (rb:Reg)
    sub-int/2addr                --> Ibinop (SubInt) (ra:Reg) (ra:Reg) (rb:Reg)
    mul-int/2addr                --> Ibinop (MulInt) (ra:Reg) (ra:Reg) (rb:Reg)
    div-int/2addr                --> Ibinop (DivInt) (ra:Reg) (ra:Reg) (rb:Reg)
    rem-int/2addr                --> Ibinop (RemInt) (ra:Reg) (ra:Reg) (rb:Reg)
    and-int/2addr                --> Ibinop (AndInt) (ra:Reg) (ra:Reg) (rb:Reg)
    or-int/2addr                 --> Ibinop (OrInt) (ra:Reg) (ra:Reg) (rb:Reg)
    xor-int/2addr                --> Ibinop (XorInt) (ra:Reg) (ra:Reg) (rb:Reg)
    shl-int/2addr                --> Ibinop (ShlInt) (ra:Reg) (ra:Reg) (rb:Reg)
    shr-int/2addr                --> Ibinop (ShrInt) (ra:Reg) (ra:Reg) (rb:Reg)
    ushr-int/2addr               --> Ibinop (UshrInt) (ra:Reg) (ra:Reg) (rb:Reg)
    add-long/2addr               --> long not supported
    sub-long/2addr               --> long not supported
    mul-long/2addr               --> long not supported
    div-long/2addr               --> long not supported
    rem-long/2addr               --> long not supported
    and-long/2addr               --> long not supported
    or-long/2addr                --> long not supported
    xor-long/2addr               --> long not supported
    shl-long/2addr               --> long not supported
    shr-long/2addr               --> long not supported
    ushr-long/2addr              --> long not supported
    add-float/2addr              --> float not supported
    sub-float/2addr              --> float not supported
    mul-float/2addr              --> float not supported
    div-float/2addr              --> float not supported
    rem-float/2addr              --> float not supported    
    add-double/2addr             --> double not supported
    sub-double/2addr             --> double not supported
    mul-double/2addr             --> double not supported
    div-double/2addr             --> double not supported
    rem-double/2addr             --> double not supported
  binop/lit16 vA, vB, #+CCCC
    add-int/lit16                --> IbinopConst (AddInt) (rt:Reg) (rs:Reg) (z:Z)
    rsub-int (reverse subtract)  --> IbinopConst (SubInt) (rt:Reg) (rs:Reg) (z:Z)
    mul-int/lit16                --> IbinopConst (MulInt) (rt:Reg) (rs:Reg) (z:Z)
    div-int/lit16                --> IbinopConst (DivInt) (rt:Reg) (rs:Reg) (z:Z)
    rem-int/lit16                --> IbinopConst (RemInt) (rt:Reg) (rs:Reg) (z:Z)
    and-int/lit16                --> IbinopConst (AndInt) (rt:Reg) (rs:Reg) (z:Z)
    or-int/lit16                 --> IbinopConst (OrInt) (rt:Reg) (rs:Reg) (z:Z)
    xor-int/lit16                --> IbinopConst (XorInt) (rt:Reg) (rs:Reg) (z:Z)
  binop/lit8 vA, vB, #+CC        
    add-int/lit8                 --> IbinopConst (AddInt) (rt:Reg) (rs:Reg) (z:Z)
    rsub-int/lit8                --> IbinopConst (SubInt) (rt:Reg) (rs:Reg) (z:Z)
    mul-int/lit8                 --> IbinopConst (MulInt) (rt:Reg) (rs:Reg) (z:Z)
    div-int/lit8                 --> IbinopConst (DivInt) (rt:Reg) (rs:Reg) (z:Z)
    rem-int/lit8                 --> IbinopConst (RemInt) (rt:Reg) (rs:Reg) (z:Z)
    and-int/lit8                 --> IbinopConst (AndInt) (rt:Reg) (rs:Reg) (z:Z)
    or-int/lit8                  --> IbinopConst (OrInt) (rt:Reg) (rs:Reg) (z:Z)
    xor-int/lit8                 --> IbinopConst (XorInt) (rt:Reg) (rs:Reg) (z:Z)
    shl-int/lit8                 --> IbinopConst (ShlInt) (rt:Reg) (rs:Reg) (z:Z)
    shr-int/lit8                 --> IbinopConst (ShrInt) (rt:Reg) (rs:Reg) (z:Z)
    ushr-int/lit8                --> IbinopConst (UshrInt) (rt:Reg) (rs:Reg) (z:Z)
   *)


  Inductive Instruction : Set :=
   | Nop
   | Move (k:ValKind) (rt:Var) (rs:Var)
   | MoveResult (k:ValKind) (rt:Var)
   | Return
   | VReturn (k:ValKind) (rt:Var)
   | Const (k:ValKind) (rt:Var) (v:Z)
   | InstanceOf (rt:Var) (r:Var) (t:refType)
   | ArrayLength (rt:Var) (rs:Var)
   | New (rt:Var) (t:refType)
   | NewArray (rt:Var) (rl:Var) (t:type)
   | Goto (o:OFFSET.t)
   | PackedSwitch (rt:Var) (firstKey:Z) (size:Z) (l:list OFFSET.t)
   | SparseSwitch (rt:Var) (size:Z) (l:list (Z * OFFSET.t))
   | If (cmp:CompInt) (ra:Var) (rb:Var) (o:OFFSET.t)
   | Ifz (cmp:CompInt) (r:Var) (o:OFFSET.t)
   | Aget (k:ArrayKind) (rt:Var) (ra:Var) (ri:Var)
   | Aput (k:ArrayKind) (rs:Var) (ra:Var) (ri:Var)
   | Iget (k:ValKind) (rt:Var) (ro:Var) (f:FieldSignature)
   | Iput (k:ValKind) (rs:Var) (ro:Var) (f:FieldSignature)
(*   | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
   | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)
   | Invokevirtual (m:MethodSignature) (n:Z) (p:list Var)
   | Invokesuper (m:MethodSignature) (n:Z) (p:list Var)
   | Invokedirect (m:MethodSignature) (n:Z) (p:list Var)
   | Invokestatic (m:MethodSignature) (n:Z) (p:list Var)
   | Invokeinterface (m:MethodSignature) (n:Z) (p:list Var)
   | Ineg (rt:Var) (rs:Var)
   | Inot (rt:Var) (rs:Var)
   | I2b (rt:Var) (rs:Var)
   | I2s (rt:Var) (rs:Var)
   | Ibinop (op:BinopInt) (rt:Var) (ra:Var) (rb:Var)
   | IbinopConst (op:BinopInt) (rt:Var) (r:Var) (v:Z)
   .

  (** Operations on exception handlers *)
(*  Module Type EXCEPTIONHANDLER_TYPE.
  (** class of the caught exception *)
    (** The constructor [None] of type option being used to implement [finally]. It
    matches any exception *)
    Parameter catchType : ExceptionHandler -> option ClassName.
    (** is the given PC in range of the handler *)
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    (** location of the handler code *) 
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
  Declare Module EXCEPTIONHANDLER : EXCEPTIONHANDLER_TYPE.*)

  (** Operations on bytecode methods *)
  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    (* The list of exception is supposed to be ordered from the innermost to
       the outermost handler, otherwise the behavior might be unexpected 
       @see JVMS 3.10 *)
    (*Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.*)

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
(*  Definition javaLangThrowable : ClassName := (javaLang,throwable). *)

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

(*  Inductive handler_catch (p:Program) : ExceptionHandler -> PC -> ClassName -> Prop :=
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
*)

  (** Lookup in the given list of exception handlers if one of them catches
      the current exception *)
(*
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
