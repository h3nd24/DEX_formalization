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

Module Type DEX_PROGRAM.

  (** Main types to be manipulated by the API *)
  Parameter DEX_Program :Type.
  Parameter DEX_Class : Type.
  Parameter DEX_Interface : Type. (*- They are collapsed to class with a special access flag *)
  Parameter DEX_Reg : Set. (* In DEX, registers are indexed by natural number *)
  Parameter DEX_Field : Set.
  Parameter DEX_Method : Type.
  Parameter DEX_BytecodeMethod : Type.
  (*Parameter ExceptionHandler : Set.*)
  Parameter DEX_ShortMethodSignature : Set.
  Parameter DEX_ShortFieldSignature :Set.
  Parameter DEX_PC : Set.

 (** Variables are indexed by integers *)
  Parameter Reg_toN : DEX_Reg -> nat.
  Parameter N_toReg : nat -> DEX_Reg.
  Parameter Reg_toN_bij1 : forall v, N_toReg (Reg_toN v) = v.
  Parameter Reg_toN_bij2 : forall n, Reg_toN (N_toReg n) = n.


  (** Handling of qualified names *)
  Parameter DEX_PackageName : Set.
  Parameter DEX_ShortClassName : Set.
  Parameter DEX_ShortMethodName : Set.
  Parameter DEX_ShortFieldName : Set.

  (**For example the qualified name [java.lang.String] of the class [String],
      is decomposed into [java.lang] for the package name and [String] for the
       short name.  *)
  Definition DEX_ClassName := DEX_PackageName * DEX_ShortClassName.
  Definition DEX_InterfaceName := DEX_PackageName * DEX_ShortClassName.
  Definition DEX_MethodName := DEX_ClassName * DEX_ShortMethodName.
  Definition DEX_FieldName := DEX_ClassName * DEX_ShortFieldName.
  Definition DEX_MethodSignature := DEX_ClassName * DEX_ShortMethodSignature.
  Definition DEX_FieldSignature := DEX_ClassName * DEX_ShortFieldSignature.
  (** Some constants *)
  Parameter javaLang : DEX_PackageName.
  Parameter object : DEX_ShortClassName.
  (*Parameter throwable : ShortClassName.*)

  (** Native Exceptions *)
(*  Parameter NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName. *)

  (** visibility modifiers *)
  Inductive DEX_Visibility : Set :=
    Package | Protected | Private | Public.

  Inductive DEX_type : Set :=
      | DEX_ReferenceType (rt : DEX_refType)
      | DEX_PrimitiveType (pt: DEX_primitiveType)
  with DEX_refType :Set := 
      | DEX_ArrayType (typ:DEX_type) 
      | DEX_ClassType  (ct:DEX_ClassName)
      | DEX_InterfaceType (it:DEX_InterfaceName)
  with  DEX_primitiveType : Set := 
      | DEX_BOOLEAN  | DEX_BYTE | DEX_SHORT | DEX_INT.
      (* + Int64, Float,Double *)
      (* + ReturnAddressType subroutines *)

 
  Inductive DEX_CompInt : Set := 
    DEX_EqInt | DEX_NeInt | DEX_LtInt | DEX_LeInt | DEX_GtInt | DEX_GeInt.
  (* Inductive CompRef : Set := EqRef | NeRef. *)

  Inductive DEX_BinopInt : Set := 
    DEX_AddInt | DEX_AndInt | DEX_DivInt | DEX_MulInt | DEX_OrInt | DEX_RemInt 
  | DEX_ShlInt | DEX_ShrInt | DEX_SubInt | DEX_UshrInt | DEX_XorInt.

  (* Type information used for Vaload and Saload *)
  Inductive DEX_ArrayKind : Set :=
    | DEX_Aarray
    | DEX_Iarray
    | DEX_Barray
    | DEX_Sarray.
    
  (* Type information used for Vload, Vstore and Vreturn *)
  Inductive DEX_ValKind : Set :=
    | DEX_Aval
    | DEX_Ival.


  Module Type DEX_OFFSET_TYPE.
    (* The type of address offsets *)
    Parameter t : Set.
     (** Jumps are defined in terms of offsets with respect to the current address. **)
    Parameter jump : DEX_PC -> t -> DEX_PC.
  End DEX_OFFSET_TYPE.
  Declare Module DEX_OFFSET : DEX_OFFSET_TYPE.

  (** Operations on the signatures of fields *)
  Module Type DEX_FIELDSIGNATURE_TYPE.
    Parameter name : DEX_ShortFieldSignature -> DEX_ShortFieldName.
    Parameter type : DEX_ShortFieldSignature -> DEX_type.
    Parameter eq_dec : forall f1 f2:DEX_ShortFieldSignature, f1=f2 \/ ~f1=f2.
  End DEX_FIELDSIGNATURE_TYPE.
  Declare Module DEX_FIELDSIGNATURE : DEX_FIELDSIGNATURE_TYPE.

  (** Content of a method signature *)
  Module Type DEX_METHODSIGNATURE_TYPE.
    (* The method name *)
    Parameter name : DEX_ShortMethodSignature -> DEX_ShortMethodName.
    (** Java types for parameters values *)
    Parameter parameters : DEX_ShortMethodSignature -> list DEX_type.
    (** Java type for return value, the constructor [None] of type option being used for the [Void] type *)
    Parameter result : DEX_ShortMethodSignature -> option DEX_type.

    Parameter eq_dec : 
      forall mid1 mid2:DEX_ShortMethodSignature, mid1=mid2 \/ ~mid1=mid2.
  End DEX_METHODSIGNATURE_TYPE.
  Declare Module DEX_METHODSIGNATURE : DEX_METHODSIGNATURE_TYPE.

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


  Inductive DEX_Instruction : Set :=
   | DEX_Nop
   | DEX_Move (k:DEX_ValKind) (rt:DEX_Reg) (rs:DEX_Reg)
(* DEX Method
   | DEX_MoveResult (k:DEX_ValKind) (rt:DEX_Reg)
*)
   | DEX_Return
   | DEX_VReturn (k:DEX_ValKind) (rt:DEX_Reg)
   | DEX_Const (k:DEX_ValKind) (rt:DEX_Reg) (v:Z)
(* DEX Objects
   | DEX_InstanceOf (rt:DEX_Reg) (r:DEX_Reg) (t:DEX_refType)
   | DEX_ArrayLength (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_New (rt:DEX_Reg) (t:DEX_refType)
   | DEX_NewArray (rt:DEX_Reg) (rl:DEX_Reg) (t:DEX_type)
*)
   | DEX_Goto (o:DEX_OFFSET.t)
   | DEX_PackedSwitch (rt:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t)
   | DEX_SparseSwitch (rt:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t))
   | DEX_Ifcmp (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t)
   | DEX_Ifz (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t)
(* DEX Objects
   | DEX_Aget (k:DEX_ArrayKind) (rt:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg)
   | DEX_Aput (k:DEX_ArrayKind) (rs:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg)
   | DEX_Iget (k:DEX_ValKind) (rt:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature)
   | DEX_Iput (k:DEX_ValKind) (rs:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature)
*)
(*   | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
   | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)
(* DEX Method
   | DEX_Invokevirtual (m:DEX_MethodSignature) (n:Z) (p:list DEX_Reg)
   | DEX_Invokesuper (m:DEX_MethodSignature) (n:Z) (p:list DEX_Reg)
   | DEX_Invokedirect (m:DEX_MethodSignature) (n:Z) (p:list DEX_Reg)
   | DEX_Invokestatic (m:DEX_MethodSignature) (n:Z) (p:list DEX_Reg)
   | DEX_Invokeinterface (m:DEX_MethodSignature) (n:Z) (p:list DEX_Reg)
*)
   | DEX_Ineg (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_Inot (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_I2b (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_I2s (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_Ibinop (op:DEX_BinopInt) (rt:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg)
   | DEX_IbinopConst (op:DEX_BinopInt) (rt:DEX_Reg) (r:DEX_Reg) (v:Z)
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
  Module Type DEX_BYTECODEMETHOD_TYPE.
    Parameter firstAddress : DEX_BytecodeMethod -> DEX_PC.
    Parameter nextAddress : DEX_BytecodeMethod -> DEX_PC -> option DEX_PC.
    Parameter instructionAt : DEX_BytecodeMethod -> DEX_PC -> option DEX_Instruction.
    (* The list of exception is supposed to be ordered from the innermost to
       the outermost handler, otherwise the behavior might be unexpected 
       @see JVMS 3.10 *)
    (*Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.*)

    (** max number of local variables *)
    Parameter max_locals : DEX_BytecodeMethod -> nat.
    (** max number of elements on the operand stack *)
    Parameter max_operand_stack_size : DEX_BytecodeMethod -> nat.
    (* DEX for type system *)
    Parameter locR : DEX_BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:DEX_BytecodeMethod) (pc:DEX_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
   
  End DEX_BYTECODEMETHOD_TYPE.
  Declare Module DEX_BYTECODEMETHOD : DEX_BYTECODEMETHOD_TYPE.
 
  (** Content of a method *)
  Module Type DEX_METHOD_TYPE.

    Parameter signature : DEX_Method -> DEX_ShortMethodSignature.
    (** A method that is not abstract has an empty method body *)
    Parameter body : DEX_Method -> option DEX_BytecodeMethod.

    (* modifiers *)
    Parameter isFinal : DEX_Method -> bool.
    Parameter isStatic : DEX_Method -> bool.
    Parameter isNative : DEX_Method -> bool.
    Definition isAbstract (m : DEX_Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.

    Parameter visibility : DEX_Method -> DEX_Visibility.

    Definition valid_reg (m:DEX_Method) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm ->
         (Reg_toN x) <= (DEX_BYTECODEMETHOD.max_locals bm).
(*
    Definition valid_stack_size (m:Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         length <= (BYTECODEMETHOD.max_operand_stack_size bm).
*)

    (* DEX additional for locR *)
    Definition within_locR (m:DEX_Method) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm ->
         (Reg_toN x) <= (DEX_BYTECODEMETHOD.locR bm).

    End DEX_METHOD_TYPE.
  Declare Module DEX_METHOD : DEX_METHOD_TYPE.

  (** Operations on fields *)
  Module Type DEX_FIELD_TYPE.
    Parameter signature : DEX_Field -> DEX_ShortFieldSignature.    
    Parameter isFinal : DEX_Field -> bool.
    Parameter isStatic : DEX_Field -> bool.

    Parameter visibility : DEX_Field -> DEX_Visibility.

    Inductive value : Set :=
      | Int (v:Z) (* Numeric value *)
(*      | Lst (l:list Z)   Array of nums *)
      | NULL (* reference *)
      | UNDEF (* default value *).

    (** Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : DEX_Field ->  value.

  End DEX_FIELD_TYPE.
  Declare Module DEX_FIELD : DEX_FIELD_TYPE.

  (** Content of a Java class *)
  Module Type DEX_CLASS_TYPE.

    Parameter name : DEX_Class -> DEX_ClassName.
    (** direct superclass *)
    (** All the classes have a superClass except [java.lang.Object]. (see [Wf.v]) *)
    Parameter superClass : DEX_Class -> option DEX_ClassName.
    (** list of implemented interfaces *)
    Parameter superInterfaces : DEX_Class -> list DEX_InterfaceName.

    Parameter field : DEX_Class -> DEX_ShortFieldName -> option DEX_Field.

    Parameter definedFields : DEX_Class -> list DEX_Field.
    Parameter in_definedFields_field_some : forall c f,
      In f (definedFields c) ->
      field c (DEX_FIELDSIGNATURE.name (DEX_FIELD.signature f)) = Some f.
    Parameter field_some_in_definedFields : forall c f sfn,
      field c sfn = Some f -> In f (definedFields c).

    Parameter method : DEX_Class -> DEX_ShortMethodSignature -> option DEX_Method.
    Parameter method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = DEX_METHOD.signature m.
    
    Definition defined_Method (cl:DEX_Class) (m:DEX_Method) :=
      method cl (DEX_METHOD.signature m) = Some m.
    
    (* modifiers *)
    Parameter isFinal : DEX_Class -> bool.
    Parameter isPublic : DEX_Class -> bool.
    Parameter isAbstract : DEX_Class -> bool.

  End DEX_CLASS_TYPE.
  Declare Module DEX_CLASS : DEX_CLASS_TYPE.

  (** Content of a Java interface *)
  Module Type DEX_INTERFACE_TYPE.

    Parameter name : DEX_Interface -> DEX_InterfaceName. 

    Parameter superInterfaces : DEX_Interface -> list DEX_InterfaceName.

    Parameter field : DEX_Interface -> DEX_ShortFieldName -> option DEX_Field.

    Parameter method : DEX_Interface -> DEX_ShortMethodSignature -> option DEX_Method.

   (* modifiers *)
    Parameter isFinal : DEX_Interface -> bool.
    Parameter isPublic : DEX_Interface -> bool.
    Parameter isAbstract : DEX_Interface -> bool.
  End DEX_INTERFACE_TYPE.
  Declare Module DEX_INTERFACE : DEX_INTERFACE_TYPE.

  (** Content of a Java Program *)
  Module Type DEX_PROG_TYPE.
    (** accessor to a class from its qualified name *)
    Parameter class : DEX_Program -> DEX_ClassName -> option DEX_Class.
    Definition defined_Class (p:DEX_Program) (cl:DEX_Class) :=
      class p (DEX_CLASS.name cl) = Some cl.

    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = DEX_CLASS.name cl.

    (** accessor to an interface from its qualified name *)
    Parameter interface : DEX_Program -> DEX_InterfaceName -> option DEX_Interface.
    Definition defined_Interface (p:DEX_Program) (i:DEX_Interface) :=
      interface p (DEX_INTERFACE.name i) = Some i.

    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = DEX_INTERFACE.name cl.

  End DEX_PROG_TYPE.
  Declare Module DEX_PROG : DEX_PROG_TYPE.

(**  
      Definitions on programs 
 
  *)


  Inductive isStatic (p:DEX_Program) (fs: DEX_FieldSignature) : Prop :=
    isStatic_field : forall (cn:DEX_ClassName) (cl:DEX_Class) (f:DEX_Field),
     DEX_PROG.class p (fst fs) = Some cl ->
     DEX_CLASS.field cl (DEX_FIELDSIGNATURE.name (snd fs)) = Some f ->
     DEX_FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : DEX_ClassName := (javaLang,object).
(*  Definition javaLangThrowable : ClassName := (javaLang,throwable). *)

  Inductive direct_subclass (p:DEX_Program) (c:DEX_Class) (s:DEX_Class) : Prop :=
    | direct_subclass1 : 
        DEX_PROG.defined_Class p c -> 
        DEX_PROG.defined_Class p s ->
        DEX_CLASS.superClass c = Some (DEX_CLASS.name s) -> 
        direct_subclass p c s.

  (** [subclass] is the reflexive transitive closure of the [direct_subclass] relation 
    (defined over the classes of the program) *)
  Definition subclass (p:DEX_Program) : DEX_Class -> DEX_Class -> Prop :=
    clos_refl_trans DEX_Class (direct_subclass p).

  Inductive subclass_name (p:DEX_Program) : DEX_ClassName -> DEX_ClassName -> Prop :=
    | subclass_name1 : forall c1 c2, 
       subclass p c1 c2 -> 
       subclass_name p (DEX_CLASS.name c1) (DEX_CLASS.name c2).

  Inductive direct_subclass_name (p:DEX_Program) : DEX_ClassName -> DEX_ClassName -> Prop :=
    | direct_subclass_name1 : forall c s,
       direct_subclass p c s ->
       direct_subclass_name p (DEX_CLASS.name c) (DEX_CLASS.name s).

  (** Similar definitions for interfaces *)
  Inductive direct_subinterface (p:DEX_Program) (c:DEX_Interface) (s:DEX_Interface) : Prop :=
    | direct_subinterface1 : 
      DEX_PROG.defined_Interface p c -> 
      DEX_PROG.defined_Interface p s ->
      In (DEX_INTERFACE.name s) (DEX_INTERFACE.superInterfaces c) -> 
      direct_subinterface p c s.

  (** [subinterface] is the reflexive transitive closure of the [direct_subinterface] 
      relation (defined over the interfaces of the program) *)
  Definition subinterface (p:DEX_Program) : DEX_Interface -> DEX_Interface -> Prop :=
    clos_refl_trans DEX_Interface (direct_subinterface p).

  Inductive subinterface_name (p:DEX_Program) : DEX_InterfaceName -> DEX_InterfaceName -> Prop :=
    | subinterface_name1 : forall c1 c2, 
       subinterface p c1 c2 -> 
       subinterface_name p (DEX_INTERFACE.name c1) (DEX_INTERFACE.name c2).

  Inductive direct_subinterface_name (p:DEX_Program) : DEX_InterfaceName -> DEX_InterfaceName -> Prop :=
    | direct_subinterface_name1 : forall c s,
       direct_subinterface p c s ->
       direct_subinterface_name p (DEX_INTERFACE.name c) (DEX_INTERFACE.name s).

  Inductive class_declares_field (p:DEX_Program) (cn:DEX_ClassName) (fd:DEX_ShortFieldSignature) : DEX_Field -> Prop :=
    | class_decl_field : forall cl f, 
      DEX_PROG.class p cn = Some cl -> 
      DEX_CLASS.field cl (DEX_FIELDSIGNATURE.name fd) = Some f -> 
      class_declares_field p cn fd f.

  Inductive interface_declares_field (p:DEX_Program) (cn:DEX_InterfaceName) (fd:DEX_ShortFieldSignature) : DEX_Field -> Prop :=
    | interface_decl_field : forall cl f, 
      DEX_PROG.interface p cn = Some cl -> 
      DEX_INTERFACE.field cl (DEX_FIELDSIGNATURE.name fd) = Some f -> 
      interface_declares_field p cn fd f.

  (** [defined_field p c fd] holds if the class [c] declares or inherits a field 
      of signature [fd] *)
  Inductive is_defined_field (p:DEX_Program) : DEX_ClassName -> DEX_FieldSignature -> DEX_Field -> Prop :=
    | def_class_field : forall cn fd cn' f,
        subclass_name p cn cn' -> 
        class_declares_field p cn' fd f -> 
        is_defined_field p cn (cn',fd) f
    | def_interface_field : forall cn fd cl i1 i' f, 
        DEX_PROG.class p cn = Some cl -> 
        In i1 (DEX_CLASS.superInterfaces cl) ->
        subinterface_name p i1 i' -> 
        interface_declares_field p i' fd f -> 
        is_defined_field p cn (i',fd) f.

  Definition defined_field (p:DEX_Program) (cn:DEX_ClassName) (fs:DEX_FieldSignature) : Prop :=
    exists f, is_defined_field p cn fs f.

  Definition findMethod (p:DEX_Program) (msig: DEX_MethodSignature) : option DEX_Method :=
    let (cn,smsig) := msig in
      match DEX_PROG.class p cn with
	| None => None
	| Some cl => DEX_CLASS.method cl smsig 
      end.

  Definition findField (p:DEX_Program) (fd: DEX_FieldSignature) : option DEX_Field :=
    let (cn,sfs) := fd in   
      match DEX_PROG.class p cn with
	| None => None
	| Some cl => DEX_CLASS.field cl (DEX_FIELDSIGNATURE.name sfs)
      end.
    

  Definition methodPackage (mname: DEX_MethodName) : DEX_PackageName :=  fst (fst mname).

  (* Relations [check_visibility,check_signature,overrides] are needed
  to define the method [lookup] algorithm **)

  Inductive check_visibility : DEX_Visibility -> DEX_PackageName -> DEX_PackageName ->  Prop :=
    | check_public :  forall p1 p2, check_visibility Public p1 p2
    | check_protected :forall p1 p2, check_visibility Protected p1 p2
    | check_package :forall p, check_visibility Package p p.
	  
  Inductive lookup_here (p:DEX_Program) : DEX_ClassName ->  DEX_ShortMethodSignature -> DEX_Method -> Prop :=
    | lookup_here_c : forall cn msig meth, 
       findMethod p (cn,msig) = Some meth -> 
       lookup_here p cn msig meth.


  Inductive lookup (p:DEX_Program) : DEX_ClassName -> DEX_ShortMethodSignature -> (DEX_ClassName*DEX_Method) -> Prop :=
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
  Definition next (m:DEX_Method) (pc:DEX_PC) : option DEX_PC :=
    match DEX_METHOD.body m with
      None => None
    | Some body => DEX_BYTECODEMETHOD.nextAddress body pc
    end.

  (** Get the instruction at the given pc *)
  Definition instructionAt (m:DEX_Method) (pc:DEX_PC) : option DEX_Instruction :=
    match DEX_METHOD.body m with
      None => None
    | Some body => DEX_BYTECODEMETHOD.instructionAt body pc
    end.

  Inductive implements (p:DEX_Program) : DEX_ClassName -> DEX_InterfaceName -> Prop :=
    | implements_def : forall i cl i', 
           DEX_PROG.defined_Interface p i -> 
           DEX_PROG.defined_Class p cl ->
           In (DEX_INTERFACE.name i) (DEX_CLASS.superInterfaces cl) ->
           subinterface_name p (DEX_INTERFACE.name i) i' ->
           implements p (DEX_CLASS.name cl) i'.

  (** [compat_refType source target] holds if a reference value of type [source] can be 
    assigned to a reference variable of type [target]. See 
    #<a href=http://java.sun.com/docs/books/vmspec/2nd-edition/html/Concepts.doc.html##19674>assignment conversion rules</a># *)

  Inductive compat_refType (p:DEX_Program) : DEX_refType -> DEX_refType -> Prop :=
   | compat_refType_class_class : forall clS clT,
       subclass_name p clS clT ->
       compat_refType p (DEX_ClassType clS) (DEX_ClassType clT)
   | compat_refType_class_interface : forall clS clT,
       implements p clS clT ->
       compat_refType p (DEX_ClassType clS) (DEX_ClassType clT)
   | compat_refType_interface_class : forall clS,
       DEX_PROG.defined_Interface p clS ->
       compat_refType p (DEX_ClassType (DEX_INTERFACE.name clS)) (DEX_ClassType javaLangObject)
   | compat_refType_interface_interface : forall clS clT,
       DEX_PROG.defined_Interface p clS ->
       subinterface p clS clT ->
       compat_refType p (DEX_ClassType (DEX_INTERFACE.name clS)) (DEX_ClassType (DEX_INTERFACE.name clT))
   | compat_refType_array_class : forall tpS,       
       compat_refType p (DEX_ArrayType tpS) (DEX_ClassType javaLangObject)
   (* FIXME: array_interface : T must be either Cloneable or java.io.Serializable? - dp *)
   | compat_refType_array_array_primitive_type : forall t,       
       compat_refType p (DEX_ArrayType (DEX_PrimitiveType t)) (DEX_ArrayType (DEX_PrimitiveType t))
   | compat_refType_array_array_reference_type : forall tpS tpT,       
       compat_refType p tpS tpT ->
       compat_refType p (DEX_ArrayType (DEX_ReferenceType tpS)) (DEX_ArrayType (DEX_ReferenceType tpT)).


  (** Extra tools for implementation *)
  Parameter DEX_PC_eq : DEX_PC -> DEX_PC -> bool.
  Parameter DEX_PC_eq_spec : forall p q:DEX_PC, if DEX_PC_eq p q then p=q else p<>q.
  Parameter DEX_PC_eq_dec : forall pc1 pc2:DEX_PC, pc1=pc2 \/ ~pc1=pc2.
  
  Parameter Reg_eq_dec : forall x1 x2:DEX_Reg, x1=x2 \/ ~x1=x2. 
  Parameter ClassName_eq_dec : forall c1 c2:DEX_ClassName, c1=c2 \/ ~c1=c2.

End DEX_PROGRAM.
    
   
(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
