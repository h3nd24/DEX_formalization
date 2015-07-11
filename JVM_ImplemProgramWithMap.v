(** * Bicolano: Program syntax (interface implementation with maps) *)
(* Hendra : trim the system to contain only Arithmetic *)
Require Export JVM_Program.
Require Export ImplemSubClass.
Require Export Relation_Operators.
Require Export Lib.
Require ImplemSubClass.

Module MapP <: MAP with Definition key := positive := BinMap.
Module MapN <: MAP with Definition key := N := BinNatMap.

Module JVM_Make <: JVM_PROGRAM.

  Definition eq_dec (A:Set) := forall x y:A, x=y \/~x=y.

  Definition JVM_Var := N. 
  Definition Var_eq := Neq. 
  
  Lemma Var_eq_dec : eq_dec JVM_Var.
  Proof.
   intros x1 x2;assert (UU:= Neq_spec x1 x2);destruct (Neq x1 x2);auto.
  Qed.

  Definition Var_toN : JVM_Var -> nat := nat_of_N.
  Definition N_toVar : nat -> JVM_Var := N_of_nat.
  Lemma Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Proof. exact nat_of_N_bij2. Qed.
  Lemma Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.
  Proof. exact nat_of_N_bij1. Qed.

  Definition JVM_PC : Set := N.
  Definition JVM_PC_eq := Neq. 
  Definition JVM_PC_eq_spec := Neq_spec.
  Lemma JVM_PC_eq_dec : eq_dec JVM_PC.
  Proof. exact Var_eq_dec. Qed.

  Definition JVM_PackageName : Set := positive.
  Definition JVM_ShortClassName : Set := positive.
  Definition JVM_ShortMethodName : Set := positive.
  Definition JVM_ShortFieldName : Set := positive.
  Definition JVM_ClassName := JVM_PackageName * JVM_ShortClassName.
  Definition JVM_InterfaceName := JVM_PackageName * JVM_ShortClassName.
  Definition JVM_MethodName := JVM_ClassName * JVM_ShortMethodName.
  Definition JVM_FieldName := JVM_ClassName * JVM_ShortFieldName.


  Definition eqClassName : JVM_ClassName -> JVM_ClassName -> bool := prod_eq _ Peq _ Peq.
  Lemma eqClassName_spec : forall x y, if eqClassName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma ClassName_eq_dec : eq_dec JVM_ClassName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqInterfaceName : JVM_InterfaceName ->JVM_InterfaceName -> bool := 
      prod_eq _ Peq _ Peq.
  Lemma eqInterfaceName_spec : forall x y, if eqInterfaceName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma InterfaceName_eq_dec : eq_dec JVM_InterfaceName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqMethodName : JVM_MethodName -> JVM_MethodName -> bool := 
    prod_eq _ eqClassName _ Peq.
  Lemma eqMethodName_spec : forall x y, if eqMethodName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma MethodName_eq_dec : eq_dec JVM_MethodName.
  Proof. exact (Aeq_dec _ eqMethodName eqMethodName_spec). Qed.

  Definition eqFieldName : JVM_FieldName -> JVM_FieldName -> bool :=
     prod_eq _ eqClassName _ Peq.
  Lemma eqFieldName_spec : forall x y, if eqFieldName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma FieldName_eq_dec : eq_dec JVM_FieldName.
  Proof. exact (Aeq_dec _ eqFieldName eqFieldName_spec). Qed.

  Open Scope positive_scope.
  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang : JVM_PackageName := 1.
  Definition EmptyPackageName : JVM_PackageName := 2.
  Definition object : JVM_ShortClassName := 1.
(* DEX
  Definition NullPointerException : ShortClassName := 2.
  Definition ArrayIndexOutOfBoundsException : ShortClassName := 3.
  Definition ArrayStoreException : ShortClassName := 4.
  Definition NegativeArraySizeException : ShortClassName := 5.
  Definition ClassCastException : ShortClassName := 6.
  Definition ArithmeticException : ShortClassName := 7.
  Definition throwable : ShortClassName := 8.
*)
  Inductive JVM_Visibility : Set :=
    Package | Protected | Private | Public.

  Definition eqVisibility x y := 
    match x, y with 
    | Package, Package => true
    | Protected, Protected => true
    | Private, Private => true
    | Public, Public => true
    | _, _ => false
    end.
  Lemma eqVisibility_spec : forall x y, if eqVisibility x y then x = y else x <> y.
  Proof. destruct x;destruct y;simpl;trivial;intro; discriminate. Qed.
  Lemma Visibility_eq_dec : eq_dec JVM_Visibility.
  Proof. exact (Aeq_dec _ eqVisibility eqVisibility_spec). Qed.

  Inductive JVM_type : Set :=
      | JVM_ReferenceType (rt : JVM_refType)
      | JVM_PrimitiveType (pt: JVM_primitiveType)
  with JVM_refType :Set := 
      | JVM_ArrayType (typ:JVM_type) 
      | JVM_ClassType  (ct:JVM_ClassName)
      | JVM_InterfaceType (it:JVM_InterfaceName)
  with  JVM_primitiveType : Set := 
      | JVM_BOOLEAN  | JVM_BYTE | JVM_SHORT | JVM_INT.
 
  Scheme type_strong_rec := Induction for JVM_type Sort Set
    with refType_strong_rec := Induction for JVM_refType Sort Set.
  
  Scheme type_strong_ind := Induction for JVM_type Sort Prop
    with refType_strong_ind := Induction for JVM_refType Sort Prop.

  Definition eq_primitiveType x y :=
    match x, y with
    | JVM_BOOLEAN, JVM_BOOLEAN => true
    | JVM_BYTE, JVM_BYTE => true
    | JVM_SHORT, JVM_SHORT => true
    | JVM_INT, JVM_INT => true 
    | _, _ => false
    end.
  Lemma eq_primitiveType_spec : forall x y, if eq_primitiveType x y then x = y else x <> y.
  Proof.
   destruct x;destruct y;simpl;trivial; intro;discriminate.
  Qed.
  Lemma primitiveType_dec : eq_dec JVM_primitiveType.
  Proof.  exact (Aeq_dec _ eq_primitiveType eq_primitiveType_spec). Qed.

  Fixpoint eq_type (t1 t2:JVM_type) {struct t1} : bool := 
    match t1, t2 with 
    | JVM_ReferenceType rt1, JVM_ReferenceType rt2 => eq_reftype rt1 rt2
    | JVM_PrimitiveType pt1, JVM_PrimitiveType pt2 => eq_primitiveType pt1 pt2
    | _, _ => false
    end
  with eq_reftype (rt1 rt2: JVM_refType) {struct rt1} : bool := 
    match rt1, rt2 with
    | JVM_ArrayType t1, JVM_ArrayType t2 => eq_type t1 t2
    | JVM_ClassType cn1, JVM_ClassType cn2 => eqClassName cn1 cn2
    | JVM_InterfaceType in1, JVM_InterfaceType in2 => eqInterfaceName in1 in2
    |_, _ => false
    end.

  Lemma eq_type_spec : forall t1 t2, if eq_type t1 t2 then t1 = t2 else t1 <> t2.
  Proof.
   induction t1 using type_strong_ind with 
        (P0:=
          fun rt1 => forall rt2, if eq_reftype rt1 rt2 then rt1 = rt2 else rt1 <> rt2);intros.
   destruct t2;simpl;try (intro;discriminate;fail).
   assert (UU:=IHt1 rt0);destruct (eq_reftype rt rt0);subst;trivial.
   intro H;injection H;auto.
   destruct t2;simpl;try (intro;discriminate;fail).
   assert (UU := eq_primitiveType_spec pt pt0);destruct (eq_primitiveType pt pt0);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;try (intro H;discriminate H).
   assert (UU:=IHt1 typ);destruct (eq_type t1 typ);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqClassName_spec ct ct0);destruct (eqClassName ct ct0);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqInterfaceName_spec it it0);destruct (eqInterfaceName it it0);subst;trivial.
   intro H;injection H;auto.
  Qed.
  Lemma type_dec : eq_dec JVM_type.
  Proof. exact (Aeq_dec _ eq_type eq_type_spec). Qed.

  Inductive JVM_CompInt : Set := 
    JVM_EqInt | JVM_NeInt | JVM_LtInt | JVM_LeInt | JVM_GtInt | JVM_GeInt.
  Inductive JVM_CompRef : Set := JVM_EqRef | JVM_NeRef.

  Inductive JVM_BinopInt : Set := 
    JVM_AddInt | JVM_AndInt | JVM_DivInt | JVM_MulInt | JVM_OrInt | JVM_RemInt 
  | JVM_ShlInt | JVM_ShrInt | JVM_SubInt | JVM_UshrInt | JVM_XorInt.

  Module Type JVM_OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : JVM_PC -> t -> JVM_PC.
  End JVM_OFFSET_TYPE.
  Module JVM_OFFSET <: JVM_OFFSET_TYPE.
    Definition t := Z.
    Definition jump (pc:JVM_PC) (ofs:t) : JVM_PC := Zabs_N (Zplus (Z_of_N pc) ofs).
  End JVM_OFFSET.

  Module JVM_FIELDSIGNATURE.
    Record t :Set := {
      name : JVM_ShortFieldName;
      type : JVM_type
    }.
    Definition eq_t (x y : t) := 
         let (n1,t1) := x in
         let (n2,t2) := y in
         if Peq n1 n2 then eq_type t1 t2 else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof. 
      intros (n1,t1) (n2,t2);simpl;generalize (Peq_spec n1 n2);
       destruct (Peq n1 n2);intros.
      generalize (eq_type_spec t1 t2);destruct (eq_type t1 t2);intros;subst;trivial.
      intro H;injection H;auto.
      intro H1;injection H1;auto.
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
  End JVM_FIELDSIGNATURE.

  Definition JVM_ShortFieldSignature := JVM_FIELDSIGNATURE.t.
  Definition JVM_FieldSignature := (JVM_ClassName * JVM_FIELDSIGNATURE.t)%type.
  Module Type JVM_FIELDSIGNATURE_TYPE.
    Parameter name : JVM_ShortFieldSignature  -> JVM_ShortFieldName.
    Parameter type : JVM_ShortFieldSignature -> JVM_type.
    Parameter eq_dec : forall f1 f2:JVM_ShortFieldSignature,  f1=f2 \/ ~f1=f2.
  End JVM_FIELDSIGNATURE_TYPE.

  Module JVM_METHODSIGNATURE.
    Record t :Set := {
      name : JVM_ShortMethodName;
      parameters : list JVM_type;
      result : option JVM_type
    }.
    Definition eq_t (x y : t) :=
      let (n1,p1,r1) := x in
      let (n2,p2,r2) := y in
      if Peq n1 n2 then 
       if list_eq _ eq_type p1 p2 then opt_eq _ eq_type r1 r2 
       else false
      else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof.
      intros (n1,p1,r1) (n2,p2,r2);simpl;generalize (Peq_spec n1 n2);
       destruct (Peq n1 n2);intros.
      generalize (list_eq_spec _ eq_type eq_type_spec p1 p2);
       destruct (list_eq _ eq_type p1 p2);intros.
      generalize (opt_eq_spec _ eq_type eq_type_spec r1 r2);
       destruct (opt_eq _ eq_type r1 r2);intros. subst;trivial.
      intro UU;injection UU;auto.
      intro UU;injection UU;auto.
      intro H1;injection H1;auto.
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
  End JVM_METHODSIGNATURE.

  Definition JVM_ShortMethodSignature := JVM_METHODSIGNATURE.t.
  Definition JVM_MethodSignature := (JVM_ClassName*JVM_METHODSIGNATURE.t)%type.

  Module Type JVM_METHODSIGNATURE_TYPE.
    Parameter name : JVM_ShortMethodSignature -> JVM_ShortMethodName.
    Parameter parameters : JVM_ShortMethodSignature -> list JVM_type.
    Parameter result : JVM_ShortMethodSignature -> option JVM_type.
    Parameter eq_dec : forall mid1 mid2:JVM_ShortMethodSignature, mid1=mid2 \/~mid1=mid2.
  End JVM_METHODSIGNATURE_TYPE.

  
  Inductive JVM_ArrayKind : Set :=
    | JVM_Aarray
    | JVM_Iarray
    | JVM_Barray
    | JVM_Sarray.
    
  Inductive JVM_ValKind : Set :=
    | JVM_Aval
    | JVM_Ival.

  Inductive JVM_Instruction : Set :=
(* DEX
   | JVM_Aconst_null
   | JVM_Arraylength
*) 
(*   | Athrow
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
(*   | Getstatic  (f:FieldSignature) *)
   | JVM_Goto (o:JVM_OFFSET.t)
   | JVM_I2b
   | JVM_I2s
   | JVM_Ibinop (op:JVM_BinopInt)
(* DEX
   | JVM_If_acmp (cmp:JVM_CompRef) (o:JVM_OFFSET.t)
*)
   | JVM_If_icmp (cmp:JVM_CompInt) (o:JVM_OFFSET.t) 
   | JVM_If0 (cmp:JVM_CompInt) (o:JVM_OFFSET.t)
(*
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
(*
   | JVM_New (c:JVM_ClassName)
   | JVM_Newarray (t:JVM_type)
*)
   | JVM_Nop
   | JVM_Pop
   | JVM_Pop2
(* DEX
   | JVM_Putfield (f:JVM_FieldSignature)
*)
(*   | Putstatic (f:FieldSignature) *)
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

  Module JVM_FIELD.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
    Definition eq_value x y := 
     match x, y with
     | Int z1, Int z2 => Zeq_bool z1 z2
     | NULL, NULL => true
     | UNDEF, UNDEF => true
     | _, _ => false
     end.
    Lemma eq_value_spec : forall x y, if eq_value x y then x = y else x <> y.
    Proof.
      destruct x;destruct y;intros;simpl;trivial;try (intro;discriminate;fail).
      generalize (Zeq_spec v v0);destruct (Zeq_bool v v0);intros. subst;trivial.
      intro H1;injection H1;auto.
    Qed.

    Record t : Set := {
      signature : JVM_ShortFieldSignature;
      isFinal : bool;
      isStatic : bool;
      visibility : JVM_Visibility;
      initValue : value
    }.

    Definition eq_t (x y:t) := 
       let (s1,f1,st1,v1,val1) := x in
       let (s2,f2,st2,v2,val2) := y in
       if JVM_FIELDSIGNATURE.eq_t s1 s2 then
        if bool_eq f1 f2 then 
         if bool_eq st1 st2 then
          if eqVisibility v1 v2 then eq_value val1 val2
          else false
        else false
      else false
     else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
    Proof with try (intro UU;injection UU;auto;fail).     
     intros (s1,f1,st1,v1,val1)(s2,f2,st2,v2,val2);simpl.
     generalize (JVM_FIELDSIGNATURE.eq_t_spec s1 s2);destruct (JVM_FIELDSIGNATURE.eq_t s1 s2);intros...
     generalize (bool_eq_spec f1 f2);destruct (bool_eq f1 f2);intros...
     generalize (bool_eq_spec st1 st2);destruct (bool_eq st1 st2);intros...
     generalize (eqVisibility_spec v1 v2);destruct (eqVisibility v1 v2);intros...
     generalize (eq_value_spec val1 val2);destruct (eq_value val1 val2);intros...
     subst;trivial. 
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
   
  End JVM_FIELD.

  Definition JVM_Field := JVM_FIELD.t.

  Module Type JVM_FIELD_TYPE.
    Parameter signature : JVM_Field -> JVM_ShortFieldSignature.    
    Parameter isFinal : JVM_Field -> bool.
    Parameter isStatic : JVM_Field -> bool.
    Parameter visibility : JVM_Field -> JVM_Visibility.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
    Parameter initValue : JVM_Field ->  value.
  End JVM_FIELD_TYPE.
(* DEX
  Module EXCEPTIONHANDLER.
    Record t : Set := {
      catchType : option ClassName;
      begin : PC;
      end_e : PC;
      handler : PC
    }.

   Definition eq_t (x y:t) :=
     let (c1,b1,e1,h1) := x in
     let (c2,b2,e2,h2) := y in
     if opt_eq _ eqClassName c1 c2 then
      if Neq b1 b2 then 
       if Neq e1 e2 then Neq h1 h2 
       else false
      else false
     else false.
    Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.    
    Proof with  try (intro UU;injection UU;auto;fail).     
      intros (c1,b1,e1,h1)(c2,b2,e2,h2);simpl.
      generalize (opt_eq_spec _ eqClassName eqClassName_spec c1 c2);
        destruct (opt_eq ClassName eqClassName c1 c2);intros ...
      generalize (Neq_spec b1 b2);destruct (Neq b1 b2);intros...
      generalize (Neq_spec e1 e2);destruct (Neq e1 e2);intros ...
      generalize (Neq_spec h1 h2);destruct (Neq h1 h2);intros ...
      subst;trivial.
     Qed.
    
    (* TODO : check correctness of isPCinRange *)
    Definition isPCinRange (ex:t) (i:PC) : bool :=
      let (_,b,e,_) := ex in
        match Ncompare b i with
        | Gt => false
        | _ => 
           match Ncompare i e with
           | Gt => false
           | _ => true
           end
        end.           
 
  End EXCEPTIONHANDLER.
  Definition ExceptionHandler := EXCEPTIONHANDLER.t.

  Module Type EXCEPTIONHANDLER_TYPE.
    Parameter catchType : ExceptionHandler -> option ClassName.
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
*)   
  Module JVM_BYTECODEMETHOD.
    Record t : Type := {
      firstAddress : JVM_PC;
      instr : MapN.t (JVM_Instruction*(option JVM_PC*list JVM_ClassName));
      (* DEX exceptionHandlers : list ExceptionHandler; *)
      max_locals : nat;
      max_operand_stack_size : nat
    }.
    
    Definition instructionAt (bm:t) (pc:JVM_PC) : option JVM_Instruction :=
      match  MapN.get _ bm.(instr) pc with
       |Some p => Some (fst p)
       |None => None
        end.

    Definition nextAddress (bm:t) (pc:JVM_PC) : option JVM_PC := 
       match MapN.get _ bm.(instr) pc with
       | Some p => fst (snd p)
       | None => None
       end.
    Definition DefinedInstruction (bm:t) (pc:JVM_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
(* DEX
    Definition throwableAt (bm:t) (pc:JVM_PC) : list JVM_ClassName := 
       match MapN.get _ bm.(instr) pc with
       | Some p => snd (snd p)
       | None => nil
       end.
*)   
  End JVM_BYTECODEMETHOD.
  Definition JVM_BytecodeMethod := JVM_BYTECODEMETHOD.t.

  Module Type JVM_BYTECODEMETHOD_TYPE.
    Parameter firstAddress : JVM_BytecodeMethod -> JVM_PC.
    Parameter nextAddress : JVM_BytecodeMethod -> JVM_PC -> option JVM_PC.
    Parameter instructionAt : JVM_BytecodeMethod -> JVM_PC -> option JVM_Instruction.
    (* DEX Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler. *)
    Parameter max_locals : JVM_BytecodeMethod -> nat.
    Parameter max_operand_stack_size : JVM_BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:JVM_BytecodeMethod) (pc:JVM_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

  End JVM_BYTECODEMETHOD_TYPE.

  Module JVM_FieldProj.
    Definition element:=JVM_Field.
    Definition key:=positive.
    Definition  proj (f:element) := f.(JVM_FIELD.signature).(JVM_FIELDSIGNATURE.name).
  End JVM_FieldProj.

  Module JVM_MapField := MapProj JVM_FieldProj.

 Module JVM_ShortMethodSignatureHash <: HASH_TYPE.
   Definition t : Set := JVM_ShortMethodSignature.
   Definition eq_t := JVM_METHODSIGNATURE.eq_t.
   Definition eq_t_spec := JVM_METHODSIGNATURE.eq_t_spec.
   Definition eq_dec :=  JVM_METHODSIGNATURE.eq_dec.
   Definition key := JVM_ShortMethodName.
   Definition hash := JVM_METHODSIGNATURE.name.
 End JVM_ShortMethodSignatureHash.
 
 Module JVM_MapMethSign_Base :=
    MapHash_Base JVM_ShortMethodSignatureHash MapP.

 Module JVM_MapShortMethSign <: MAP with Definition key := JVM_ShortMethodSignature :=
    Map_Of_MapBase JVM_MapMethSign_Base.

  Module JVM_METHOD.
    Record t : Type := {
      signature : JVM_ShortMethodSignature;
      body : option JVM_BytecodeMethod;
      isFinal : bool;
      isStatic : bool;
      isNative : bool;
      visibility : JVM_Visibility      
    }.
    
    Definition isAbstract (m : t) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_var (m:t) (x:JVM_Var) : Prop :=
      forall bm, body m = Some bm ->
         ((Var_toN x) <= (JVM_BYTECODEMETHOD.max_locals bm))%nat.
    Definition valid_stack_size (m:t) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         (length <= (JVM_BYTECODEMETHOD.max_operand_stack_size bm))%nat.
  End JVM_METHOD.
  
  Definition JVM_Method := JVM_METHOD.t.


  Module Type JVM_METHOD_TYPE.
    Parameter signature : JVM_Method -> JVM_ShortMethodSignature.
    Parameter body : JVM_Method -> option JVM_BytecodeMethod.
    Parameter isFinal : JVM_Method -> bool.
    Parameter isStatic : JVM_Method -> bool.
    Parameter isNative : JVM_Method -> bool.
    Parameter visibility : JVM_Method -> JVM_Visibility.
    Definition isAbstract (m : JVM_Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_var (m:JVM_Method) (x:JVM_Var) : Prop :=
      forall bm, body m = Some bm ->
         ((Var_toN x) <= (JVM_BYTECODEMETHOD.max_locals bm))%nat.

    Definition valid_stack_size (m:JVM_Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         (length <= (JVM_BYTECODEMETHOD.max_operand_stack_size bm))%nat.
  End JVM_METHOD_TYPE.

  Module JVM_CLASS .
    Record t : Type := {
      name : JVM_ClassName;
      superClass : option JVM_ClassName;
      superInterfaces : list JVM_InterfaceName;
      fields : JVM_MapField.t;
      methods : JVM_MapShortMethSign.t JVM_Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.

    Definition field (c:t) (f:JVM_ShortFieldName):option JVM_Field := JVM_MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = JVM_FIELDSIGNATURE.name (JVM_FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= JVM_MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

  Definition definedFields (c:JVM_CLASS.t) : list JVM_FIELD.t := 
    JVM_MapField.elements (JVM_CLASS.fields c).
  Lemma in_definedFields_field_some : forall (c:JVM_CLASS.t) (f:JVM_FIELD.t),
    In f (definedFields c) ->
    JVM_CLASS.field c (JVM_FIELDSIGNATURE.name (JVM_FIELD.signature f)) = Some f.
  Proof.
    intros c; apply (JVM_MapField.in_elements_get_some (JVM_CLASS.fields c)).
  Qed.
  Lemma field_some_in_definedFields : forall (c:JVM_CLASS.t) (f:JVM_FIELD.t) (sfs:JVM_ShortFieldName),
    JVM_CLASS.field c sfs = Some f-> In f (definedFields c).
  Proof.
    unfold definedFields; intros.
    apply JVM_MapField.get_some_in_elements with sfs; auto.
  Qed.


    Definition method (c:t) (msig:JVM_ShortMethodSignature) : option JVM_Method :=
      match JVM_MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if JVM_METHODSIGNATURE.eq_t msig m.(JVM_METHOD.signature) then Some m
         else None
      | None => None
      end.
 

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = JVM_METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct JVM_MapShortMethSign.get;try (intros;discriminate).
      generalize (JVM_METHODSIGNATURE.eq_t_spec cl (JVM_METHOD.signature j));
      destruct (JVM_METHODSIGNATURE.eq_t cl (JVM_METHOD.signature j));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.
    Definition defined_Method (cl:t) (m:JVM_Method) :=
      method cl (JVM_METHOD.signature m) = Some m.
  End JVM_CLASS.

  Definition JVM_Class := JVM_CLASS.t.

  Module Type JVM_CLASS_TYPE.
    Parameter name : JVM_Class -> JVM_ClassName.
    Parameter superClass : JVM_Class -> option JVM_ClassName.
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
    Parameter isFinal : JVM_Class -> bool.
    Parameter isPublic : JVM_Class -> bool.
    Parameter isAbstract : JVM_Class -> bool.
    Definition defined_Method (cl:JVM_Class) (m:JVM_Method) :=
      method cl (JVM_METHOD.signature m) = Some m.
  End JVM_CLASS_TYPE.

  Module JVM_INTERFACE.
    Record t : Type := {
      name : JVM_InterfaceName;
      superInterfaces : list JVM_InterfaceName;
      fields : JVM_MapField.t;
      methods : JVM_MapShortMethSign.t JVM_Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.
 
    Definition field (c:t) (f:JVM_ShortFieldName):option JVM_Field := JVM_MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = JVM_FIELDSIGNATURE.name (JVM_FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= JVM_MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

    Definition method (c:t) (msig:JVM_ShortMethodSignature) : option JVM_Method :=
      match JVM_MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if JVM_METHODSIGNATURE.eq_t msig m.(JVM_METHOD.signature) then Some m
         else None
      | None => None
      end.

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = JVM_METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct JVM_MapShortMethSign.get;try (intros;discriminate).
      generalize (JVM_METHODSIGNATURE.eq_t_spec cl (JVM_METHOD.signature j));
      destruct (JVM_METHODSIGNATURE.eq_t cl (JVM_METHOD.signature j));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.

  End JVM_INTERFACE.
 
  Definition JVM_Interface := JVM_INTERFACE.t.

  Module Type JVM_INTERFACE_TYPE.
    Parameter name : JVM_Interface -> JVM_InterfaceName. 
    Parameter superInterfaces : JVM_Interface ->  list JVM_InterfaceName.
    Parameter field : JVM_Interface -> JVM_ShortFieldName -> option JVM_Field.
    Parameter method : JVM_Interface -> JVM_ShortMethodSignature -> option JVM_Method.
    Parameter isFinal : JVM_Interface -> bool.
    Parameter isPublic : JVM_Interface -> bool.
    Parameter isAbstract : JVM_Interface -> bool.
  End JVM_INTERFACE_TYPE.

  Module JVM_PROG.

    Module JVM_ClassNameProj.
      Definition element:=JVM_Class.
      Definition key1 := JVM_PackageName.
      Definition key2 :=JVM_ShortClassName.
      Definition proj := JVM_CLASS.name.
    End JVM_ClassNameProj.

   Module JVM_ClassNameProj1.
      Definition element:=JVM_Class.
      Definition key := JVM_PackageName.
      Definition proj := fun (x:element) => fst (JVM_ClassNameProj.proj x).
   End JVM_ClassNameProj1.

  Module JVM_MapClNameProj1 :=  MapProj JVM_ClassNameProj1.

  Module JVM_ClassNameProj2.
     Definition element := (JVM_ShortClassName * JVM_MapClNameProj1.t)%type.
     Definition key := JVM_ShortClassName.
     Definition proj := fun x:element => fst x. 
  End JVM_ClassNameProj2.

  Module JVM_MapClNameProj2 :=  MapProj JVM_ClassNameProj2.

  Module JVM_MapClass := MapProjPair JVM_ClassNameProj JVM_MapClNameProj1 JVM_MapClNameProj2.

 
  Module JVM_InterfaceNameProj.
      Definition element:=JVM_Interface.
      Definition key1 := JVM_PackageName.
      Definition key2 :=JVM_ShortClassName.
      Definition proj := JVM_INTERFACE.name.
    End JVM_InterfaceNameProj.

   Module JVM_InterfaceNameProj1.
      Definition element:=JVM_Interface.
      Definition key := JVM_PackageName.
      Definition proj := fun (x:element) => fst (JVM_InterfaceNameProj.proj x).
   End JVM_InterfaceNameProj1.

  Module JVM_MapInterfaceNameProj1 :=  MapProj JVM_InterfaceNameProj1.

  Module JVM_InterfaceNameProj2.
     Definition element := (JVM_ShortClassName * JVM_MapInterfaceNameProj1.t)%type.
     Definition key := JVM_ShortClassName.
     Definition proj := fun x:element => fst x. 
  End JVM_InterfaceNameProj2.

  Module JVM_MapInterfaceNameProj2 :=  MapProj JVM_InterfaceNameProj2.

  Module JVM_MapInterface := 
    MapProjPair JVM_InterfaceNameProj JVM_MapInterfaceNameProj1 JVM_MapInterfaceNameProj2.

  Record t : Type := {
    classes_map : JVM_MapClass.t;
    interfaces_map : JVM_MapInterface.t;
    throwableBy_map : JVM_MapShortMethSign.t (list JVM_ClassName)
    }.
(* DEX
  Definition throwableBy (p:t) (sms:JVM_ShortMethodSignature) : list JVM_ClassName :=
    match MapShortMethSign.get _ p.(throwableBy_map) sms with
      | Some l => l
      | None => nil
    end.
*)
    Definition classes p := JVM_MapClass.elements p.(classes_map).

    Definition class (p:t) (cn:JVM_ClassName) : option JVM_Class :=
      JVM_MapClass.get p.(classes_map) cn.

    Definition defined_Class (p:t) (cl:JVM_Class) :=
      class p (JVM_CLASS.name cl) = Some cl.

    Lemma name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = JVM_CLASS.name cl.
    Proof.
      unfold class; intros p cn cl H0.
      assert (UU:= JVM_MapClass.get_proj _ _ _ H0);subst;trivial.
    Qed.

    Lemma In_classes_defined_Class : forall p cl,
      distinct JVM_CLASS.name (classes p) ->
      In cl (classes p) -> defined_Class p cl.
    Proof.
      unfold defined_Class,class;intros.
      apply JVM_MapClass.in_elements_get_some;trivial.
    Qed.

    Lemma defined_Class_In_classes : forall p cl,
      defined_Class p cl -> In cl (classes p).
    Proof.
      unfold defined_Class, classes,class ; intros.     
      eapply JVM_MapClass.get_some_in_elements;eauto.
    Qed.

    Definition interfaces p := JVM_MapInterface.elements p.(interfaces_map).

    Definition interface (p:t) (i:JVM_InterfaceName): option JVM_Interface :=
      JVM_MapInterface.get p.(interfaces_map) i.
    Definition defined_Interface (p:t) (i:JVM_Interface) :=
      interface p (JVM_INTERFACE.name i) = Some i.
    Lemma name_interface_invariant1 : forall p iname i,
      interface p iname = Some i -> iname = JVM_INTERFACE.name i.
    Proof.
      unfold interface; intros p iname i H0.
      assert (UU:= JVM_MapInterface.get_proj _ _ _ H0);subst;trivial.
    Qed.
  End JVM_PROG.

  Definition JVM_Program := JVM_PROG.t.

  Module Type JVM_PROG_TYPE.
    Parameter class : JVM_Program -> JVM_ClassName -> option JVM_Class.
    Definition defined_Class (p:JVM_Program) (cl:JVM_Class) :=
      class p (JVM_CLASS.name cl) = Some cl.
    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = JVM_CLASS.name cl.
    Parameter interface : JVM_Program -> JVM_InterfaceName -> option JVM_Interface.
    Definition defined_Interface (p:JVM_Program) (i:JVM_Interface) :=
      interface p (JVM_INTERFACE.name i) = Some i.
    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = JVM_INTERFACE.name cl.
  End JVM_PROG_TYPE.

  Inductive isStatic (p:JVM_Program) (fs: JVM_FieldSignature) : Prop :=
    isStatic_field : forall (cn:JVM_ClassName) (cl:JVM_Class) (f:JVM_Field),
     JVM_PROG.class p (fst fs) = Some cl ->
     JVM_CLASS.field cl (JVM_FIELDSIGNATURE.name (snd fs)) = Some f ->
     JVM_FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : JVM_ClassName := (javaLang,object).
(* DEX  Definition javaLangThrowable : ClassName := (javaLang,throwable). *)

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

(*
  (** [check_signature] verifies that the two methods share the same signature and that the defining classes belong to the [subclass] relation. *)
  (* CAVEAT: the methods may not be defined in the program *)
  Inductive check_signature (p:Program) : MethodName*Method -> MethodName*Method -> Prop :=
    | check_signature_c : forall  mn1 meth1 mn2 meth2,
      subclass_name p (fst mn1) (fst mn2) ->
      snd mn1 = snd mn2 -> 
      METHODSIGNATURE.parameters (METHOD.signature meth1) =
        METHODSIGNATURE.parameters (METHOD.signature meth2) -> 
      METHODSIGNATURE.result (METHOD.signature meth1) =
        METHODSIGNATURE.result (METHOD.signature meth2) -> 
      check_signature p (mn1,meth1) (mn2,meth2).
      
  (* FIXME: lookup should deal with interfaces - fb *)

  (**  Definition of the #<a href=http://java.sun.com/docs/books/jls/third_edition/html/classes.html##8.4.8>  overrides relation </a># *)
  Inductive overrides (p:Program) : MethodName*Method -> MethodName*Method -> Prop :=
    | overrides_here : forall  mn1 meth1 mn2 meth2,
      check_signature p (mn1,meth1) (mn2,meth2) -> 
      check_visibility (METHOD.visibility meth2) (methodPackage mn1) (methodPackage mn2) ->
      overrides p (mn1,meth1) (mn2,meth2)
    | overrides_trans : forall  mn1 meth1 mn' meth' mn2 meth2,
	  (* In the spec, there is a side-condition which says that minter is different from msig1 and msig2 !?! *)
      check_signature p (mn1,meth1) (mn2,meth2) -> 
      overrides p (mn1,meth1) (mn',meth') -> overrides p (mn',meth') (mn2,meth2) -> 
      overrides p (mn1,meth1) (mn2,meth2).
*)	  
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
(* DEX
  Definition throwableAt (m:JVM_Method) (pc:JVM_PC) : list JVM_ClassName := 
    match JVM_METHOD.body m with
      None => nil
    | Some body => JVM_BYTECODEMETHOD.throwableAt body pc
    end.
*)

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

  (* subclass_test TO BE PROVED CORRECT ! *)  
  Module Map2P' := MapPair_Base BinMap_Base BinMap_Base.
  Module Map2P <: MAP with Definition key := (positive*positive)%type :=
      Map_Of_MapBase Map2P'.

  Definition subclass_test (p:JVM_Program):
         option (JVM_ClassName -> JVM_ClassName -> bool) :=
      @ImplemSubClass.subclass_test 
           JVM_ClassName JVM_CLASS.t 
           JVM_CLASS.name eqClassName JVM_CLASS.superClass
           Map2P.t Map2P.empty Map2P.update Map2P.get
           (JVM_PROG.classes p).

  Axiom subclass_test_prop : forall p test,
    subclass_test p = Some test ->
    forall c1 c2,
      if test c1 c2 then subclass_name p c1 c2
      else ~ subclass_name p c1 c2.

End JVM_Make.

Module JVM_P <: JVM_PROGRAM := JVM_Make.

Import JVM_P.

Definition JVM_bc_empty := MapN.empty (JVM_Instruction*(option JVM_PC * list JVM_ClassName)).

Definition JVM_bc_single pc i :=  
  MapN.update (JVM_Instruction*(option JVM_PC * list JVM_ClassName)) JVM_bc_empty pc (i,(None,nil)).

Definition JVM_bc_cons pc i pc' bc :=
  MapN.update (JVM_Instruction*(option JVM_PC * list JVM_ClassName)) bc pc (i,(Some pc',nil)).

Definition JVM_bc_cons' pc i pc' l bc :=
  MapN.update (JVM_Instruction*(option JVM_PC * list JVM_ClassName)) bc pc (i,(Some pc',l)).


(* creation function for method map *)

Definition JVM_ms_empty := JVM_MapShortMethSign.empty JVM_Method.

Definition JVM_ms_single ms := 
  JVM_MapShortMethSign.update JVM_Method JVM_ms_empty (JVM_METHOD.signature ms) ms.

Definition JVM_ms_cons ms mms := 
  JVM_MapShortMethSign.update JVM_Method mms (JVM_METHOD.signature ms) ms.


(* creation function for field map *)

Definition JVM_mf_empty := JVM_MapField.empty.

Definition JVM_mf_single mf := JVM_MapField.update JVM_mf_empty mf.

Definition JVM_mf_cons mf mmf := JVM_MapField.update mmf mf.


(* creation function for class map *)
 
Definition JVM_mc_empty := JVM_PROG.JVM_MapClass.empty.

Definition JVM_mc_cons c mc := JVM_PROG.JVM_MapClass.update mc c.

Definition JVM_mi_empty := JVM_PROG.JVM_MapInterface.empty.

Definition JVM_mi_cons c mc := JVM_PROG.JVM_MapInterface.update mc c.

Module JVM_MapClassName <: MAP with Definition key := JVM_ClassName := Map2P.

Definition eqFieldSignature := prod_eq _ eqClassName _ JVM_FIELDSIGNATURE.eq_t.
Lemma eqFieldSignature_spec : forall x y:JVM_FieldSignature, 
  if eqFieldSignature x y then x = y else x <> y.
Proof (prod_eq_spec _ _ eqClassName_spec _ _ JVM_FIELDSIGNATURE.eq_t_spec).

Module JVM_MapFieldSignature_hash <: HASH_TYPE.
  Definition t : Set := JVM_FieldSignature.
  Definition eq_t : t -> t -> bool := eqFieldSignature.
  Definition eq_t_spec : forall t1 t2, if eq_t t1 t2 then t1 = t2 else t1 <> t2 :=
    eqFieldSignature_spec.
  Definition eq_dec : forall x y:t, x=y \/ ~x=y := Aeq_dec _ _ eq_t_spec.
  Definition key : Set := (JVM_ShortClassName * JVM_ShortFieldName)%type.
  Definition hash : t -> key := fun x =>
    (snd (fst x), JVM_FIELDSIGNATURE.name (snd x)).
End JVM_MapFieldSignature_hash.

Module JVM_MapFieldSignature_base := MapHash_Base JVM_MapFieldSignature_hash Map2P'.
Module JVM_MapFieldSignature <: MAP with Definition key := JVM_FieldSignature :=
  Map_Of_MapBase JVM_MapFieldSignature_base.






