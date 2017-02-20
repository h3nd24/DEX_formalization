(** * Bicolano: Program syntax (interface implementation with maps) *)
(* Hendra : - Modified to suit DEX program. 
            - DEX has different instructions list from JVM.
            - Also trim the system to contain only Arithmetic *)

Require Export DEX_Program.
Require Export Relation_Operators.
Require Export Lib.

Module MapP <: MAP with Definition key := positive := BinMap.
Module MapN <: MAP with Definition key := N := BinNatMap.

Module DEX_Make <: DEX_PROGRAM.

  Definition eq_dec (A:Set) := forall x y:A, x=y \/~x=y.

  Definition DEX_Reg := N. 
  Definition Reg_eq := Neq. 
  
  Lemma Reg_eq_dec : eq_dec DEX_Reg.
  Proof.
   intros x1 x2;assert (UU:= Neq_spec x1 x2);destruct (Neq x1 x2);auto.
  Qed.

  Definition Reg_toN : DEX_Reg -> nat := nat_of_N.
  Definition N_toReg : nat -> DEX_Reg := N_of_nat.
  Lemma Reg_toN_bij1 : forall v, N_toReg (Reg_toN v) = v.
  Proof. exact nat_of_N_bij2. Qed.
  Lemma Reg_toN_bij2 : forall n, Reg_toN (N_toReg n) = n.
  Proof. exact nat_of_N_bij1. Qed. 

  Definition DEX_PC : Set := N.
  Definition DEX_PC_eq := Neq. 
  Definition DEX_PC_eq_spec := Neq_spec.
  Lemma DEX_PC_eq_dec : eq_dec DEX_PC.
  Proof. exact Reg_eq_dec. Qed.

  Definition DEX_PackageName : Set := positive.
  Definition DEX_ShortClassName : Set := positive.
  Definition DEX_ShortMethodName : Set := positive.
  Definition DEX_ShortFieldName : Set := positive.
  Definition DEX_ClassName := DEX_PackageName * DEX_ShortClassName.
  Definition DEX_InterfaceName := DEX_PackageName * DEX_ShortClassName.
  Definition DEX_MethodName := DEX_ClassName * DEX_ShortMethodName.
  Definition DEX_FieldName := DEX_ClassName * DEX_ShortFieldName.

  Definition eqClassName : DEX_ClassName -> DEX_ClassName -> bool := prod_eq _ Peq _ Peq.
  Lemma eqClassName_spec : forall x y, if eqClassName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma ClassName_eq_dec : eq_dec DEX_ClassName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqInterfaceName : DEX_InterfaceName ->DEX_InterfaceName -> bool := 
      prod_eq _ Peq _ Peq.
  Lemma eqInterfaceName_spec : forall x y, if eqInterfaceName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma InterfaceName_eq_dec : eq_dec DEX_InterfaceName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqMethodName : DEX_MethodName -> DEX_MethodName -> bool := 
    prod_eq _ eqClassName _ Peq.
  Lemma eqMethodName_spec : forall x y, if eqMethodName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma MethodName_eq_dec : eq_dec DEX_MethodName.
  Proof. exact (Aeq_dec _ eqMethodName eqMethodName_spec). Qed.

  Definition eqFieldName : DEX_FieldName -> DEX_FieldName -> bool :=
     prod_eq _ eqClassName _ Peq.
  Lemma eqFieldName_spec : forall x y, if eqFieldName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma FieldName_eq_dec : eq_dec DEX_FieldName.
  Proof. exact (Aeq_dec _ eqFieldName eqFieldName_spec). Qed.

  Open Scope positive_scope.
  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang : DEX_PackageName := 1.
  Definition EmptyPackageName : DEX_PackageName := 2.
  Definition object : DEX_ShortClassName := 1.

  Inductive DEX_Visibility : Set :=
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
  Lemma Visibility_eq_dec : eq_dec DEX_Visibility.
  Proof. exact (Aeq_dec _ eqVisibility eqVisibility_spec). Qed.

  Inductive DEX_type : Set :=
      | DEX_ReferenceType (rt : DEX_refType)
      | DEX_PrimitiveType (pt: DEX_primitiveType)
  with DEX_refType :Set := 
      | DEX_ClassType  (ct:DEX_ClassName)
      | DEX_InterfaceType (it:DEX_InterfaceName)
  with  DEX_primitiveType : Set := 
      | DEX_BOOLEAN  | DEX_BYTE | DEX_SHORT | DEX_INT.
 
(*  Scheme type_strong_rec := Induction for DEX_type Sort Set.
  Scheme type_strong_ind := Induction for DEX_type Sort Prop.*)

  Scheme type_strong_rec := Induction for DEX_type Sort Set
    with refType_strong_rec := Induction for DEX_refType Sort Set.
  
  Scheme type_strong_ind := Induction for DEX_type Sort Prop
    with refType_strong_ind := Induction for DEX_refType Sort Prop.

  Definition eq_primitiveType x y :=
    match x, y with
    | DEX_BOOLEAN, DEX_BOOLEAN => true
    | DEX_BYTE, DEX_BYTE => true
    | DEX_SHORT, DEX_SHORT => true
    | DEX_INT, DEX_INT => true 
    | _, _ => false
    end.
  Lemma eq_primitiveType_spec : forall x y, if eq_primitiveType x y then x = y else x <> y.
  Proof.
   destruct x;destruct y;simpl;trivial; intro;discriminate.
  Qed.
  Lemma primitiveType_dec : eq_dec DEX_primitiveType.
  Proof.  exact (Aeq_dec _ eq_primitiveType eq_primitiveType_spec). Qed.

  Fixpoint eq_type (t1 t2:DEX_type) {struct t1} : bool := 
    match t1, t2 with 
      | DEX_PrimitiveType pt1, DEX_PrimitiveType pt2 => eq_primitiveType pt1 pt2
      | DEX_ReferenceType rt1, DEX_ReferenceType rt2 => eq_reftype rt1 rt2
      | _, _ => false
    end
  with eq_reftype (rt1 rt2: DEX_refType) {struct rt1} : bool := 
    match rt1, rt2 with
    | DEX_ClassType cn1, DEX_ClassType cn2 => eqClassName cn1 cn2
    | DEX_InterfaceType in1, DEX_InterfaceType in2 => eqInterfaceName in1 in2
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
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqClassName_spec ct ct0);destruct (eqClassName ct ct0);subst;trivial.
   intro H;injection H;auto.
   destruct rt2;simpl;intros;try (intro;discriminate;fail).
   assert (UU := eqInterfaceName_spec it it0);destruct (eqInterfaceName it it0);subst;trivial.
   intro H;injection H;auto.
   (*assert (UU := eq_primitiveType_spec pt pt0).
   destruct eq_primitiveType. 
   subst; trivial.
   intro H. injection H. auto.*)
  Qed.
  Lemma type_dec : eq_dec DEX_type.
  Proof. exact (Aeq_dec _ eq_type eq_type_spec). Qed.

  Inductive DEX_CompInt : Set := 
    DEX_EqInt | DEX_NeInt | DEX_LtInt | DEX_LeInt | DEX_GtInt | DEX_GeInt.
  Inductive DEX_CompRef : Set := EqRef | NeRef.

  Inductive DEX_BinopInt : Set := 
    DEX_AddInt | DEX_AndInt | DEX_DivInt | DEX_MulInt | DEX_OrInt | DEX_RemInt 
  | DEX_ShlInt | DEX_ShrInt | DEX_SubInt | DEX_UshrInt | DEX_XorInt.

  Module Type DEX_OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : DEX_PC -> t -> DEX_PC.
  End DEX_OFFSET_TYPE.
  Module DEX_OFFSET <: DEX_OFFSET_TYPE.
    Definition t := Z.
    Definition jump (pc:DEX_PC) (ofs:t) : DEX_PC := Zabs_N (Zplus (Z_of_N pc) ofs).
  End DEX_OFFSET.

  Module DEX_FIELDSIGNATURE.
    Record t :Set := {
      name : DEX_ShortFieldName;
      type : DEX_type
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
  End DEX_FIELDSIGNATURE.

  Definition DEX_ShortFieldSignature := DEX_FIELDSIGNATURE.t.
  Definition DEX_FieldSignature := (DEX_ClassName * DEX_FIELDSIGNATURE.t)%type.
  Module Type DEX_FIELDSIGNATURE_TYPE.
    Parameter name : DEX_ShortFieldSignature  -> DEX_ShortFieldName.
    Parameter type : DEX_ShortFieldSignature -> DEX_type.
    Parameter eq_dec : forall f1 f2:DEX_ShortFieldSignature,  f1=f2 \/ ~f1=f2.
  End DEX_FIELDSIGNATURE_TYPE.

  Module DEX_METHODSIGNATURE.
    Record t :Set := {
      name : DEX_ShortMethodName;
      parameters : list DEX_type;
      result : option DEX_type
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
  End DEX_METHODSIGNATURE.

  Definition DEX_ShortMethodSignature := DEX_METHODSIGNATURE.t.
  Definition DEX_MethodSignature := (DEX_ClassName*DEX_METHODSIGNATURE.t)%type.

  Module Type DEX_METHODSIGNATURE_TYPE.
    Parameter name : DEX_ShortMethodSignature -> DEX_ShortMethodName.
    Parameter parameters : DEX_ShortMethodSignature -> list DEX_type.
    Parameter result : DEX_ShortMethodSignature -> option DEX_type.
    Parameter eq_dec : forall mid1 mid2:DEX_ShortMethodSignature, mid1=mid2 \/~mid1=mid2.
  End DEX_METHODSIGNATURE_TYPE.

  Inductive DEX_ValKind : Set :=
    (*| DEX_Aval*)
    | DEX_Ival.

  Inductive DEX_Instruction : Set :=
   | DEX_Nop
   | DEX_Move (k:DEX_ValKind) (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_Return
   | DEX_VReturn (k:DEX_ValKind) (rt:DEX_Reg)
   | DEX_Const (k:DEX_ValKind) (rt:DEX_Reg) (v:Z)
   | DEX_Goto (o:DEX_OFFSET.t)
   | DEX_PackedSwitch (rt:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t)
   | DEX_SparseSwitch (rt:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t))
   | DEX_Ifcmp (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t)
   | DEX_Ifz (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t)
   | DEX_Ineg (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_Inot (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_I2b (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_I2s (rt:DEX_Reg) (rs:DEX_Reg)
   | DEX_Ibinop (op:DEX_BinopInt) (rt:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg)
   | DEX_IbinopConst (op:DEX_BinopInt) (rt:DEX_Reg) (r:DEX_Reg) (v:Z)
   | DEX_Iget (t:DEX_type) (rt:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature)
   | DEX_Iput (t:DEX_type) (rs:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature)
   | DEX_New (rt:DEX_Reg) (c:DEX_ClassName)
   .

  Module DEX_FIELD.
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
      signature : DEX_ShortFieldSignature;
      isFinal : bool;
      isStatic : bool;
      visibility : DEX_Visibility;
      initValue : value
    }.

    Definition eq_t (x y:t) := 
       let (s1,f1,st1,v1,val1) := x in
       let (s2,f2,st2,v2,val2) := y in
       if DEX_FIELDSIGNATURE.eq_t s1 s2 then
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
     generalize (DEX_FIELDSIGNATURE.eq_t_spec s1 s2);destruct (DEX_FIELDSIGNATURE.eq_t s1 s2);intros...
     generalize (bool_eq_spec f1 f2);destruct (bool_eq f1 f2);intros...
     generalize (bool_eq_spec st1 st2);destruct (bool_eq st1 st2);intros...
     generalize (eqVisibility_spec v1 v2);destruct (eqVisibility v1 v2);intros...
     generalize (eq_value_spec val1 val2);destruct (eq_value val1 val2);intros...
     subst;trivial. 
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
   
  End DEX_FIELD.

  Definition DEX_Field := DEX_FIELD.t.

  Module Type DEX_FIELD_TYPE.
    Parameter signature : DEX_Field -> DEX_ShortFieldSignature.    
    Parameter isFinal : DEX_Field -> bool.
    Parameter isStatic : DEX_Field -> bool.
    Parameter visibility : DEX_Field -> DEX_Visibility.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
    Parameter initValue : DEX_Field ->  value.
  End DEX_FIELD_TYPE.
  
  Module DEX_BYTECODEMETHOD.
    Record t : Type := {
      firstAddress : DEX_PC;
      instr : MapN.t (DEX_Instruction*(option DEX_PC*list DEX_ClassName));
      max_locals : nat;
      max_operand_stack_size : nat;
      locR : list DEX_Reg;
      regs : list DEX_Reg;
      noDup_regs : NoDup regs
    }.

    Definition instructionAt (bm:t) (pc:DEX_PC) : option DEX_Instruction :=
      match  MapN.get _ bm.(instr) pc with
       |Some p => Some (fst p)
       |None => None
        end.

    Definition nextAddress (bm:t) (pc:DEX_PC) : option DEX_PC := 
       match MapN.get _ bm.(instr) pc with
       | Some p => fst (snd p)
       | None => None
       end.
    Definition DefinedInstruction (bm:t) (pc:DEX_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

  End DEX_BYTECODEMETHOD.
  Definition DEX_BytecodeMethod := DEX_BYTECODEMETHOD.t.

  Module Type DEX_BYTECODEMETHOD_TYPE.
    Parameter firstAddress : DEX_BytecodeMethod -> DEX_PC.
    Parameter nextAddress : DEX_BytecodeMethod -> DEX_PC -> option DEX_PC.
    Parameter instructionAt : DEX_BytecodeMethod -> DEX_PC -> option DEX_Instruction.
    Parameter max_locals : DEX_BytecodeMethod -> nat.
    Parameter max_operand_stack_size : DEX_BytecodeMethod -> nat.
    Parameter locR : DEX_BytecodeMethod -> list DEX_Reg.
    Parameter regs : DEX_BytecodeMethod -> list DEX_Reg.
    Parameter noDup_regs : forall bm, NoDup (regs (bm)).

    Definition DefinedInstruction (bm:DEX_BytecodeMethod) (pc:DEX_PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

  End DEX_BYTECODEMETHOD_TYPE.

  Module DEX_FieldProj.
    Definition element:=DEX_Field.
    Definition key:=positive.
    Definition  proj (f:element) := f.(DEX_FIELD.signature).(DEX_FIELDSIGNATURE.name).
  End DEX_FieldProj.

  Module DEX_MapField := MapProj DEX_FieldProj.

 Module DEX_ShortMethodSignatureHash <: HASH_TYPE.
   Definition t : Set := DEX_ShortMethodSignature.
   Definition eq_t := DEX_METHODSIGNATURE.eq_t.
   Definition eq_t_spec := DEX_METHODSIGNATURE.eq_t_spec.
   Definition eq_dec :=  DEX_METHODSIGNATURE.eq_dec.
   Definition key := DEX_ShortMethodName.
   Definition hash := DEX_METHODSIGNATURE.name.
 End DEX_ShortMethodSignatureHash.
 
 Module DEX_MapMethSign_Base :=
    MapHash_Base DEX_ShortMethodSignatureHash MapP.

 Module DEX_MapShortMethSign <: MAP with Definition key := DEX_ShortMethodSignature :=
    Map_Of_MapBase DEX_MapMethSign_Base.

  Module DEX_METHOD.
    Record t : Type := {
      signature : DEX_ShortMethodSignature;
      body : option DEX_BytecodeMethod;
      isFinal : bool;
      isStatic : bool;
      isNative : bool;
      visibility : DEX_Visibility      
    }.
    
    Definition isAbstract (m : t) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_reg (m:t) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm ->
         ((Reg_toN x) <= (DEX_BYTECODEMETHOD.max_locals bm))%nat.

    Definition within_locR (m:t) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm -> In x (DEX_BYTECODEMETHOD.locR bm).
  End DEX_METHOD.
  
  Definition DEX_Method := DEX_METHOD.t.


  Module Type DEX_METHOD_TYPE.
    Parameter signature : DEX_Method -> DEX_ShortMethodSignature.
    Parameter body : DEX_Method -> option DEX_BytecodeMethod.
    Parameter isFinal : DEX_Method -> bool.
    Parameter isStatic : DEX_Method -> bool.
    Parameter isNative : DEX_Method -> bool.
    Parameter visibility : DEX_Method -> DEX_Visibility.
    Definition isAbstract (m : DEX_Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_reg (m:DEX_Method) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm ->
         ((Reg_toN x) <= (DEX_BYTECODEMETHOD.max_locals bm))%nat.

    Definition within_locR (m:DEX_Method) (x:DEX_Reg) : Prop :=
      forall bm, body m = Some bm -> In x (DEX_BYTECODEMETHOD.locR bm).

  End DEX_METHOD_TYPE.

  Module DEX_CLASS .
    Record t : Type := {
      name : DEX_ClassName;
      superClass : option DEX_ClassName;
      superInterfaces : list DEX_InterfaceName;
      fields : DEX_MapField.t;
      methods : DEX_MapShortMethSign.t DEX_Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.

    Definition field (c:t) (f:DEX_ShortFieldName):option DEX_Field := DEX_MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = DEX_FIELDSIGNATURE.name (DEX_FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= DEX_MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

  Definition definedFields (c:DEX_CLASS.t) : list DEX_FIELD.t := 
    DEX_MapField.elements (DEX_CLASS.fields c).
  Lemma in_definedFields_field_some : forall (c:DEX_CLASS.t) (f:DEX_FIELD.t),
    In f (definedFields c) ->
    DEX_CLASS.field c (DEX_FIELDSIGNATURE.name (DEX_FIELD.signature f)) = Some f.
  Proof.
    intros c; apply (DEX_MapField.in_elements_get_some (DEX_CLASS.fields c)).
  Qed.
  Lemma field_some_in_definedFields : forall (c:DEX_CLASS.t) (f:DEX_FIELD.t) (sfs:DEX_ShortFieldName),
    DEX_CLASS.field c sfs = Some f-> In f (definedFields c).
  Proof.
    unfold definedFields; intros.
    apply DEX_MapField.get_some_in_elements with sfs; auto.
  Qed.


    Definition method (c:t) (msig:DEX_ShortMethodSignature) : option DEX_Method :=
      match DEX_MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if DEX_METHODSIGNATURE.eq_t msig m.(DEX_METHOD.signature) then Some m
         else None
      | None => None
      end.
 

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = DEX_METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct DEX_MapShortMethSign.get;try (intros;discriminate).
      generalize (DEX_METHODSIGNATURE.eq_t_spec cl (DEX_METHOD.signature d));
      destruct (DEX_METHODSIGNATURE.eq_t cl (DEX_METHOD.signature d));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.
    Definition defined_Method (cl:t) (m:DEX_Method) :=
      method cl (DEX_METHOD.signature m) = Some m.
  End DEX_CLASS.

  Definition DEX_Class := DEX_CLASS.t.

  Module Type DEX_CLASS_TYPE.
    Parameter name : DEX_Class -> DEX_ClassName.
    Parameter superClass : DEX_Class -> option DEX_ClassName.
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
    Parameter isFinal : DEX_Class -> bool.
    Parameter isPublic : DEX_Class -> bool.
    Parameter isAbstract : DEX_Class -> bool.
    Definition defined_Method (cl:DEX_Class) (m:DEX_Method) :=
      method cl (DEX_METHOD.signature m) = Some m.
  End DEX_CLASS_TYPE.

  Module DEX_INTERFACE.
    Record t : Type := {
      name : DEX_InterfaceName;
      superInterfaces : list DEX_InterfaceName;
      fields : DEX_MapField.t;
      methods : DEX_MapShortMethSign.t DEX_Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.
 
    Definition field (c:t) (f:DEX_ShortFieldName):option DEX_Field := DEX_MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = DEX_FIELDSIGNATURE.name (DEX_FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= DEX_MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

    Definition method (c:t) (msig:DEX_ShortMethodSignature) : option DEX_Method :=
      match DEX_MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if DEX_METHODSIGNATURE.eq_t msig m.(DEX_METHOD.signature) then Some m
         else None
      | None => None
      end.

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = DEX_METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct DEX_MapShortMethSign.get;try (intros;discriminate).
      generalize (DEX_METHODSIGNATURE.eq_t_spec cl (DEX_METHOD.signature d));
      destruct (DEX_METHODSIGNATURE.eq_t cl (DEX_METHOD.signature d));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.

  End DEX_INTERFACE.
 
  Definition DEX_Interface := DEX_INTERFACE.t.

  Module Type DEX_INTERFACE_TYPE.
    Parameter name : DEX_Interface -> DEX_InterfaceName. 
    Parameter superInterfaces : DEX_Interface ->  list DEX_InterfaceName.
    Parameter field : DEX_Interface -> DEX_ShortFieldName -> option DEX_Field.
    Parameter method : DEX_Interface -> DEX_ShortMethodSignature -> option DEX_Method.
    Parameter isFinal : DEX_Interface -> bool.
    Parameter isPublic : DEX_Interface -> bool.
    Parameter isAbstract : DEX_Interface -> bool.
  End DEX_INTERFACE_TYPE.

  Module DEX_PROG.

    Module DEX_ClassNameProj.
      Definition element:=DEX_Class.
      Definition key1 := DEX_PackageName.
      Definition key2 :=DEX_ShortClassName.
      Definition proj := DEX_CLASS.name.
    End DEX_ClassNameProj.

   Module DEX_ClassNameProj1.
      Definition element:=DEX_Class.
      Definition key := DEX_PackageName.
      Definition proj := fun (x:element) => fst (DEX_ClassNameProj.proj x).
   End DEX_ClassNameProj1.

  Module DEX_MapClNameProj1 :=  MapProj DEX_ClassNameProj1.

  Module DEX_ClassNameProj2.
     Definition element := (DEX_ShortClassName * DEX_MapClNameProj1.t)%type.
     Definition key := DEX_ShortClassName.
     Definition proj := fun x:element => fst x. 
  End DEX_ClassNameProj2.

  Module DEX_MapClNameProj2 :=  MapProj DEX_ClassNameProj2.

  Module DEX_MapClass := MapProjPair DEX_ClassNameProj DEX_MapClNameProj1 DEX_MapClNameProj2.

 
  Module DEX_InterfaceNameProj.
      Definition element:=DEX_Interface.
      Definition key1 := DEX_PackageName.
      Definition key2 :=DEX_ShortClassName.
      Definition proj := DEX_INTERFACE.name.
    End DEX_InterfaceNameProj.

   Module DEX_InterfaceNameProj1.
      Definition element:=DEX_Interface.
      Definition key := DEX_PackageName.
      Definition proj := fun (x:element) => fst (DEX_InterfaceNameProj.proj x).
   End DEX_InterfaceNameProj1.

  Module DEX_MapInterfaceNameProj1 :=  MapProj DEX_InterfaceNameProj1.

  Module DEX_InterfaceNameProj2.
     Definition element := (DEX_ShortClassName * DEX_MapInterfaceNameProj1.t)%type.
     Definition key := DEX_ShortClassName.
     Definition proj := fun x:element => fst x. 
  End DEX_InterfaceNameProj2.

  Module DEX_MapInterfaceNameProj2 :=  MapProj DEX_InterfaceNameProj2.

  Module DEX_MapInterface := 
    MapProjPair DEX_InterfaceNameProj DEX_MapInterfaceNameProj1 DEX_MapInterfaceNameProj2.

  Record t : Type := {
    classes_map : DEX_MapClass.t;
    interfaces_map : DEX_MapInterface.t
    }.

    Definition classes p := DEX_MapClass.elements p.(classes_map).

    Definition class (p:t) (cn:DEX_ClassName) : option DEX_Class :=
      DEX_MapClass.get p.(classes_map) cn.

    Definition defined_Class (p:t) (cl:DEX_Class) :=
      class p (DEX_CLASS.name cl) = Some cl.

    Lemma name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = DEX_CLASS.name cl.
    Proof.
      unfold class; intros p cn cl H0.
      assert (UU:= DEX_MapClass.get_proj _ _ _ H0);subst;trivial.
    Qed.

    Lemma In_classes_defined_Class : forall p cl,
      distinct DEX_CLASS.name (classes p) ->
      In cl (classes p) -> defined_Class p cl.
    Proof.
      unfold defined_Class,class;intros.
      apply DEX_MapClass.in_elements_get_some;trivial.
    Qed.

    Lemma defined_Class_In_classes : forall p cl,
      defined_Class p cl -> In cl (classes p).
    Proof.
      unfold defined_Class, classes,class ; intros.     
      eapply DEX_MapClass.get_some_in_elements;eauto.
    Qed.

    Definition interfaces p := DEX_MapInterface.elements p.(interfaces_map).

    Definition interface (p:t) (i:DEX_InterfaceName): option DEX_Interface :=
      DEX_MapInterface.get p.(interfaces_map) i.
    Definition defined_Interface (p:t) (i:DEX_Interface) :=
      interface p (DEX_INTERFACE.name i) = Some i.
    Lemma name_interface_invariant1 : forall p iname i,
      interface p iname = Some i -> iname = DEX_INTERFACE.name i.
    Proof.
      unfold interface; intros p iname i H0.
      assert (UU:= DEX_MapInterface.get_proj _ _ _ H0);subst;trivial.
    Qed.
  End DEX_PROG.

  Definition DEX_Program := DEX_PROG.t.

  Module Type DEX_PROG_TYPE.
    Parameter class : DEX_Program -> DEX_ClassName -> option DEX_Class.
    Definition defined_Class (p:DEX_Program) (cl:DEX_Class) :=
      class p (DEX_CLASS.name cl) = Some cl.
    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = DEX_CLASS.name cl.
    Parameter interface : DEX_Program -> DEX_InterfaceName -> option DEX_Interface.
    Definition defined_Interface (p:DEX_Program) (i:DEX_Interface) :=
      interface p (DEX_INTERFACE.name i) = Some i.
    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = DEX_INTERFACE.name cl.
  End DEX_PROG_TYPE.

  Inductive isStatic (p:DEX_Program) (fs: DEX_FieldSignature) : Prop :=
    isStatic_field : forall (cn:DEX_ClassName) (cl:DEX_Class) (f:DEX_Field),
     DEX_PROG.class p (fst fs) = Some cl ->
     DEX_CLASS.field cl (DEX_FIELDSIGNATURE.name (snd fs)) = Some f ->
     DEX_FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : DEX_ClassName := (javaLang,object).

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

  (* subclass_test TO BE PROVED CORRECT ! *)  
  Module Map2P' := MapPair_Base BinMap_Base BinMap_Base.
  Module Map2P <: MAP with Definition key := (positive*positive)%type :=
      Map_Of_MapBase Map2P'.

End DEX_Make.

Module P <: DEX_PROGRAM := DEX_Make.

Import P.

Definition DEX_bc_empty := MapN.empty (DEX_Instruction*(option DEX_PC * list DEX_ClassName)).

Definition DEX_bc_single pc i :=  
  MapN.update (DEX_Instruction*(option DEX_PC * list DEX_ClassName)) DEX_bc_empty pc (i,(None,nil)).

Definition DEX_bc_cons pc i pc' bc :=
  MapN.update (DEX_Instruction*(option DEX_PC * list DEX_ClassName)) bc pc (i,(Some pc',nil)).

Definition DEX_bc_cons' pc i pc' l bc :=
  MapN.update (DEX_Instruction*(option DEX_PC * list DEX_ClassName)) bc pc (i,(Some pc',l)).


(* creation function for method map *)

Definition DEX_ms_empty := DEX_MapShortMethSign.empty DEX_Method.

Definition DEX_ms_single ms := 
  DEX_MapShortMethSign.update DEX_Method DEX_ms_empty (DEX_METHOD.signature ms) ms.

Definition DEX_ms_cons ms mms := 
  DEX_MapShortMethSign.update DEX_Method mms (DEX_METHOD.signature ms) ms.


(* creation function for field map *)

Definition DEX_mf_empty := DEX_MapField.empty.

Definition DEX_mf_single mf := DEX_MapField.update DEX_mf_empty mf.

Definition DEX_mf_cons mf mmf := DEX_MapField.update mmf mf.


(* creation function for class map *)
 
Definition DEX_mc_empty := DEX_PROG.DEX_MapClass.empty.

Definition DEX_mc_cons c mc := DEX_PROG.DEX_MapClass.update mc c.

Definition DEX_mi_empty := DEX_PROG.DEX_MapInterface.empty.

Definition DEX_mi_cons c mc := DEX_PROG.DEX_MapInterface.update mc c.

Module DEX_MapClassName <: MAP with Definition key := DEX_ClassName := Map2P.

Definition eqFieldSignature := prod_eq _ eqClassName _ DEX_FIELDSIGNATURE.eq_t.
Lemma eqFieldSignature_spec : forall x y:DEX_FieldSignature, 
  if eqFieldSignature x y then x = y else x <> y.
Proof (prod_eq_spec _ _ eqClassName_spec _ _ DEX_FIELDSIGNATURE.eq_t_spec).

Module DEX_MapFieldSignature_hash <: HASH_TYPE.
  Definition t : Set := DEX_FieldSignature.
  Definition eq_t : t -> t -> bool := eqFieldSignature.
  Definition eq_t_spec : forall t1 t2, if eq_t t1 t2 then t1 = t2 else t1 <> t2 :=
    eqFieldSignature_spec.
  Definition eq_dec : forall x y:t, x=y \/ ~x=y := Aeq_dec _ _ eq_t_spec.
  Definition key : Set := (DEX_ShortClassName * DEX_ShortFieldName)%type.
  Definition hash : t -> key := fun x =>
    (snd (fst x), DEX_FIELDSIGNATURE.name (snd x)).
End DEX_MapFieldSignature_hash.

Module DEX_MapFieldSignature_base := MapHash_Base DEX_MapFieldSignature_hash Map2P'.
Module DEX_MapFieldSignature <: MAP with Definition key := DEX_FieldSignature :=
  Map_Of_MapBase DEX_MapFieldSignature_base.