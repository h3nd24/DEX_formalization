(** * Bicolano: Program syntax (interface implementation with maps) *)

Require Export Program.
Require Export ImplemSubClass.
Require Export Relation_Operators.
Require Export Lib.
Require ImplemSubClass.

Module MapP <: MAP with Definition key := positive := BinMap.
Module MapN <: MAP with Definition key := N := BinNatMap.

Module Make <: PROGRAM.

  Definition eq_dec (A:Set) := forall x y:A, x=y \/~x=y.

  Definition Var := N. 
  Definition Var_eq := Neq. 
  
  Lemma Var_eq_dec : eq_dec Var.
  Proof.
   intros x1 x2;assert (UU:= Neq_spec x1 x2);destruct (Neq x1 x2);auto.
  Qed.

  Definition Var_toN : Var -> nat := nat_of_N.
  Definition N_toVar : nat -> Var := N_of_nat.
  Lemma Var_toN_bij1 : forall v, N_toVar (Var_toN v) = v.
  Proof. exact nat_of_N_bij2. Qed.
  Lemma Var_toN_bij2 : forall n, Var_toN (N_toVar n) = n.
  Proof. exact nat_of_N_bij1. Qed. 

  Definition PC : Set := N.
  Definition PC_eq := Neq. 
  Definition PC_eq_spec := Neq_spec.
  Lemma PC_eq_dec : eq_dec PC.
  Proof. exact Var_eq_dec. 
    (*intros x1 x2;assert (UU:= Neq_spec x1 x2);destruct (Neq x1 x2);auto.*)
  Qed.

  Definition PackageName : Set := positive.
  Definition ShortClassName : Set := positive.
  Definition ShortMethodName : Set := positive.
  Definition ShortFieldName : Set := positive.
  Definition ClassName := PackageName * ShortClassName.
  Definition InterfaceName := PackageName * ShortClassName.
  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.


  Definition eqClassName : ClassName -> ClassName -> bool := prod_eq _ Peq _ Peq.
  Lemma eqClassName_spec : forall x y, if eqClassName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma ClassName_eq_dec : eq_dec ClassName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqInterfaceName : InterfaceName ->InterfaceName -> bool := 
      prod_eq _ Peq _ Peq.
  Lemma eqInterfaceName_spec : forall x y, if eqInterfaceName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ Peq Peq_spec _ Peq Peq_spec). Qed.
  Lemma InterfaceName_eq_dec : eq_dec InterfaceName.
  Proof. exact (Aeq_dec _ eqClassName eqClassName_spec). Qed.

  Definition eqMethodName : MethodName -> MethodName -> bool := 
    prod_eq _ eqClassName _ Peq.
  Lemma eqMethodName_spec : forall x y, if eqMethodName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma MethodName_eq_dec : eq_dec MethodName.
  Proof. exact (Aeq_dec _ eqMethodName eqMethodName_spec). Qed.

  Definition eqFieldName : FieldName -> FieldName -> bool :=
     prod_eq _ eqClassName _ Peq.
  Lemma eqFieldName_spec : forall x y, if eqFieldName x y then x = y else x <> y.
  Proof. exact (prod_eq_spec _ eqClassName eqClassName_spec _ Peq Peq_spec). Qed.
  Lemma FieldName_eq_dec : eq_dec FieldName.
  Proof. exact (Aeq_dec _ eqFieldName eqFieldName_spec). Qed.

  Open Scope positive_scope.
  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang : PackageName := 1.
  Definition EmptyPackageName : PackageName := 2.
  Definition object : ShortClassName := 1.
  Definition NullPointerException : ShortClassName := 2.
  Definition ArrayIndexOutOfBoundsException : ShortClassName := 3.
  Definition ArrayStoreException : ShortClassName := 4.
  Definition NegativeArraySizeException : ShortClassName := 5.
  Definition ClassCastException : ShortClassName := 6.
  Definition ArithmeticException : ShortClassName := 7.
  Definition throwable : ShortClassName := 8.

  Inductive Visibility : Set :=
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
  Lemma Visibility_eq_dec : eq_dec Visibility.
  Proof. exact (Aeq_dec _ eqVisibility eqVisibility_spec). Qed.

  Inductive type : Set :=
      | ReferenceType (rt : refType)
      | PrimitiveType (pt: primitiveType)
  with refType :Set := 
      | ArrayType (typ:type) 
      | ClassType  (ct:ClassName)
      | InterfaceType (it:InterfaceName)
  with  primitiveType : Set := 
      | BOOLEAN  | BYTE | SHORT | INT.
 
  Scheme type_strong_rec := Induction for type Sort Set
    with refType_strong_rec := Induction for refType Sort Set.
  
  Scheme type_strong_ind := Induction for type Sort Prop
    with refType_strong_ind := Induction for refType Sort Prop.

  Definition eq_primitiveType x y :=
    match x, y with
    | BOOLEAN, BOOLEAN => true
    | BYTE, BYTE => true
    | SHORT, SHORT => true
    | INT, INT => true 
    | _, _ => false
    end.
  Lemma eq_primitiveType_spec : forall x y, if eq_primitiveType x y then x = y else x <> y.
  Proof.
   destruct x;destruct y;simpl;trivial; intro;discriminate.
  Qed.
  Lemma primitiveType_dec : eq_dec primitiveType.
  Proof.  exact (Aeq_dec _ eq_primitiveType eq_primitiveType_spec). Qed.

  Fixpoint eq_type (t1 t2:type) {struct t1} : bool := 
    match t1, t2 with 
    | ReferenceType rt1, ReferenceType rt2 => eq_reftype rt1 rt2
    | PrimitiveType pt1, PrimitiveType pt2 => eq_primitiveType pt1 pt2
    | _, _ => false
    end
  with eq_reftype (rt1 rt2: refType) {struct rt1} : bool := 
    match rt1, rt2 with
    | ArrayType t1, ArrayType t2 => eq_type t1 t2
    | ClassType cn1, ClassType cn2 => eqClassName cn1 cn2
    | InterfaceType in1, InterfaceType in2 => eqInterfaceName in1 in2
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
  Lemma type_dec : eq_dec type.
  Proof. exact (Aeq_dec _ eq_type eq_type_spec). Qed.

  Inductive CompInt : Set := EqInt | NeInt | LtInt | LeInt | GtInt | GeInt.
  Inductive CompRef : Set := EqRef | NeRef.

  Inductive BinopInt : Set := AddInt | AndInt | DivInt | MulInt | OrInt | RemInt 
                            | ShlInt | ShrInt | SubInt | UshrInt | XorInt.

  Module Type OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Module OFFSET <: OFFSET_TYPE.
    Definition t := Z.
    Definition jump (pc:PC) (ofs:t) : PC := Zabs_N (Zplus (Z_of_N pc) ofs).
  End OFFSET.

  Module FIELDSIGNATURE.
    Record t :Set := {
      name : ShortFieldName;
      type : type
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
  End FIELDSIGNATURE.

  Definition ShortFieldSignature := FIELDSIGNATURE.t.
  Definition FieldSignature := (ClassName * FIELDSIGNATURE.t)%type.
  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : ShortFieldSignature  -> ShortFieldName.
    Parameter type : ShortFieldSignature -> type.
    Parameter eq_dec : forall f1 f2:ShortFieldSignature,  f1=f2 \/ ~f1=f2.
  End FIELDSIGNATURE_TYPE.

  Module METHODSIGNATURE.
    Record t :Set := {
      name : ShortMethodName;
      parameters : list type;
      result : option type
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
  End METHODSIGNATURE.

  Definition ShortMethodSignature := METHODSIGNATURE.t.
  Definition MethodSignature := (ClassName*METHODSIGNATURE.t)%type.

  Module Type METHODSIGNATURE_TYPE.
    Parameter name : ShortMethodSignature -> ShortMethodName.
    Parameter parameters : ShortMethodSignature -> list type.
    Parameter result : ShortMethodSignature -> option type.
    Parameter eq_dec : forall mid1 mid2:ShortMethodSignature, mid1=mid2 \/~mid1=mid2.
  End METHODSIGNATURE_TYPE.

  
  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  Inductive ValKind : Set :=
    | Aval
    | Ival.

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
(*   | Getstatic  (f:FieldSignature) *)
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
   | New (c:ClassName)
   | Newarray (t:type)
   | Nop
   | Pop
   | Pop2
   | Putfield (f:FieldSignature)
(*   | Putstatic (f:FieldSignature) *)
   | Return
   | Swap 
   | Tableswitch (def:OFFSET.t) (low high:Z) (l:list OFFSET.t)
   | Vaload (k:ArrayKind) 
   | Vastore (k:ArrayKind)
   | Vload (k:ValKind) (x:Var)
   | Vreturn (k:ValKind)
   | Vstore (k:ValKind) (x:Var).*)

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
   | Ifcmp (cmp:CompInt) (ra:Var) (rb:Var) (o:OFFSET.t)
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

  Module FIELD.
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
      signature : ShortFieldSignature;
      isFinal : bool;
      isStatic : bool;
      visibility : Visibility;
      initValue : value
    }.

    Definition eq_t (x y:t) := 
       let (s1,f1,st1,v1,val1) := x in
       let (s2,f2,st2,v2,val2) := y in
       if FIELDSIGNATURE.eq_t s1 s2 then
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
     generalize (FIELDSIGNATURE.eq_t_spec s1 s2);destruct (FIELDSIGNATURE.eq_t s1 s2);intros...
     generalize (bool_eq_spec f1 f2);destruct (bool_eq f1 f2);intros...
     generalize (bool_eq_spec st1 st2);destruct (bool_eq st1 st2);intros...
     generalize (eqVisibility_spec v1 v2);destruct (eqVisibility v1 v2);intros...
     generalize (eq_value_spec val1 val2);destruct (eq_value val1 val2);intros...
     subst;trivial. 
    Qed.
    Lemma eq_dec : eq_dec t.
    Proof. exact (Aeq_dec _ eq_t eq_t_spec). Qed.
   
  End FIELD.

  Definition Field := FIELD.t.

  Module Type FIELD_TYPE.
    Parameter signature : Field -> ShortFieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter isStatic : Field -> bool.
    Parameter visibility : Field -> Visibility.
    Inductive value : Set :=
    | Int (v:Z)
    | NULL 
    | UNDEF.
    Parameter initValue : Field ->  value.
  End FIELD_TYPE.
(*
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
  Module BYTECODEMETHOD.
    Record t : Type := {
      firstAddress : PC;
      instr : MapN.t (Instruction*(option PC*list ClassName));
      (*exceptionHandlers : list ExceptionHandler;*)
      max_locals : nat;
      max_operand_stack_size : nat;
      (* DEX type system locR *)
      locR : nat
    }.
    
    Definition instructionAt (bm:t) (pc:PC) : option Instruction :=
      match  MapN.get _ bm.(instr) pc with
       |Some p => Some (fst p)
       |None => None
        end.

    Definition nextAddress (bm:t) (pc:PC) : option PC := 
       match MapN.get _ bm.(instr) pc with
       | Some p => fst (snd p)
       | None => None
       end.
    Definition DefinedInstruction (bm:t) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.
(*
    Definition throwableAt (bm:t) (pc:PC) : list ClassName := 
       match MapN.get _ bm.(instr) pc with
       | Some p => snd (snd p)
       | None => nil
       end.
*)   
  End BYTECODEMETHOD.
  Definition BytecodeMethod := BYTECODEMETHOD.t.

  Module Type BYTECODEMETHOD_TYPE.
    Parameter firstAddress : BytecodeMethod -> PC.
    Parameter nextAddress : BytecodeMethod -> PC -> option PC.
    Parameter instructionAt : BytecodeMethod -> PC -> option Instruction.
    (*Parameter exceptionHandlers : BytecodeMethod -> list ExceptionHandler.*)
    Parameter max_locals : BytecodeMethod -> nat.
    Parameter max_operand_stack_size : BytecodeMethod -> nat.
    (* DEX type system locR *)
    Parameter locR : BytecodeMethod -> nat.

    Definition DefinedInstruction (bm:BytecodeMethod) (pc:PC) : Prop :=
      exists i, instructionAt bm pc = Some i.

  End BYTECODEMETHOD_TYPE.

  Module FieldProj.
    Definition element:=Field.
    Definition key:=positive.
    Definition  proj (f:element) := f.(FIELD.signature).(FIELDSIGNATURE.name).
  End FieldProj.

  Module MapField := MapProj FieldProj.

 Module ShortMethodSignatureHash <: HASH_TYPE.
   Definition t : Set := ShortMethodSignature.
   Definition eq_t := METHODSIGNATURE.eq_t.
   Definition eq_t_spec := METHODSIGNATURE.eq_t_spec.
   Definition eq_dec :=  METHODSIGNATURE.eq_dec.
   Definition key := ShortMethodName.
   Definition hash := METHODSIGNATURE.name.
 End ShortMethodSignatureHash.
 
 Module MapMethSign_Base :=
    MapHash_Base ShortMethodSignatureHash MapP.

 Module MapShortMethSign <: MAP with Definition key := ShortMethodSignature :=
    Map_Of_MapBase MapMethSign_Base.

  Module METHOD.
    Record t : Type := {
      signature : ShortMethodSignature;
      body : option BytecodeMethod;
      isFinal : bool;
      isStatic : bool;
      isNative : bool;
      visibility : Visibility      
    }.
    
    Definition isAbstract (m : t) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_var (m:t) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
         ((Var_toN x) <= (BYTECODEMETHOD.max_locals bm))%nat.
    Definition valid_stack_size (m:t) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         (length <= (BYTECODEMETHOD.max_operand_stack_size bm))%nat.

    (* DEX type system locR *)
    Definition within_locR (m:t) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
        ((Var_toN x) <= (BYTECODEMETHOD.locR bm))%nat.
  End METHOD.
  
  Definition Method := METHOD.t.


  Module Type METHOD_TYPE.
    Parameter signature : Method -> ShortMethodSignature.
    Parameter body : Method -> option BytecodeMethod.
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter isNative : Method -> bool.
    Parameter visibility : Method -> Visibility.
    Definition isAbstract (m : Method) : bool :=
      match body m with
        None => true
      | Some _ => false
    end.
    Definition valid_var (m:Method) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
         ((Var_toN x) <= (BYTECODEMETHOD.max_locals bm))%nat.

    Definition valid_stack_size (m:Method) (length:nat) : Prop :=
      forall bm, body m = Some bm ->
         (length <= (BYTECODEMETHOD.max_operand_stack_size bm))%nat.
    (* DEX type system locR *)
    Definition within_locR (m:Method) (x:Var) : Prop :=
      forall bm, body m = Some bm ->
        ((Var_toN x) <= (BYTECODEMETHOD.locR bm))%nat.

  End METHOD_TYPE.

  Module CLASS .
    Record t : Type := {
      name : ClassName;
      superClass : option ClassName;
      superInterfaces : list InterfaceName;
      fields : MapField.t;
      methods : MapShortMethSign.t Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.

    Definition field (c:t) (f:ShortFieldName):option Field := MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = FIELDSIGNATURE.name (FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

  Definition definedFields (c:CLASS.t) : list FIELD.t := 
    MapField.elements (CLASS.fields c).
  Lemma in_definedFields_field_some : forall (c:CLASS.t) (f:FIELD.t),
    In f (definedFields c) ->
    CLASS.field c (FIELDSIGNATURE.name (FIELD.signature f)) = Some f.
  Proof.
    intros c; apply (MapField.in_elements_get_some (CLASS.fields c)).
  Qed.
  Lemma field_some_in_definedFields : forall (c:CLASS.t) (f:FIELD.t) (sfs:ShortFieldName),
    CLASS.field c sfs = Some f-> In f (definedFields c).
  Proof.
    unfold definedFields; intros.
    apply MapField.get_some_in_elements with sfs; auto.
  Qed.


    Definition method (c:t) (msig:ShortMethodSignature) : option Method :=
      match MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if METHODSIGNATURE.eq_t msig m.(METHOD.signature) then Some m
         else None
      | None => None
      end.
 

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct MapShortMethSign.get;try (intros;discriminate).
      generalize (METHODSIGNATURE.eq_t_spec cl (METHOD.signature m));
      destruct (METHODSIGNATURE.eq_t cl (METHOD.signature m));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.
    Definition defined_Method (cl:t) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
  End CLASS.

  Definition Class := CLASS.t.

  Module Type CLASS_TYPE.
    Parameter name : Class -> ClassName.
    Parameter superClass : Class -> option ClassName.
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
    Parameter isFinal : Class -> bool.
    Parameter isPublic : Class -> bool.
    Parameter isAbstract : Class -> bool.
    Definition defined_Method (cl:Class) (m:Method) :=
      method cl (METHOD.signature m) = Some m.
  End CLASS_TYPE.

  Module INTERFACE.
    Record t : Type := {
      name : InterfaceName;
      superInterfaces : list InterfaceName;
      fields : MapField.t;
      methods : MapShortMethSign.t Method;
      isFinal : bool;
      isPublic : bool;
      isAbstract : bool
    }.
 
    Definition field (c:t) (f:ShortFieldName):option Field := MapField.get c.(fields) f.

    Lemma field_shortname_prop : forall cl s f,
      field cl s = Some f -> s = FIELDSIGNATURE.name (FIELD.signature f).
    Proof.
      unfold field;intros cl s f H.
      assert (UU:= MapField.get_proj _ _ _ H);subst;trivial.
    Qed.

    Definition method (c:t) (msig:ShortMethodSignature) : option Method :=
      match MapShortMethSign.get _ c.(methods) msig with
      | Some m => 
         if METHODSIGNATURE.eq_t msig m.(METHOD.signature) then Some m
         else None
      | None => None
      end.

    Lemma method_signature_prop : forall cl mid m,
      method cl mid = Some m -> mid = METHOD.signature m.
    Proof.
      unfold method; intros p cl mid.
      destruct MapShortMethSign.get;try (intros;discriminate).
      generalize (METHODSIGNATURE.eq_t_spec cl (METHOD.signature m));
      destruct (METHODSIGNATURE.eq_t cl (METHOD.signature m));intros.
      injection H0;intros;subst;trivial.
      discriminate.
    Qed.

  End INTERFACE.
 
  Definition Interface := INTERFACE.t.

  Module Type INTERFACE_TYPE.
    Parameter name : Interface -> InterfaceName. 
    Parameter superInterfaces : Interface ->  list InterfaceName.
    Parameter field : Interface -> ShortFieldName -> option Field.
    Parameter method : Interface -> ShortMethodSignature -> option Method.
    Parameter isFinal : Interface -> bool.
    Parameter isPublic : Interface -> bool.
    Parameter isAbstract : Interface -> bool.
  End INTERFACE_TYPE.

  Module PROG.

    Module ClassNameProj.
      Definition element:=Class.
      Definition key1 := PackageName.
      Definition key2 :=ShortClassName.
      Definition proj := CLASS.name.
    End ClassNameProj.

   Module ClassNameProj1.
      Definition element:=Class.
      Definition key := PackageName.
      Definition proj := fun (x:element) => fst (ClassNameProj.proj x).
   End ClassNameProj1.

  Module MapClNameProj1 :=  MapProj ClassNameProj1.

  Module ClassNameProj2.
     Definition element := (ShortClassName * MapClNameProj1.t)%type.
     Definition key := ShortClassName.
     Definition proj := fun x:element => fst x. 
  End ClassNameProj2.

  Module MapClNameProj2 :=  MapProj ClassNameProj2.

  Module MapClass := MapProjPair ClassNameProj MapClNameProj1 MapClNameProj2.

 
  Module InterfaceNameProj.
      Definition element:=Interface.
      Definition key1 := PackageName.
      Definition key2 :=ShortClassName.
      Definition proj := INTERFACE.name.
    End InterfaceNameProj.

   Module InterfaceNameProj1.
      Definition element:=Interface.
      Definition key := PackageName.
      Definition proj := fun (x:element) => fst (InterfaceNameProj.proj x).
   End InterfaceNameProj1.

  Module MapInterfaceNameProj1 :=  MapProj InterfaceNameProj1.

  Module InterfaceNameProj2.
     Definition element := (ShortClassName * MapInterfaceNameProj1.t)%type.
     Definition key := ShortClassName.
     Definition proj := fun x:element => fst x. 
  End InterfaceNameProj2.

  Module MapInterfaceNameProj2 :=  MapProj InterfaceNameProj2.

  Module MapInterface := 
    MapProjPair InterfaceNameProj MapInterfaceNameProj1 MapInterfaceNameProj2.

  Record t : Type := {
    classes_map : MapClass.t;
    interfaces_map : MapInterface.t;
    throwableBy_map : MapShortMethSign.t (list ClassName)
    }.

  Definition throwableBy (p:t) (sms:ShortMethodSignature) : list ClassName :=
    match MapShortMethSign.get _ p.(throwableBy_map) sms with
      | Some l => l
      | None => nil
    end.

    Definition classes p := MapClass.elements p.(classes_map).

    Definition class (p:t) (cn:ClassName) : option Class :=
      MapClass.get p.(classes_map) cn.

    Definition defined_Class (p:t) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.

    Lemma name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.
    Proof.
      unfold class; intros p cn cl H0.
      assert (UU:= MapClass.get_proj _ _ _ H0);subst;trivial.
    Qed.

    Lemma In_classes_defined_Class : forall p cl,
      distinct CLASS.name (classes p) ->
      In cl (classes p) -> defined_Class p cl.
    Proof.
      unfold defined_Class,class;intros.
      apply MapClass.in_elements_get_some;trivial.
    Qed.

    Lemma defined_Class_In_classes : forall p cl,
      defined_Class p cl -> In cl (classes p).
    Proof.
      unfold defined_Class, classes,class ; intros.     
      eapply MapClass.get_some_in_elements;eauto.
    Qed.

    Definition interfaces p := MapInterface.elements p.(interfaces_map).

    Definition interface (p:t) (i:InterfaceName): option Interface :=
      MapInterface.get p.(interfaces_map) i.
    Definition defined_Interface (p:t) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.
    Lemma name_interface_invariant1 : forall p iname i,
      interface p iname = Some i -> iname = INTERFACE.name i.
    Proof.
      unfold interface; intros p iname i H0.
      assert (UU:= MapInterface.get_proj _ _ _ H0);subst;trivial.
    Qed.
  End PROG.

  Definition Program := PROG.t.

  Module Type PROG_TYPE.
    Parameter class : Program -> ClassName -> option Class.
    Definition defined_Class (p:Program) (cl:Class) :=
      class p (CLASS.name cl) = Some cl.
    Parameter name_class_invariant1 : forall p cn cl,
      class p cn = Some cl -> cn = CLASS.name cl.
    Parameter interface : Program -> InterfaceName -> option Interface.
    Definition defined_Interface (p:Program) (i:Interface) :=
      interface p (INTERFACE.name i) = Some i.
    Parameter name_interface_invariant1 : forall p cn cl,
      interface p cn = Some cl -> cn = INTERFACE.name cl.
  End PROG_TYPE.

  Inductive isStatic (p:Program) (fs: FieldSignature) : Prop :=
    isStatic_field : forall (cn:ClassName) (cl:Class) (f:Field),
     PROG.class p (fst fs) = Some cl ->
     CLASS.field cl (FIELDSIGNATURE.name (snd fs)) = Some f ->
     FIELD.isStatic f = true ->
     isStatic p fs.

  Definition javaLangObject : ClassName := (javaLang,object).
  (*Definition javaLangThrowable : ClassName := (javaLang,throwable).*)

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
   Inductive lookup_here (p:Program) : ClassName ->  ShortMethodSignature -> Method -> Prop :=
    | lookup_here_c : forall cn msig meth, 
       findMethod p (cn,msig) = Some meth -> 
       lookup_here p cn msig meth.


  Inductive lookup (p:Program) : ClassName -> ShortMethodSignature -> (ClassName*Method) -> Prop :=
    | lookup_no_up : forall cn msig meth, lookup_here p cn msig meth -> lookup p cn msig (cn,meth)
    | lookup_up : forall cn  msig, (forall meth, ~ lookup_here p cn msig meth) -> 
      forall super res , direct_subclass_name p cn super -> lookup p super msig res -> lookup p cn msig res.
(*
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
(*
  Definition throwableAt (m:Method) (pc:PC) : list ClassName := 
    match METHOD.body m with
      None => nil
    | Some body => BYTECODEMETHOD.throwableAt body pc
    end.
*)

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

  (* subclass_test TO BE PROVED CORRECT ! *)  
  Module Map2P' := MapPair_Base BinMap_Base BinMap_Base.
  Module Map2P <: MAP with Definition key := (positive*positive)%type :=
      Map_Of_MapBase Map2P'.

  Definition subclass_test (p:Program):
         option (ClassName -> ClassName -> bool) :=
      @ImplemSubClass.subclass_test 
           ClassName CLASS.t 
           CLASS.name eqClassName CLASS.superClass
           Map2P.t Map2P.empty Map2P.update Map2P.get
           (PROG.classes p).

  Axiom subclass_test_prop : forall p test,
    subclass_test p = Some test ->
    forall c1 c2,
      if test c1 c2 then subclass_name p c1 c2
      else ~ subclass_name p c1 c2.

End Make.

Module P <: PROGRAM := Make.

Import P.

Definition bc_empty := MapN.empty (Instruction*(option PC * list ClassName)).

Definition bc_single pc i :=  
  MapN.update (Instruction*(option PC * list ClassName)) bc_empty pc (i,(None,nil)).

Definition bc_cons pc i pc' bc :=
  MapN.update (Instruction*(option PC * list ClassName)) bc pc (i,(Some pc',nil)).

Definition bc_cons' pc i pc' l bc :=
  MapN.update (Instruction*(option PC * list ClassName)) bc pc (i,(Some pc',l)).


(* creation function for method map *)

Definition ms_empty := MapShortMethSign.empty Method.

Definition ms_single ms := 
  MapShortMethSign.update Method ms_empty (METHOD.signature ms) ms.

Definition ms_cons ms mms := 
  MapShortMethSign.update Method mms (METHOD.signature ms) ms.


(* creation function for field map *)

Definition mf_empty := MapField.empty.

Definition mf_single mf := MapField.update mf_empty mf.

Definition mf_cons mf mmf := MapField.update mmf mf.


(* creation function for class map *)
 
Definition mc_empty := PROG.MapClass.empty.

Definition mc_cons c mc := PROG.MapClass.update mc c.

Definition mi_empty := PROG.MapInterface.empty.

Definition mi_cons c mc := PROG.MapInterface.update mc c.

Module MapClassName <: MAP with Definition key := ClassName := Map2P.

Definition eqFieldSignature := prod_eq _ eqClassName _ FIELDSIGNATURE.eq_t.
Lemma eqFieldSignature_spec : forall x y:FieldSignature, 
  if eqFieldSignature x y then x = y else x <> y.
Proof (prod_eq_spec _ _ eqClassName_spec _ _ FIELDSIGNATURE.eq_t_spec).

Module MapFieldSignature_hash <: HASH_TYPE.
  Definition t : Set := FieldSignature.
  Definition eq_t : t -> t -> bool := eqFieldSignature.
  Definition eq_t_spec : forall t1 t2, if eq_t t1 t2 then t1 = t2 else t1 <> t2 :=
    eqFieldSignature_spec.
  Definition eq_dec : forall x y:t, x=y \/ ~x=y := Aeq_dec _ _ eq_t_spec.
  Definition key : Set := (ShortClassName * ShortFieldName)%type.
  Definition hash : t -> key := fun x =>
    (snd (fst x), FIELDSIGNATURE.name (snd x)).
End MapFieldSignature_hash.

Module MapFieldSignature_base := MapHash_Base MapFieldSignature_hash Map2P'.
Module MapFieldSignature <: MAP with Definition key := FieldSignature :=
  Map_Of_MapBase MapFieldSignature_base.






