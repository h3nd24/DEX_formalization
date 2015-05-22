(** * Bicolano: Semantic domains (interface implementation) *)

Require Export JVM_ImplemProgramWithMap.
Require Export JVM_Domain.

 
Ltac caseeq t := generalize (refl_equal t); pattern t at -1 in |- * ; case t.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module JVM_Dom <: JVM_SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Module JVM_Prog := JVM_ImplemProgramWithMap.JVM_Make.
 Import JVM_Prog.

Open Scope Z_scope.
 Module SByte <: Numeric.NUMSIZE. Definition power := 7%nat. End SByte.
 Module SShort<: Numeric.NUMSIZE. Definition power := 15%nat. End SShort.
 Module SInt  <: Numeric.NUMSIZE. Definition power := 31%nat. End SInt.

 Module Byte  : Numeric.NUMERIC with Definition power := 7%nat := Numeric.Make SByte.
 Module Short : Numeric.NUMERIC with Definition power := 15%nat := Numeric.Make SShort.
 Module Int   : Numeric.NUMERIC with Definition power := 31%nat := Numeric.Make SInt.

 (** conversion *)
 Definition b2i (b:Byte.t) : Int.t := Int.const (Byte.toZ b).
 Definition s2i (s:Short.t) : Int.t := Int.const (Short.toZ s).
 Definition i2b (i:Int.t) : Byte.t := Byte.const (Int.toZ i).
 Definition i2s (i:Int.t) : Short.t := Short.const (Int.toZ i).
 Definition i2bool (i:Int.t) : Byte.t := Byte.const (Int.toZ i mod 2).

 Inductive JVM_num : Set :=
   | I : Int.t -> JVM_num
   | B : Byte.t -> JVM_num
   | Sh : Short.t -> JVM_num.
 
 (** Location is the domain of adresses in the heap *)
 Definition JVM_Location : Set := N.
 Definition JVM_Location_dec : forall loc1 loc2:JVM_Location,{loc1=loc2}+{~loc1=loc2} :=
   (Aeq_Dec _ _ Neq_spec).

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

 Module JVM_MapVar <: MAP with Definition key := JVM_Var := BinNatMap.

 Module JVM_LocalVar <: JVM_LOCALVAR.
   Definition t := JVM_MapVar.t JVM_value.
   Definition get : t -> JVM_Var -> option JVM_value := @JVM_MapVar.get JVM_value.
   Definition update : t -> JVM_Var -> JVM_value -> t := @JVM_MapVar.update JVM_value.
   Lemma get_update_new : forall l x v, get (update l x v) x = Some v.
   Proof. exact (JVM_MapVar.get_update1 JVM_value). Qed.
   Lemma get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
   Proof. 
    intros;refine (JVM_MapVar.get_update2 JVM_value _ _ _ _ _). 
    intro;apply H;subst;trivial.
  Qed.
  Definition empty := JVM_MapVar.empty JVM_value.
 End JVM_LocalVar.

 (* Domain of operand stacks *) 
 Module Type JVM_OPERANDSTACK.
   Definition t : Set := list JVM_value.
   Definition empty : t := nil.
   Definition push : JVM_value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option JVM_value := fun s n => nth_error s n.
 End JVM_OPERANDSTACK.

 Module JVM_OperandStack <: JVM_OPERANDSTACK.
   Definition t : Set := list JVM_value.
   Definition empty : t := nil.
   Definition push : JVM_value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option JVM_value := fun s n => nth_error s n.
  End JVM_OperandStack.

 (** Transfert fonction between operand stack and local variables necessary for invoke instructions *)
  
 Fixpoint stack2localvar_rec
    (os:JVM_OperandStack.t) (n:nat) (l:JVM_LocalVar.t) {struct n}: JVM_LocalVar.t :=
   match n with 
   | O => l
   | S n => 
      match os with
      | nil => l
      | v::os => 
         stack2localvar_rec os n (JVM_LocalVar.update l (N_toVar n) v)
      end
   end.
 Definition stack2localvar os n := stack2localvar_rec os n JVM_LocalVar.empty.

 Lemma stack2locvar_rec_prop1 :
   forall n l os x, (n <= Var_toN x)%nat -> 
     JVM_LocalVar.get (stack2localvar_rec  os n l) x = JVM_LocalVar.get l x.
 Proof.
  induction n;simpl;intros;trivial.
  destruct os;simpl;intros;trivial.
  assert (n <= Var_toN x)%nat. omega.
  rewrite IHn;trivial.
  unfold JVM_LocalVar.get, JVM_LocalVar.update;rewrite JVM_MapVar.get_update2;trivial.
  intro Heq;rewrite Heq in H.
  rewrite Var_toN_bij2 in H;omega.
 Qed.

 Lemma stack2locvar_prop1 :
   forall s n x, (n <= Var_toN x)%nat -> JVM_LocalVar.get (stack2localvar s n) x = None.
 Proof.
   unfold stack2localvar;intros.
   rewrite stack2locvar_rec_prop1;trivial.
   exact (JVM_MapVar.get_empty _ _).
 Qed.

 Lemma stack2locvar_rec_prop2 :
   forall n os l x, (Var_toN x < n)%nat ->
     (forall y, (Var_toN y < n)%nat -> JVM_LocalVar.get l y = None) ->
     JVM_LocalVar.get (stack2localvar_rec os n l) x = 
       JVM_OperandStack.get_nth os (n-(Var_toN x)-1)%nat.
 Proof.
   induction n;simpl;intros.
   elimtype False;omega.
   destruct os.
   rewrite H0;trivial.
   destruct (Var_toN x);simpl;trivial.
   destruct (n-0)%nat;trivial.
   destruct (n-n0-1)%nat;trivial.
   change (match Var_toN x with
   | O => (S n)
   | S l0 => (n - l0)
   end - 1)%nat with (S n- Var_toN x -1)%nat.
   assert (Var_toN x = n \/ Var_toN x < n)%nat. omega.
   destruct H1.
   pattern n at 2;rewrite <- H1;rewrite Var_toN_bij1.
   rewrite stack2locvar_rec_prop1. 2:omega.
   rewrite JVM_LocalVar.get_update_new.
   replace (S n - Var_toN x - 1)%nat with O;try omega.
   simpl;trivial.
   rewrite IHn;trivial.
   replace (S n - Var_toN x - 1)%nat with (S (n - Var_toN x - 1))%nat;try omega.
   simpl;trivial.
   intros;rewrite JVM_LocalVar.get_update_old.
   apply H0;omega.
   intro Heq;rewrite <-Heq in H2;rewrite Var_toN_bij2 in H2;omega.
  Qed.
   
 Lemma stack2locvar_prop2 :
   forall s n x, (Var_toN x < n)%nat ->
     JVM_LocalVar.get (stack2localvar s n) x = JVM_OperandStack.get_nth s (n-(Var_toN x)-1)%nat.
 Proof.
  unfold stack2localvar;intros;apply stack2locvar_rec_prop2;trivial.
  intros;exact (JVM_MapVar.get_empty _ _).
 Qed.


 Fixpoint all_super_classes (p:JVM_Program) (c:JVM_Class) (n:nat) {struct n} : option (list JVM_Class) :=
   match n with
     | O => None
     | S n =>
       match JVM_CLASS.superClass c with
         | None => Some nil
         | Some super_name => 
           match JVM_PROG.class p super_name with
             | None => None
             | Some super => 
               match (all_super_classes p super n) with
                 | None => None
                 | Some l => Some (super::l)
               end
           end
       end
   end.

 Ltac inv H := inversion H; subst; clear H.

 Lemma clos_refl_trans_ind2 :
      forall (A:Type) (R:A -> A -> Prop) (P:A -> A -> Prop),
        (forall x, P x x) ->
        (forall x y z:A, R x y -> clos_refl_trans A R y z -> P y z  -> P x z) ->
        forall x y, clos_refl_trans A R x y -> P x y.
 Proof.
   intros A R P H1 H2.
   assert (forall x y, clos_refl_trans A R x y -> 
              forall z, clos_refl_trans A R y z -> P y z -> P x z).
   induction 1; eauto; intros.
   apply IHclos_refl_trans1.
   constructor 3 with z; auto.
   apply IHclos_refl_trans2; auto.
   intros.
   apply H with y; auto.
   constructor 2.
 Qed.

Lemma subclass_left : forall p c1 c2,
  subclass p c1 c2 -> c1=c2 \/ (exists c, direct_subclass p c1 c /\ subclass p c c2).
Proof.
  intros p; unfold subclass; apply clos_refl_trans_ind2; intros; auto.
  destruct H1; subst; auto.
  right; exists z; auto.
  destruct H1 as [c [T1 T2]].
  right; exists y; split; auto.
Qed.

 Definition all_super_classes_correct : forall p n c l,
   all_super_classes p c n = Some l ->
   JVM_PROG.defined_Class p c -> 
   forall c', subclass p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros c l; case_eq (JVM_CLASS.superClass c).
   intros c' H'.
   case_eq (JVM_PROG.class p c'); try (intros; discriminate).
   intros c'' H''.
   case_eq (all_super_classes p c'' n); try (intros; discriminate).
   intros.
   inv H0.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H0 as [c0 [T1 T2]].
   clear H2.
   inv T1.
   unfold JVM_PROG.defined_Class in *.
   assert (c0 = c'') by congruence.
   assert (c'=JVM_CLASS.name c'') by congruence.
   subst.
   clear H2 H3 H1.
   right; apply (IHn _ _ H H'' _ T2).

   intros.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H3 as [c0 [T1 T2]].
   inv T1.
   congruence.
 Qed.

 Fixpoint all_super_interfaces (p:JVM_Program) (n:nat) {struct n} : 
                          JVM_Interface -> option (list JVM_Interface) :=
   match n with
     | O => fun _ => None
     | S n => fun c =>
       List.fold_left 
         (fun o iname =>
           match o with
             | None => None
             | Some l => 
               match JVM_PROG.interface p iname with
                 | None => None
                 | Some itf => 
                   match all_super_interfaces p n itf with
                     | None => None
                     | Some l' => Some (itf::l++l')
                   end
               end
           end) 
         (JVM_INTERFACE.superInterfaces c)
         (Some (c::nil))
   end.

Lemma subinterface_left : forall p c1 c2,
  subinterface p c1 c2 -> c1=c2 \/ (exists c, direct_subinterface p c1 c /\ subinterface p c c2).
Proof.
  intros p; unfold subinterface; apply clos_refl_trans_ind2; intros; auto.
  destruct H1; subst; auto.
  right; exists z; auto.
  destruct H1 as [c [T1 T2]].
  right; exists y; split; auto.
Qed.

Lemma all_super_interfaces_aux : forall p n l3,
   fold_left
     (fun (o : option (list JVM_Interface)) (iname : JVM_InterfaceName) =>
      match o with
      | Some l6 => 
             match JVM_PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l6 ++ l')
                 | None => None (A:=list JVM_Interface)
                 end
             | None => None (A:=list JVM_Interface)
             end
      | None => None (A:=list JVM_Interface)
      end) l3 None=None.
Proof.
  induction l3; simpl; auto.
Qed.

Lemma all_super_interfaces_aux' : forall p n l0 l1 l2,
     fold_left
        (fun (o : option (list JVM_Interface)) (iname : JVM_InterfaceName) =>
         match o with
         | Some l =>
             match JVM_PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l ++ l')
                 | None => None (A:=list JVM_Interface)
                 end
             | None => None (A:=list JVM_Interface)
             end
         | None => None (A:=list JVM_Interface)
         end) l0 (Some l1) = Some l2 -> incl l1 l2.
Proof.
  induction l0; simpl.
  intros.
  inversion H; subst; intro; auto.
  destruct (JVM_PROG.interface p a); try (intros; discriminate).
  destruct (all_super_interfaces p n j); try (intros; discriminate).
  intros.
  assert (IH:=IHl0 _ _ H); clear H IHl0.
  repeat intro; apply IH.
  right; auto with datatypes.
  rewrite all_super_interfaces_aux; intros; discriminate.
  rewrite all_super_interfaces_aux; intros; discriminate.
 Qed.


 Definition all_super_interfaces_correct : forall p n c l,
   all_super_interfaces p n c = Some l ->
   JVM_PROG.defined_Interface p c -> 
   forall c', subinterface p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros.
   destruct (subinterface_left _ _ _ H1); clear H1; auto.
   right; destruct H2 as [c0 [T1 T2]].
   inv T1.
   generalize dependent (Some (c::nil)).
   generalize dependent (JVM_INTERFACE.superInterfaces c).
   induction l0; simpl; intros.
   elim H3.
   destruct o; simpl in H; try discriminate.
   case_eq (JVM_PROG.interface p a); intros.   
   rewrite H4 in H.
   case_eq (all_super_interfaces p n j); intros.
   rewrite H5 in H.
   destruct H3; subst.
   unfold JVM_PROG.defined_Interface in *.
   assert (c0=j) by congruence; clear H4; subst.
   generalize (IHn _ _ H5 H2 _ T2).
   assert (T:=all_super_interfaces_aux' _ _ _ _ _ H).
   simpl; intros.
   apply T.
   destruct H3.
   left; auto.
   right; auto with datatypes.
   apply IHl0 with (Some (j :: l1 ++ l2)); auto.
   rewrite H5 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite H4 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite all_super_interfaces_aux in H; discriminate.
 Qed.

  Definition all_interfaces (p:JVM_Program) (n:nat) (c:JVM_Class) : option (list JVM_Interface) :=
    List.fold_left 
    (fun o iname =>
      match o with
        | None => None
        | Some l => 
          match JVM_PROG.interface p iname with
            | None => None
            | Some itf => 
              match all_super_interfaces p n itf with
                | None => None
                | Some l' => Some (itf::l++l')
              end
          end
      end) 
    (JVM_CLASS.superInterfaces c)
    (Some nil).

  Lemma all_interfaces_correct : forall p n c l,
    all_interfaces p n c = Some l -> forall i I I',
      In i (JVM_CLASS.superInterfaces c) ->
      JVM_PROG.interface p i = Some I ->
      subinterface p I I' -> 
      In I l.
  Proof.
    unfold all_interfaces.
    intros p n c.
    generalize (@nil JVM_Interface).
    generalize (JVM_CLASS.superInterfaces c).
    induction l; simpl.
    intuition.
    intros l0; case_eq (JVM_PROG.interface p a).
    intros i Hi; case_eq (all_super_interfaces p n i); intros.
    destruct H1; subst.
    assert (I0=i) by congruence; subst; clear Hi.
    apply (all_super_interfaces_aux' _ _ _ _ _ H0).
    left; reflexivity.
    eapply IHl ;eauto.
    rewrite all_super_interfaces_aux in H0; discriminate.
    intros.
    rewrite all_super_interfaces_aux in H0; intros; discriminate.
  Qed.



Set Implicit Arguments.

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

Module JVM_Heap <: JVM_HEAP.
  Module JVM_Object.
    Record t : Type := Obj { class : JVM_ClassName; fieldsval : JVM_MapFieldSignature.t JVM_value }.
    Definition get (o:t) := JVM_MapFieldSignature.get JVM_value o.(fieldsval).
    Definition op_get (o:option t) :=
      match o with
        | Some o => get o
        | None => fun f => None
      end.
    Definition op_update (f:JVM_FieldSignature) (v:JVM_value) (o:option t) : option t :=
      match o with
        | None => None
        | Some o => Some (Obj o.(class) (JVM_MapFieldSignature.update _ o.(fieldsval) f v))
      end.

    Definition init_fields :  list (JVM_ClassName*JVM_Field) -> JVM_MapFieldSignature.t JVM_value :=
      @fold_right (JVM_MapFieldSignature.t JVM_value) _
        (fun f m => JVM_MapFieldSignature.update _ m (fst f,JVM_FIELD.signature (snd f)) (init_field_value (snd f)))
        (JVM_MapFieldSignature.empty _).

    Definition default (c:JVM_Class) : t :=
      Obj
      (JVM_CLASS.name c) 
      (init_fields (List.map (fun f => (JVM_CLASS.name c,f)) (JVM_CLASS.definedFields c))).

  End JVM_Object.
  Module JVM_Array.
    Record t : Type := Arr {
      length : Int.t;
      element_type : JVM_type; 
      elements : BinNatMap.t JVM_value;
      creation_point : JVM_Method * JVM_PC
    }.

    Definition Ncase (i:Z)  : option N :=
      match i with
        | Z0 => Some N0
        | Zpos p => Some (Npos p)
        | _ => None
      end.

    Definition get (a:t) (i:Z) :=
      match Ncase i with
        | Some n => 
          match Zcompare i (Int.toZ a.(length)) with
            | Lt => BinNatMap.get JVM_value a.(elements) n
            | _ => None
          end
        | None => None
      end.
    Definition op_get (a:option (t)) :=
      match a with
        | Some a => get a
        | None => fun i => None
      end.
    Definition op_update (i:Z) (v:JVM_value) (a:option t) : option t :=
      match a with
        | None => None
        | Some a => 
          match Ncase i with
            | Some n =>
              match Zcompare i (Int.toZ a.(length)) with
                | Lt => Some 
                         (Arr a.(length) a.(element_type) (BinNatMap.update _ a.(elements) n v) a.(creation_point))
                | _ => Some a
              end
            | _ => Some a
          end
      end.

    Fixpoint init_array_rec (n:nat) (v:JVM_value) {struct n} : BinNatMap.t JVM_value :=
      match n with 
        | O => BinNatMap.empty _
        | S p => BinNatMap.update _ (init_array_rec p v) (N_of_nat p) v
      end.

    Definition default (lgth:Int.t) (n:nat) (tp:JVM_type) (a:JVM_Method*JVM_PC): t:=
      Arr lgth tp (init_array_rec n (init_value tp)) a.

   Definition N_to_nat (n:N) : nat :=
     match n with
       | Npos p => nat_of_P p
       | N0 => O
     end.
 
   Lemma ZL4_inf : forall y:positive, {h : nat | nat_of_P y = S h}.
   Proof.
   intro y; induction y as [p H| p H1| ];
    [ elim H; intros x H1; exists (S x + S x)%nat; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL0; rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H1; rewrite H1; auto with arith | elim H1; intros x H2; exists (x + S x)%nat; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL0; rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H2; rewrite H2; auto with arith | exists 0%nat; auto with arith ].
   Qed.

   Lemma N_of_nat_N_to_nat : forall n, N_of_nat (N_to_nat n) = n.
   Proof.
     unfold N_of_nat, N_to_nat; intros.
     destruct n.
     reflexivity.
     destruct (ZL4_inf p).
     rewrite e.
     generalize (nat_of_P_o_P_of_succ_nat_eq_succ x).
     rewrite <- e; intros.
     assert (Zpos (P_of_succ_nat x) = Zpos p).
     rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
     rewrite H.
     rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
     auto.
     congruence.
   Qed.

   Lemma N_to_nat_N_of_nat : forall n, N_to_nat (N_of_nat n) = n.
   Proof.
     unfold N_of_nat, N_to_nat; intros.
     destruct n.
     reflexivity.
     rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
     reflexivity.
   Qed.

   Lemma get_init_array_rec: forall n v i,
      (N_to_nat i<n)%nat ->
      BinNatMap.get _ (init_array_rec n v) i = Some v.
   Proof.
     induction n; simpl; intros.
     apply False_ind; omega.
     assert (N_to_nat i < n \/ N_to_nat i = n)%nat by omega.
     destruct H0; clear H.
     rewrite BinNatMap.get_update2.
     auto.
     intro; subst.
     rewrite N_to_nat_N_of_nat in H0; omega.
     subst.
     rewrite N_of_nat_N_to_nat.
     rewrite BinNatMap.get_update1.
     reflexivity.
   Qed.

   Lemma get_init_array_none_rec: forall n v i,
      (N_to_nat i>=n)%nat ->
      BinNatMap.get _ (init_array_rec n v) i = None.
   Proof.
     induction n; simpl; intros.
     apply BinNatMap.get_empty.
     rewrite BinNatMap.get_update2.
     apply IHn.
     omega.
     intro; subst.
     rewrite N_to_nat_N_of_nat in H; omega.
   Qed.


  End JVM_Array.

  Module JVM_LocMap := BinNatMap.

  Record t_ : Type := hp {
    statics : JVM_MapFieldSignature.t JVM_value;
    objects : JVM_LocMap.t JVM_Object.t;
    arrays : JVM_LocMap.t JVM_Array.t;
    next_loc : JVM_Location
  }.
  Definition t : Type := t_.
  
  Inductive JVM_AdressingMode : Set :=
  | StaticField : JVM_FieldSignature -> JVM_AdressingMode
  | DynamicField : JVM_Location -> JVM_FieldSignature -> JVM_AdressingMode
  | ArrayElement : JVM_Location -> Z -> JVM_AdressingMode.

  Inductive JVM_LocationType : Type :=
  | LocationObject : JVM_ClassName -> JVM_LocationType 
  | LocationArray : Int.t -> JVM_type -> JVM_Method*JVM_PC -> JVM_LocationType.

   Definition typeof (h:t) (l:JVM_Location) : option (JVM_LocationType) :=
     match JVM_LocMap.get _ h.(objects) l with
       | Some o => Some (LocationObject o.(JVM_Object.class))
       | None =>
         match JVM_LocMap.get _ h.(arrays) l with
           | Some a => Some (LocationArray a.(JVM_Array.length) a.(JVM_Array.element_type) a.(JVM_Array.creation_point))
           | None => None
         end
     end.

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

   Definition check_compat (h:t) (am:JVM_AdressingMode) : bool :=
     match am with
       | StaticField f => true
       | DynamicField loc f =>
         match typeof h loc with
           | Some (LocationObject _) => true
           | _ => false
         end
       | ArrayElement loc i =>
         match typeof h loc with
           | Some (LocationArray length _ _ ) => 
             match i ?= 0 with
               | Lt => false
               | _ =>
                 match i ?= Int.toZ length with
                   | Lt => true
                   | _ => false
                 end
             end
           | _ => false
         end
     end.

   Lemma bounded_compare : forall i t:Z,
     i < t -> i ?= t = Lt.
   Proof.
     intros.
     generalize (Zlt_compare _ _ H); rewrite H; auto.
   Qed.

   Lemma case_compare : forall i t:Z,
     (i ?= t = Lt /\ i<t) \/ (i ?=t = Gt) \/ (i ?=t = Eq).
   Proof.
     intros.
     generalize (Zge_compare i t0).
     destruct (i ?= t0); simpl; auto.
     left; split; auto; omega.
   Qed.

   Lemma check_compat_correct : forall h am,
     if check_compat h am then Compat h am else ~ Compat h am.
   Proof.
     unfold check_compat; intros.
     destruct am.
     constructor.
     case_eq (typeof h j); intros.
     destruct j1.
     econstructor; eauto.
     intro T; inversion T; subst.
     rewrite H1 in H; discriminate.
     intro T; inversion T; subst.
     rewrite H1 in H; discriminate.
     case_eq (typeof h j); intros.
     destruct j0.
     intro T; inversion T; subst.
     rewrite H3 in H; discriminate.
     generalize (Zge_compare z 0).
     generalize (Zlt_compare z 0).
     destruct (z ?= 0).
     generalize (Zge_compare z (Int.toZ t0)).
     generalize (Zlt_compare z (Int.toZ t0)).
     destruct (z ?= (Int.toZ t0)).
     repeat intro.
     inversion H4; subst.
     rewrite H8 in H; inversion H; subst; omega.
     intros; econstructor; eauto.
     omega.
     repeat intro.
     inversion H4; subst.
     rewrite H8 in H; inversion H; subst; omega.
     repeat intro.
     inversion H2; subst.
     rewrite H6 in H; inversion H; subst; omega.
     generalize (Zge_compare z (Int.toZ t0)).
     generalize (Zlt_compare z (Int.toZ t0)).
     destruct (z ?= (Int.toZ t0)).
     repeat intro.
     inversion H4; subst.
     rewrite H8 in H; inversion H; subst; omega.
     intros; econstructor; eauto.
     omega.
     repeat intro.
     inversion H4; subst.
     rewrite H8 in H; inversion H; subst; omega.
     intro.
     inversion H0; subst.
     rewrite H4 in H; inversion H.
   Qed.

  Definition get (h:t) (am:JVM_AdressingMode) : option JVM_value :=
    if check_compat h am then
      match am with
        | StaticField f =>  JVM_MapFieldSignature.get _ h.(statics) f
        | DynamicField l f => JVM_Object.op_get (JVM_LocMap.get _ h.(objects) l) f
        | ArrayElement l i => JVM_Array.op_get (JVM_LocMap.get _ h.(arrays) l) i 
      end
      else None.
  Definition update (h:t) (am:JVM_AdressingMode) (v:JVM_value) : t :=
    if check_compat h am then
      match am with
        | StaticField f => 
          hp
          (JVM_MapFieldSignature.update _ h.(statics) f v)
          h.(objects)
          h.(arrays)
          h.(next_loc)
        | DynamicField l f => 
          hp
          h.(statics)
          (JVM_LocMap.modify _ h.(objects) l (JVM_Object.op_update f v))
          h.(arrays)              
          h.(next_loc)
        | ArrayElement l i => 
          hp
          h.(statics)
          h.(objects)
          (JVM_LocMap.modify _ h.(arrays) l (JVM_Array.op_update i v))
          h.(next_loc)
      end else h.     

   Definition Int_to_nat (i:Int.t) : option nat :=
     match Int.toZ i with
       | Zpos p => Some (nat_of_P p)
       | Z0 => Some O
       | Zneg _ => None
     end.

   Definition check_fresh (h:t) (l:JVM_Location) : bool :=
     match JVM_LocMap.get _ h.(objects) l with
       | Some _ => false
       | _ =>      
         match JVM_LocMap.get _ h.(arrays) l with
           | Some _ => false
           | _ => true
         end
     end.

   Lemma check_fresh_correct : forall h l,
     check_fresh h l = true ->
       (JVM_LocMap.get _ h.(objects) l = None
        /\ JVM_LocMap.get _ h.(arrays) l = None).
   Proof.
     unfold check_fresh; intros.
     destruct (JVM_LocMap.get _ (objects h) l); try discriminate.
     destruct (JVM_LocMap.get _ (arrays h) l); try discriminate.
     auto.
   Qed.

   Definition new (h:t) (p:JVM_Program) (ltp:JVM_LocationType) : option (JVM_Location * t) :=
     if check_fresh h h.(next_loc) then
       match ltp with
         | LocationObject cn => 
           match JVM_PROG.class p cn with
             | None => None
             | Some c => 
                 Some
                 (h.(next_loc),
                   hp
                   h.(statics)
                   (JVM_LocMap.update _ h.(objects) h.(next_loc) (JVM_Object.default c))
                   h.(arrays)              
                   (Nsucc h.(next_loc)))
           end
       | LocationArray lgth tp a => 
             match Int_to_nat lgth with
               | None => None
               | Some n =>
                 Some
                 (h.(next_loc),
                   hp
                   h.(statics)
                   h.(objects)              
                   (JVM_LocMap.update _ h.(arrays) h.(next_loc) (JVM_Array.default lgth n tp a))
                   (Nsucc h.(next_loc)))
             end
       end
       else None.

   Lemma pos_Ncase : forall i:Z,
     0<=i -> exists n, JVM_Array.Ncase i = Some n.
   Proof.
     destruct i; simpl; intros; eauto.
     elim H; auto.
   Qed.

   Lemma case_Ncase : forall i:Z,
     JVM_Array.Ncase i = None \/
     exists n, JVM_Array.Ncase i = Some n /\ 0<=i.
   Proof.
     destruct i; simpl; eauto with zarith.
   Qed.

   Lemma Ncase_inj : forall i j,
     JVM_Array.Ncase i = JVM_Array.Ncase j -> JVM_Array.Ncase i <> None -> i = j.
   Proof.
     destruct i; destruct j; intros H; inversion H; auto.
     simpl; intuition.
   Qed.

   Lemma typeof_update_same : forall h loc am v,
     typeof (update h am v) loc = typeof h loc.
   Proof.
     unfold typeof, update; intros.
     generalize (check_compat_correct h am); destruct (check_compat h am); simpl; intros.
     destruct H; simpl.
     auto.
     destruct (PC_eq_dec loc0 loc); subst.
     unfold typeof in H.
     rewrite JVM_LocMap.get_modify1; auto.
     unfold JVM_LocMap.get in H.
     unfold JVM_LocMap.get in *.
     case_eq (BinNatMap_Base.get JVM_Object.t (objects h) loc); intros.
     rewrite H0 in H.
     reflexivity.
     rewrite H0 in H.
     reflexivity.
     
     rewrite JVM_LocMap.get_modify2; auto.

     destruct (PC_eq_dec loc0 loc); subst.
     rewrite JVM_LocMap.get_modify1; auto.
     unfold typeof in *.
     destruct (JVM_LocMap.get JVM_Object.t (objects h) loc); try reflexivity.
     unfold JVM_LocMap.get in *.
     case_eq (BinNatMap_Base.get _ (arrays h) loc); simpl; intros.
     rewrite H1 in H0.
     inversion H0; clear H0; subst.
     elim (@pos_Ncase i); [intros n H2|omega].
     rewrite H2.
     rewrite bounded_compare; try omega.
     reflexivity.
     reflexivity.
     rewrite JVM_LocMap.get_modify2; auto.

     reflexivity.
   Qed.

   Lemma Compat_update1 : forall h am am0 v0,
     Compat h am -> Compat (update h am0 v0) am.
   Proof.
     destruct 1; econstructor; eauto.
     rewrite typeof_update_same; eauto.
     rewrite typeof_update_same; eauto.
   Qed.

   Lemma Compat_update2 : forall h am am0 v0,
     Compat (update h am0 v0) am -> Compat h am.
   Proof.
     destruct 1; econstructor; eauto.
     rewrite typeof_update_same in H; eauto.
     rewrite typeof_update_same in H0; eauto.
   Qed.

   Lemma check_compat_update : forall h am v am',
     check_compat (update h am v) am' = check_compat h am'.
   Proof.
     intros.
     generalize (check_compat_correct (update h am v) am').
     generalize (check_compat_correct h am').
     destruct (check_compat (update h am v) am');
     destruct (check_compat h am'); auto.
     intros.
     elim H; eapply Compat_update2; eauto.
     intros.
     elim H0; eapply Compat_update1; eauto.   
   Qed.

   Lemma get_update_same : forall h am v, Compat h am ->  get (update h am v) am = Some v.
   Proof.
     unfold get; intros.
     rewrite check_compat_update.
     unfold update.
     generalize (check_compat_correct h am); destruct (check_compat h am).
     clear H.     
     destruct 1; simpl.
     rewrite JVM_MapFieldSignature.get_update1; auto.
     rewrite JVM_LocMap.get_modify1; auto.
     caseeq (BinNatMap_Base.get JVM_Object.t (objects h) loc); intros; simpl.
     unfold JVM_Object.get; simpl.
     rewrite JVM_MapFieldSignature.get_update1; auto.
     unfold typeof in H.
     replace JVM_LocMap.get with BinNatMap_Base.get in H; auto.
     rewrite H0 in H.
     destruct (BinNatMap_Base.get (JVM_Array.t) (arrays h) loc); discriminate.

     unfold typeof in H0.
     replace JVM_LocMap.get with BinNatMap_Base.get in *; auto.
     caseeq (BinNatMap_Base.get JVM_Object.t (objects h) loc); intros; simpl.
     rewrite H1 in H0.
     inversion H0.
     rewrite H1 in *.
     rewrite JVM_LocMap.get_modify1; auto.
     unfold JVM_Array.op_update, JVM_Array.op_get, JVM_Array.get.
     caseeq (BinNatMap_Base.get _ (arrays h) loc); intros.
     rewrite H2 in H0.
     injection H0; intros; subst; clear H0.
     destruct (JVM_Array.elements t0).
     elim (@pos_Ncase i); [intros n Hn|omega].
     rewrite Hn.
     rewrite bounded_compare; [idtac|omega].
     rewrite Hn.
     simpl.
     rewrite bounded_compare; [idtac|omega].
     destruct n; simpl; auto.
     rewrite BinMap_Base.get_modify1; auto.
     rewrite H2 in H0; discriminate.
     intuition.
   Qed.

   Lemma get_update_old : forall h am1 am2 v, am1<>am2 -> get (update h am1 v) am2 = get h am2.
   Proof.
     unfold get; intros.
     rewrite check_compat_update.
     unfold update; intros.
     generalize (check_compat_correct h am1); destruct (check_compat h am1); auto.
     destruct 1; destruct am2; simpl; intros; auto.
     rewrite JVM_MapFieldSignature.get_update2; auto; congruence.

     destruct (PC_eq_dec loc j); subst.
     rewrite JVM_LocMap.get_modify1; auto.
     unfold typeof,JVM_LocMap.get in *.
     destruct (BinNatMap_Base.get JVM_Object.t (objects h) j); simpl in *.
     unfold JVM_Object.get; simpl.
     rewrite JVM_MapFieldSignature.get_update2; auto; congruence.
     auto.
     rewrite JVM_LocMap.get_modify2; auto.

     destruct (PC_eq_dec loc j); subst.
     unfold typeof in H1.
     caseeq (JVM_LocMap.get _ (objects h) j); intros; simpl; auto.
     rewrite H2 in H1; inversion H1.
     rewrite H2 in H1.
     unfold JVM_LocMap.get in *.
     rewrite JVM_LocMap.get_modify1; auto.
     clear H2.
     caseeq (BinNatMap_Base.get JVM_Array.t (arrays h) j); intros; simpl; auto.
     rewrite H2 in H1; try discriminate.
     inversion H1; subst; clear H1.
     destruct (case_Ncase i).
     rewrite H1; auto.
     destruct H1 as [n [H1 H3]]; rewrite H1.
     destruct (case_compare i (Int.toZ (JVM_Array.length t0))).
     destruct H4 as [H4 H5]; rewrite H4.
     simpl.
     unfold JVM_Array.get.
     destruct (case_Ncase z).
     rewrite H6; auto.
     destruct H6 as [n' [H6 H7]]; rewrite H6; simpl.
     destruct (case_compare z (Int.toZ (JVM_Array.length t0))).
     destruct H8 as [H8 H9]; rewrite H8.
     rewrite BinNatMap.get_update2; auto.
     intro; assert (i=z) by (apply Ncase_inj; congruence).
     elim H; congruence.
     destruct H8; rewrite H8; auto.
     destruct H4; rewrite H4; auto.
     rewrite JVM_LocMap.get_modify2; auto.
   Qed.
     
   Lemma get_uncompat : forall h am, ~ Compat h am -> get h am = None.
   Proof.
     unfold get; intros.
     generalize (check_compat_correct h am);
       destruct (check_compat h am); intuition.
   Qed.

   Lemma new_fresh_location : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc:JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.
   Proof.
     unfold new; intros.
     generalize (check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     intros T; destruct (T (refl_equal _)); clear T.
     unfold typeof; destruct lt.
     destruct (JVM_PROG.class p j); try discriminate.
     inversion H; clear H; subst.
     rewrite H0; rewrite H1; reflexivity.
     destruct (Int_to_nat t0); try discriminate.
     inversion H; clear H; subst.
     rewrite H0; rewrite H1; reflexivity.
   Qed.
     
   Lemma new_typeof : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc:JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct lt.
     case_eq (JVM_PROG.class p j); intros.
     rewrite H0 in H.
     inversion H; clear H; subst.
     simpl.
     rewrite JVM_LocMap.get_update1.
     generalize (JVM_PROG.name_class_invariant1 _ _ _ H0).
     unfold JVM_Object.default; simpl.
     intros; congruence.
     rewrite H0 in H; discriminate.
     destruct (Int_to_nat t0); inversion H; clear H; subst; simpl.
     destruct (T (refl_equal _)) as [T1 T2]; clear T.
     rewrite T1.
     rewrite JVM_LocMap.get_update1.
     reflexivity.
   Qed.

   Lemma new_typeof_old : forall (h:t) (p:JVM_Program) (lt:JVM_LocationType) (loc loc':JVM_Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (T (refl_equal _)) as [T1 T2]; clear T.
     destruct lt.
     destruct (JVM_PROG.class p j); try discriminate.
     inversion H; clear H; subst.
     simpl.
     rewrite JVM_LocMap.get_update2; auto.
     destruct (Int_to_nat t0); inversion H; clear H; subst; simpl.
     rewrite JVM_LocMap.get_update2; auto.
   Qed.

   Lemma Compat_new_obj1 :
     forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     Compat h am -> Compat h' am.
   Proof.
     intros.
     destruct H0; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H); eauto.
     intro; subst.
     rewrite (@new_fresh_location _ _ _ _ _ H) in H0.
     discriminate.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H); eauto.
     intro; subst.
     rewrite (@new_fresh_location _ _ _ _ _ H) in H1.
     discriminate.     
   Qed.

   Lemma Compat_new_obj2 :
     forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:JVM_FieldSignature), am <> (DynamicField loc fs)) ->
     Compat h' am -> Compat h am.
   Proof.
     intros.
     destruct H1; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H) in H1; eauto.
     intro; subst.
     elim (H0 f); auto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H) in H2; eauto.
     intro; subst.
     rewrite (@new_typeof _ _ _ _ _ H) in H2.
     discriminate.     
   Qed.

   Lemma check_compat_new_obj :
     forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:JVM_FieldSignature), am <> (DynamicField loc fs)) ->
     check_compat h' am = check_compat h am.
   Proof.
     intros.
     generalize (check_compat_correct h' am).
     generalize (check_compat_correct h am).
     destruct (check_compat h' am);
     destruct (check_compat h am); auto.
     intros.
     elim H1; eapply Compat_new_obj2; eauto.
     intros.
     elim H2; eapply Compat_new_obj1; eauto.   
   Qed.

   Lemma Compat_new_array1 :
     forall (h:t) (p:JVM_Program) i tp a (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationArray i tp a) = Some (loc,h') ->
     Compat h am -> Compat h' am.
   Proof.
     intros.
     destruct H0; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H); eauto.
     intro; subst.
     rewrite (@new_fresh_location _ _ _ _ _ H) in H0.
     discriminate.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H); eauto.
     intro; subst.
     rewrite (@new_fresh_location _ _ _ _ _ H) in H1.
     discriminate.     
   Qed.

   Lemma Compat_new_array2 :
     forall (h:t) (p:JVM_Program) i tp a (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationArray i tp a) = Some (loc,h') ->
     (forall j, am <> (ArrayElement loc j)) ->
     Compat h' am -> Compat h am.
   Proof.
     intros.
     destruct H1; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H) in H1; eauto.
     intro; subst.
     rewrite (@new_typeof _ _ _ _ _ H) in H1.
     discriminate.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H) in H2; eauto.
     intro; subst.
     elim (H0 i0); auto.
   Qed.

   Lemma check_compat_new_array :
     forall (h:t) (p:JVM_Program) i tp a (loc:JVM_Location) (h':t) am,
     new h p (LocationArray i tp a) = Some (loc,h') ->
     (forall j, am <> (ArrayElement loc j)) ->
     check_compat h' am = check_compat h am.
   Proof.
     intros.
     generalize (check_compat_correct h' am).
     generalize (check_compat_correct h am).
     destruct (check_compat h' am);
     destruct (check_compat h am); auto.
     intros.
     elim H1; eapply Compat_new_array2; eauto.
     intros.
     elim H2; eapply Compat_new_array1; eauto.   
   Qed.

   Parameter new_defined_object_field : forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (fs:JVM_FieldSignature) (f:JVM_Field) (loc:JVM_Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DynamicField loc fs) = Some (init_field_value f).

   Axiom new_undefined_object_field : forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (fs:JVM_FieldSignature) (loc:JVM_Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DynamicField loc fs) = None.
 
  Lemma new_object_no_change : 
     forall (h:t) (p:JVM_Program) (cn:JVM_ClassName) (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:JVM_FieldSignature), am <> (DynamicField loc fs)) ->
     get h' am = get h am.
   Proof.
     unfold get; intros.
     rewrite (@check_compat_new_obj _ _ _ _ _ _ H H0).
     assert (T:=check_compat_correct h am).
     destruct (check_compat h am); try reflexivity.
     unfold new in *.
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (JVM_PROG.class p cn); try discriminate.
     inversion H; clear H; subst.
     destruct T; simpl.
     reflexivity.
     rewrite JVM_LocMap.get_update2; auto.
     intro; subst; elim (H0 f); auto.
     auto.
   Qed.

  Lemma new_valid_array_index : forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (i:Z) (loc:JVM_Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = Some (init_value tp).
   Proof.
     unfold get; intros.
     assert (T:=check_compat_correct h' (ArrayElement loc i)).
     destruct (check_compat h' (ArrayElement loc i)).
     unfold new in *; simpl.
     destruct (check_fresh h (next_loc h)); try discriminate.
     assert (exists p, Int.toZ length = Zpos p).
     destruct (Int.toZ length); eauto.
     apply False_ind; omega.
     generalize (Zlt_neg_0 p0); intros.
     apply False_ind; omega.
     destruct H1.
     unfold Int_to_nat in H; rewrite H1 in H.
     inversion H; clear H; subst.
     simpl.
     rewrite JVM_LocMap.get_update1.
     simpl.
     unfold JVM_Array.default; simpl.
     unfold JVM_Array.get; simpl.
     unfold JVM_Array.Ncase.
     rewrite H1.
     rewrite bounded_compare.
     destruct i.
     apply JVM_Array.get_init_array_rec. 
     simpl.
     apply lt_O_nat_of_P.
     apply JVM_Array.get_init_array_rec. 
     simpl.
     apply nat_of_P_lt_Lt_compare_morphism.
     generalize (Zlt_compare (Zpos p0) (Zpos x)).
     simpl. 
      intros. inversion H0. rewrite H1 in H3. apply H3.
     generalize (Zlt_neg_0 p0); intros. omega.
     omega. 
     elim T; econstructor; eauto.
     eapply new_typeof; eauto.
   Qed.

  Lemma new_unvalid_array_index : forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (i:Z) (loc:JVM_Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     ~ 0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = None.
  Proof.
     unfold get; intros.
     assert (T:=check_compat_correct h' (ArrayElement loc i)).
     destruct (check_compat h' (ArrayElement loc i)).
     unfold new in *; simpl.
     destruct (check_fresh h (next_loc h)); try discriminate.
     unfold JVM_Array.op_get, JVM_Array.get.
     inversion T; clear T; subst.
     case_eq (Int_to_nat length); intros.
     rewrite H1 in H; try discriminate.
     inversion H; clear H; subst.
     simpl.
     rewrite JVM_LocMap.get_update1.
     elim (@pos_Ncase  i); [intros|omega].
     rewrite H.
     simpl.
     unfold typeof in H4.
     simpl in H4.
     destruct (JVM_LocMap.get JVM_Object.t (objects h) (next_loc h)); try discriminate.
     rewrite JVM_LocMap.get_update1 in H4.
     inversion H4; clear H4; subst.
     elim H0; auto.
     rewrite H1 in H; discriminate.
     reflexivity.
   Qed.

  Lemma new_array_no_change : 
     forall (h:t) (p:JVM_Program) (length:Int.t) (tp:JVM_type) a (loc:JVM_Location) (h':t) (am:JVM_AdressingMode),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     (forall (i:Z), am <> (ArrayElement loc i)) ->
     get h' am = get h am.
  Proof.
     unfold get; intros.
     rewrite (@check_compat_new_array _ _ _ _ _ _ _ _ H H0).
     assert (T:=check_compat_correct h am).
     destruct (check_compat h am); try reflexivity.
     unfold new in *.
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (Int_to_nat length); try discriminate.
     inversion H; clear H; subst.
     destruct T; simpl.
     reflexivity.
     reflexivity.
     rewrite JVM_LocMap.get_update2; auto.
     intro; subst; elim (H0 i); auto.
   Qed.

 End JVM_Heap.

Opaque JVM_Heap.update.
  Inductive JVM_ReturnVal : Set :=
   | Normal : option JVM_value -> JVM_ReturnVal
   | Exception : JVM_Location -> JVM_ReturnVal.

 (** Domain of frames *)
 Module Type JVM_FRAME.
   Inductive t : Type := 
      make : JVM_Method -> JVM_PC -> JVM_OperandStack.t -> JVM_LocalVar.t -> t.
 End JVM_FRAME.
 
 Module JVM_Frame.
   Inductive t : Type := 
      make : JVM_Method -> JVM_PC -> JVM_OperandStack.t -> JVM_LocalVar.t -> t.
 End JVM_Frame.

 (** Domain of call stacks *)
 Module Type JVM_CALLSTACK.
   Definition t : Type := list JVM_Frame.t.
 End JVM_CALLSTACK.

 Module JVM_CallStack.
   Definition t : Type := list JVM_Frame.t.
 End JVM_CallStack.
(* DEX
 Module Type EXCEPTION_FRAME.
   Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
 End EXCEPTION_FRAME.
 Module ExceptionFrame.
    Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
  End ExceptionFrame.
*)
 (** Domain of states *)
 Module Type JVM_STATE.
   Inductive t : Type := 
      normal : JVM_Heap.t -> JVM_Frame.t -> JVM_CallStack.t -> t
    (* DEX | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t *).
   Definition get_sf  (s:t) : JVM_CallStack.t :=
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

 Module JVM_State.
  Inductive t : Type := 
      normal : JVM_Heap.t -> JVM_Frame.t -> JVM_CallStack.t -> t
    (* DEX | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t *).
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
 End JVM_State.
 (** Some notations *)
 Notation St := JVM_State.normal.
(* DEX Notation StE := State.exception. *)
 Notation Fr := JVM_Frame.make.
(* DEX Notation FrE := ExceptionFrame.make. *)

  (** compatibility between ArrayKind and type *) 
  Inductive compat_ArrayKind_type : JVM_ArrayKind -> JVM_type -> Prop :=
    | compat_ArrayKind_type_ref : forall rt,
        compat_ArrayKind_type Aarray (JVM_ReferenceType rt)
    | compat_ArrayKind_type_int : 
        compat_ArrayKind_type Iarray (JVM_PrimitiveType JVM_INT)
    | compat_ArrayKind_type_byte : 
        compat_ArrayKind_type Barray (JVM_PrimitiveType JVM_BYTE)
    | compat_ArrayKind_type_bool : 
        compat_ArrayKind_type Barray (JVM_PrimitiveType JVM_BOOLEAN)
    | compat_ArrayKind_type_short : 
        compat_ArrayKind_type Sarray (JVM_PrimitiveType JVM_SHORT).

  Inductive isReference : JVM_value -> Prop :=
  | isReference_null : isReference Null
  | isReference_ref : forall loc, isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : JVM_ValKind -> JVM_value -> Prop :=
    | compat_ValKind_value_ref : forall v,
        isReference v -> compat_ValKind_value Aval v
    | compat_ValKind_value_int : forall n,
        compat_ValKind_value Ival (Num (I n)).

  (** compatibility between ArrayKind and value *) 
  Inductive compat_ArrayKind_value : JVM_ArrayKind -> JVM_value -> Prop :=
    | compat_ArrayKind_value_ref : forall v,
        isReference v -> compat_ArrayKind_value Aarray v
    | compat_ArrayKind_value_int : forall n,
        compat_ArrayKind_value Iarray (Num (I n))
    | compat_ArrayKind_value_byte : forall n,
        compat_ArrayKind_value Barray (Num (B n))
    | compat_ArrayKind_value_short : forall n,
        compat_ArrayKind_value Sarray (Num (Sh n)).

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
          SemCompRef EqRef v1 v2
  | SemCompRef_ne : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 <> v2 ->
     (****************************************************)
          SemCompRef NeRef v1 v2.

  Definition SemCompInt (cmp:JVM_CompInt) (z1 z2: Z) : Prop :=
    match cmp with
      EqInt =>  z1=z2
    | NeInt => z1<>z2
    | LtInt => z1<z2
    | LeInt => z1<=z2
    | GtInt => z1>z2
    | GeInt => z1>=z2
    end.

  Definition SemBinopInt (op:JVM_BinopInt) (i1 i2:Int.t) : Int.t :=
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
(* DEX
  Inductive CaughtException  (p:Program) : Method -> PC*Heap.t*Location -> PC -> Prop :=
    CaughtException_def : forall m pc h loc bm pc' e,
      METHOD.body m = Some bm ->
      Heap.typeof h loc = Some (Heap.LocationObject e) ->
      lookup_handlers p (BYTECODEMETHOD.exceptionHandlers bm) pc e pc' ->
      CaughtException p m (pc,h,loc) pc'.

  Inductive UnCaughtException  (p:Program) : Method -> PC*Heap.t*Location -> Prop :=
    UnCaughtException_def : forall m pc h loc bm e,
      METHOD.body m = Some bm ->
      Heap.typeof h loc = Some (Heap.LocationObject e) ->
      (forall pc', ~ lookup_handlers p (BYTECODEMETHOD.exceptionHandlers bm) pc e pc') ->
      UnCaughtException p m (pc,h,loc).
*)

End JVM_Dom.

