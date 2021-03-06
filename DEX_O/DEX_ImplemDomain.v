(** * Bicolano: Semantic domains (interface implementation) *)
(* Hendra : - Modified to suit DEX program (Removed Operand Stack).
            - Removed Reference comparison. 
            - Also trim the system to contain only Arithmetic *)

Require Export DEX_ImplemProgramWithMap.
Require Export DEX_Domain.
 
Ltac caseeq t := generalize (refl_equal t); pattern t at -1 in |- * ; case t.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module DEX_Dom <: DEX_SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Module DEX_Prog := DEX_ImplemProgramWithMap.DEX_Make.
 Import DEX_Prog.

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

 Definition DEX_Location : Set := N.
 Definition DEX_Location_dec : forall loc1 loc2:DEX_Location,{loc1=loc2}+{~loc1=loc2} :=
   (Aeq_Dec _ _ Neq_spec).

 Inductive DEX_num : Set :=
   | I : Int.t -> DEX_num
   | B : Byte.t -> DEX_num
   | Sh : Short.t -> DEX_num.

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

 Module DEX_MapReg <: MAP with Definition key := DEX_Reg := BinNatMap.

 Module DEX_Registers <: DEX_REGISTERS.
   Definition t := DEX_MapReg.t DEX_value.
   Definition get : t -> DEX_Reg -> option DEX_value := @DEX_MapReg.get DEX_value.
   Definition update : t -> DEX_Reg -> DEX_value -> t := @DEX_MapReg.update DEX_value.
   Definition dom : t -> list DEX_Reg := @DEX_MapReg.dom DEX_value.
   Lemma get_update_new : forall l x v, get (update l x v) x = Some v.
   Proof. exact (DEX_MapReg.get_update1 DEX_value). Qed.
   Lemma get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
   Proof. 
    intros;refine (DEX_MapReg.get_update2 DEX_value _ _ _ _ _). 
    intro;apply H;subst;trivial.
  Qed.
  Definition empty := DEX_MapReg.empty DEX_value.
 End DEX_Registers.

 Fixpoint listreg2regs_rec
    (l_ori:DEX_Registers.t) (n:nat) (lv:list DEX_Reg) (l:DEX_Registers.t) {struct n}: DEX_Registers.t :=
   match n with 
   | O => l
   | S n =>
     match lv with 
     | nil => l
     | h :: t =>
       match DEX_Registers.get l_ori h with
       | None =>
         listreg2regs_rec l_ori n t l
       | Some v => 
         listreg2regs_rec l_ori n t (DEX_Registers.update l (N_toReg n) v)
       end
     end
   end.
 Definition listreg2regs (l_ori:DEX_Registers.t) (n:nat) (lv:list DEX_Reg)
   := listreg2regs_rec l_ori n lv DEX_Registers.empty.


 Fixpoint all_super_classes (p:DEX_Program) (c:DEX_Class) (n:nat) {struct n} : option (list DEX_Class) :=
   match n with
     | O => None
     | S n =>
       match DEX_CLASS.superClass c with
         | None => Some nil
         | Some super_name => 
           match DEX_PROG.class p super_name with
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
   DEX_PROG.defined_Class p c -> 
   forall c', subclass p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros c l; case_eq (DEX_CLASS.superClass c).
   intros c' H'.
   case_eq (DEX_PROG.class p c'); try (intros; discriminate).
   intros c'' H''.
   case_eq (all_super_classes p c'' n); try (intros; discriminate).
   intros.
   inv H0.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H0 as [c0 [T1 T2]].
   clear H2.
   inv T1.
   unfold DEX_PROG.defined_Class in *.
   assert (c0 = c'') by congruence.
   assert (c'=DEX_CLASS.name c'') by congruence.
   subst.
   clear H2 H3 H1.
   right; apply (IHn _ _ H H'' _ T2).

   intros.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H3 as [c0 [T1 T2]].
   inv T1.
   congruence.
 Qed.

 Fixpoint all_super_interfaces (p:DEX_Program) (n:nat) {struct n} : 
                          DEX_Interface -> option (list DEX_Interface) :=
   match n with
     | O => fun _ => None
     | S n => fun c =>
       List.fold_left 
         (fun o iname =>
           match o with
             | None => None
             | Some l => 
               match DEX_PROG.interface p iname with
                 | None => None
                 | Some itf => 
                   match all_super_interfaces p n itf with
                     | None => None
                     | Some l' => Some (itf::l++l')
                   end
               end
           end) 
         (DEX_INTERFACE.superInterfaces c)
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
     (fun (o : option (list DEX_Interface)) (iname : DEX_InterfaceName) =>
      match o with
      | Some l6 => 
             match DEX_PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l6 ++ l')
                 | None => None (A:=list DEX_Interface)
                 end
             | None => None (A:=list DEX_Interface)
             end
      | None => None (A:=list DEX_Interface)
      end) l3 None=None.
Proof.
  induction l3; simpl; auto.
Qed.

Lemma all_super_interfaces_aux' : forall p n l0 l1 l2,
     fold_left
        (fun (o : option (list DEX_Interface)) (iname : DEX_InterfaceName) =>
         match o with
         | Some l =>
             match DEX_PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l ++ l')
                 | None => None (A:=list DEX_Interface)
                 end
             | None => None (A:=list DEX_Interface)
             end
         | None => None (A:=list DEX_Interface)
         end) l0 (Some l1) = Some l2 -> incl l1 l2.
Proof.
  induction l0; simpl.
  intros.
  inversion H; subst; intro; auto.
  destruct (DEX_PROG.interface p a); try (intros; discriminate).
  destruct (all_super_interfaces p n d); try (intros; discriminate).
  intros.
  assert (IH:=IHl0 _ _ H); clear H IHl0.
  repeat intro; apply IH.
  right; auto with datatypes.
  rewrite all_super_interfaces_aux; intros; discriminate.
  rewrite all_super_interfaces_aux; intros; discriminate.
 Qed.


 Definition all_super_interfaces_correct : forall p n c l,
   all_super_interfaces p n c = Some l ->
   DEX_PROG.defined_Interface p c -> 
   forall c', subinterface p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros.
   destruct (subinterface_left _ _ _ H1); clear H1; auto.
   right; destruct H2 as [c0 [T1 T2]].
   inv T1.
   generalize dependent (Some (c::nil)).
   generalize dependent (DEX_INTERFACE.superInterfaces c).
   induction l0; simpl; intros.
   elim H3.
   destruct o; simpl in H; try discriminate.
   case_eq (DEX_PROG.interface p a); intros.   
   rewrite H4 in H.
   case_eq (all_super_interfaces p n d); intros.
   rewrite H5 in H.
   destruct H3; subst.
   unfold DEX_PROG.defined_Interface in *.
   assert (c0=d) by congruence; clear H4; subst.
   generalize (IHn _ _ H5 H2 _ T2).
   assert (T:=all_super_interfaces_aux' _ _ _ _ _ H).
   simpl; intros.
   apply T.
   destruct H3.
   left; auto.
   right; auto with datatypes.
   apply IHl0 with (Some (d :: l1 ++ l2)); auto.
   rewrite H5 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite H4 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite all_super_interfaces_aux in H; discriminate.
 Qed.

  Definition all_interfaces (p:DEX_Program) (n:nat) (c:DEX_Class) : option (list DEX_Interface) :=
    List.fold_left 
    (fun o iname =>
      match o with
        | None => None
        | Some l => 
          match DEX_PROG.interface p iname with
            | None => None
            | Some itf => 
              match all_super_interfaces p n itf with
                | None => None
                | Some l' => Some (itf::l++l')
              end
          end
      end) 
    (DEX_CLASS.superInterfaces c)
    (Some nil).

  Lemma all_interfaces_correct : forall p n c l,
    all_interfaces p n c = Some l -> forall i I I',
      In i (DEX_CLASS.superInterfaces c) ->
      DEX_PROG.interface p i = Some I ->
      subinterface p I I' -> 
      In I l.
  Proof.
    unfold all_interfaces.
    intros p n c.
    generalize (@nil DEX_Interface).
    generalize (DEX_CLASS.superInterfaces c).
    induction l; simpl.
    intuition.
    intros l0; case_eq (DEX_PROG.interface p a).
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
     (*| CompatArray : forall length tp loc i a,
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

   Parameter new_typeof : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc:DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.

   Parameter new_typeof_old : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc loc':DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.

   Parameter new_defined_object_field : forall (h:t) (p:DEX_Program) 
      (cn:DEX_ClassName) (fs:DEX_FieldSignature) (f:DEX_Field) (loc:DEX_Location) (h':t), 
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DEX_DynamicField loc fs) = Some (init_field_value f).

   Parameter new_undefined_object_field : forall (h:t) (p:DEX_Program) 
      (cn:DEX_ClassName) (fs:DEX_FieldSignature) (loc:DEX_Location) (h':t),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DEX_DynamicField loc fs) = None.
 
  Parameter new_object_no_change : 
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) 
      (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     (forall (fs:DEX_FieldSignature), am <> (DEX_DynamicField loc fs)) ->
     get h' am = get h am.

 End DEX_HEAP.

Module DEX_Heap <: DEX_HEAP.
  Module DEX_Object.
    Record t : Type := Obj { class : DEX_ClassName; 
      fieldsval : DEX_MapFieldSignature.t DEX_value }.
    Definition get (o:t) := DEX_MapFieldSignature.get DEX_value o.(fieldsval).
    Definition op_get (o:option t) :=
      match o with
        | Some o => get o
        | None => fun f => None
      end.
    Definition op_update (f:DEX_FieldSignature) (v:DEX_value) (o:option t) : option t :=
      match o with
        | None => None
        | Some o => Some (Obj o.(class) (DEX_MapFieldSignature.update _ o.(fieldsval) f v))
      end.

    Definition init_fields :  list (DEX_ClassName*DEX_Field) -> DEX_MapFieldSignature.t DEX_value :=
      @fold_right (DEX_MapFieldSignature.t DEX_value) _
        (fun f m => DEX_MapFieldSignature.update _ m (fst f,DEX_FIELD.signature (snd f)) (init_field_value (snd f)))
        (DEX_MapFieldSignature.empty _).

    Definition default (c:DEX_Class) : t :=
      Obj
      (DEX_CLASS.name c) 
      (init_fields (List.map (fun f => (DEX_CLASS.name c,f)) 
        (DEX_CLASS.definedFields c))).

  End DEX_Object.

  Module LocMap := BinNatMap.

  Record t_ : Type := hp {
(*     statics : DEX_MapFieldSignature.t DEX_value; *)
    objects : LocMap.t DEX_Object.t;
    next_loc : DEX_Location
  }.
  Definition t : Type := t_.
  
  Inductive DEX_AdressingMode : Set :=
(*   | StaticField : FieldSignature -> AdressingMode *)
  | DEX_DynamicField : DEX_Location -> DEX_FieldSignature -> DEX_AdressingMode
  (* | ArrayElement : Location -> Z -> AdressingMode *).

  Inductive DEX_LocationType : Type :=
  | DEX_LocationObject : DEX_ClassName -> DEX_LocationType 
  (* | LocationArray : Int.t -> type -> Method*PC -> LocationType *).

   Definition typeof (h:t) (l:DEX_Location) : option (DEX_LocationType) :=
     match LocMap.get _ h.(objects) l with
       | Some o => Some (DEX_LocationObject o.(DEX_Object.class))
       | None => None
     end.

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : DEX_AdressingMode -> Prop :=
     (* | CompatStatic : forall f,
         Compat h (StaticField f) *)
     | CompatObject : forall cn loc f,
         typeof h loc = Some (DEX_LocationObject cn) ->
         Compat h (DEX_DynamicField loc f)
     (* | CompatArray : forall length tp loc i a,
         0 <= i < Int.toZ length ->
         typeof h loc = Some (LocationArray length tp a) ->
         Compat h (ArrayElement loc i) *).

   Definition check_compat (h:t) (am:DEX_AdressingMode) : bool :=
     match am with
       (* | StaticField f => true *)
       | DEX_DynamicField loc f =>
         match typeof h loc with
           | Some (DEX_LocationObject _) => true
           | _ => false
         end
       (* | ArrayElement loc i =>
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
         end *)
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
(*      constructor. *)
     case_eq (typeof h d); intros.
     destruct d1.
     econstructor; eauto.
     intro T; inversion T; subst.
     rewrite H1 in H; discriminate.   
  Qed.

  Definition get (h:t) (am:DEX_AdressingMode) : option DEX_value :=
    if check_compat h am then
      match am with
(*         | StaticField f =>  MapFieldSignature.get _ h.(statics) f *)
        | DEX_DynamicField l f => DEX_Object.op_get (LocMap.get _ h.(objects) l) f
(*         | ArrayElement l i => Array.op_get (LocMap.get _ h.(arrays) l) i  *)
      end
      else None.

  Definition update (h:t) (am:DEX_AdressingMode) (v:DEX_value) : t :=
    if check_compat h am then
      match am with
(*         | StaticField f => 
          hp
          (MapFieldSignature.update _ h.(statics) f v)
          h.(objects)
          h.(arrays)
          h.(next_loc) *)
        | DEX_DynamicField l f => 
          hp
(*           h.(statics) *)
          (LocMap.modify _ h.(objects) l (DEX_Object.op_update f v))
(*           h.(arrays)               *)
          h.(next_loc)
(*         | ArrayElement l i => 
          hp
          h.(statics)
          h.(objects)
          (LocMap.modify _ h.(arrays) l (Array.op_update i v))
          h.(next_loc)
 *)      end else h.     

   Definition Int_to_nat (i:Int.t) : option nat :=
     match Int.toZ i with
       | Zpos p => Some (nat_of_P p)
       | Z0 => Some O
       | Zneg _ => None
     end.

   Definition check_fresh (h:t) (l:DEX_Location) : bool :=
     match LocMap.get _ h.(objects) l with
       | Some _ => false
       | _ => true     
     end.

   Lemma check_fresh_correct : forall h l,
     check_fresh h l = true ->
       (LocMap.get _ h.(objects) l = None).
   Proof.
     unfold check_fresh; intros.
     destruct (LocMap.get _ (objects h) l); try discriminate.
     auto.
   Qed.

   Definition new (h:t) (p:DEX_Program) (ltp:DEX_LocationType) 
      : option (DEX_Location * t) :=
     if check_fresh h h.(next_loc) then
       match ltp with
         | DEX_LocationObject cn => 
           match DEX_PROG.class p cn with
             | None => None
             | Some c => 
                 Some
                 (h.(next_loc),
                   hp
(*                    h.(statics) *)
                   (LocMap.update _ h.(objects) h.(next_loc) (DEX_Object.default c))
(*                    h.(arrays)               *)
                   (Nsucc h.(next_loc)))
           end
       (* | LocationArray lgth tp a => 
             match Int_to_nat lgth with
               | None => None
               | Some n =>
                 Some
                 (h.(next_loc),
                   hp
                   h.(statics)
                   h.(objects)              
                   (LocMap.update _ h.(arrays) h.(next_loc) (Array.default lgth n tp a))
                   (Nsucc h.(next_loc)))
             end *)
       end
       else None.

   Lemma typeof_update_same : forall h loc am v,
     typeof (update h am v) loc = typeof h loc.
   Proof.
     unfold typeof, update; intros.
     generalize (check_compat_correct h am); destruct (check_compat h am); simpl; intros.
     destruct H; simpl.
     auto.
     destruct (DEX_PC_eq_dec loc0 loc); subst.
     unfold typeof in H.
     rewrite LocMap.get_modify1; auto.
     unfold LocMap.get in H.
     unfold LocMap.get in *.
     case_eq (BinNatMap_Base.get DEX_Object.t (objects h) loc); intros.
     rewrite H0 in H.
     reflexivity.
     rewrite H0 in H.
     reflexivity.
     
     rewrite LocMap.get_modify2; auto.
     reflexivity.
   Qed.

   Lemma Compat_update1 : forall h am am0 v0,
     Compat h am -> Compat (update h am0 v0) am.
   Proof.
     destruct 1; econstructor; eauto.
     rewrite typeof_update_same; eauto.
   Qed.

   Lemma Compat_update2 : forall h am am0 v0,
     Compat (update h am0 v0) am -> Compat h am.
   Proof.
     destruct 1; econstructor; eauto.
     rewrite typeof_update_same in H; eauto.
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
(*      rewrite DEX_MapFieldSignature.get_update1; auto. *)
     rewrite LocMap.get_modify1; auto.
     caseeq (BinNatMap_Base.get DEX_Object.t (objects h) loc); intros; simpl.
     unfold DEX_Object.get; simpl.
     rewrite DEX_MapFieldSignature.get_update1; auto.
     unfold typeof in H.
     replace LocMap.get with BinNatMap_Base.get in H; auto.
     rewrite H0 in H. discriminate.
     intuition.
   Qed.

   Lemma get_update_old : forall h am1 am2 v, am1<>am2 -> get (update h am1 v) am2 = get h am2.
   Proof.
     unfold get; intros.
     rewrite check_compat_update.
     unfold update; intros.
     generalize (check_compat_correct h am1); destruct (check_compat h am1); auto.
     (* destruct 1; *) intro H1; destruct H1; destruct am2; simpl; intros; auto.
(*      rewrite DEX_MapFieldSignature.get_update2; auto; congruence. *)

     destruct (DEX_PC_eq_dec loc d); subst.
     rewrite LocMap.get_modify1; auto.
     unfold typeof,LocMap.get in *.
     destruct (BinNatMap_Base.get DEX_Object.t (objects h) d); simpl in *.
     unfold DEX_Object.get; simpl.
     rewrite DEX_MapFieldSignature.get_update2; auto; congruence.
     auto.
     rewrite LocMap.get_modify2; auto.
   Qed.
     
   Lemma get_uncompat : forall h am, ~ Compat h am -> get h am = None.
   Proof.
     unfold get; intros.
     generalize (check_compat_correct h am);
       destruct (check_compat h am); intuition.
   Qed.

   Lemma new_fresh_location : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc:DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.
   Proof.
     unfold new; intros.
     generalize (check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     intros T. (* destruct (T (refl_equal _)). *)
(*      intros T; destruct (T (refl_equal _)); clear T. *)
     unfold typeof; destruct lt.
     destruct (DEX_PROG.class p d); try discriminate.
     inversion H. clear H; subst.
     rewrite T with (1:=(refl_equal _)). auto.
   Qed.
     
   Lemma new_typeof : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc:DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct lt.
     case_eq (DEX_PROG.class p d); intros.
     rewrite H0 in H.
     inversion H; clear H; subst.
     simpl.
     rewrite LocMap.get_update1.
     generalize (DEX_PROG.name_class_invariant1 _ _ _ H0).
     unfold DEX_Object.default; simpl.
     intros; congruence.
     rewrite H0 in H; discriminate.
   Qed.

   Lemma new_typeof_old : forall (h:t) (p:DEX_Program) (lt:DEX_LocationType) 
      (loc loc':DEX_Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (T (refl_equal _)) as [T1 T2]; clear T.
     destruct lt.
     destruct (DEX_PROG.class p d); try discriminate.
     inversion H; clear H; subst.
     simpl.
     rewrite LocMap.get_update2; auto.
   Qed.

   Lemma Compat_new_obj1 :
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) 
      (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     Compat h am -> Compat h' am.
   Proof.
     intros.
     destruct H0; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H); eauto.
     intro; subst.
     rewrite (@new_fresh_location _ _ _ _ _ H) in H0.
     discriminate.     
   Qed.

   Lemma Compat_new_obj2 :
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) 
      (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     (forall (fs:DEX_FieldSignature), am <> (DEX_DynamicField loc fs)) ->
     Compat h' am -> Compat h am.
   Proof.
     intros.
     destruct H1; econstructor; eauto.
     rewrite (@new_typeof_old _ _ _ _ loc0 _ H) in H1; eauto.
     intro; subst.
     elim (H0 f); auto.
   Qed.

   Lemma check_compat_new_obj :
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) 
      (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     (forall (fs:DEX_FieldSignature), am <> (DEX_DynamicField loc fs)) ->
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

   Parameter new_defined_object_field : forall (h:t) (p:DEX_Program) 
      (cn:DEX_ClassName) (fs:DEX_FieldSignature) (f:DEX_Field) (loc:DEX_Location) (h':t),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DEX_DynamicField loc fs) = Some (init_field_value f).

   Axiom new_undefined_object_field : forall (h:t) (p:DEX_Program) 
      (cn:DEX_ClassName) (fs:DEX_FieldSignature) (loc:DEX_Location) (h':t),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DEX_DynamicField loc fs) = None.
 
  Lemma new_object_no_change : 
     forall (h:t) (p:DEX_Program) (cn:DEX_ClassName) (loc:DEX_Location) (h':t) 
      (am:DEX_AdressingMode),
     new h p (DEX_LocationObject cn) = Some (loc,h') ->
     (forall (fs:DEX_FieldSignature), am <> (DEX_DynamicField loc fs)) ->
     get h' am = get h am.
   Proof.
     unfold get; intros.
     rewrite (@check_compat_new_obj _ _ _ _ _ _ H H0).
     assert (T:=check_compat_correct h am).
     destruct (check_compat h am); try reflexivity.
     unfold new in *.
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (DEX_PROG.class p cn); try discriminate.
     inversion H; clear H; subst.
     destruct T; simpl.
(*      reflexivity. *)
     rewrite LocMap.get_update2; auto.
     intro; subst; elim (H0 f); auto.
   Qed.

 End DEX_Heap.

Opaque DEX_Heap.update.

  Inductive DEX_ReturnVal : Set :=
   | Normal : option DEX_value -> DEX_ReturnVal.

 (** Domain of frames *)
 Module Type DEX_FRAME.
   Inductive t : Type := 
      make : DEX_Method -> DEX_PC -> DEX_Registers.t -> t.
 End DEX_FRAME.
 
 Module DEX_Frame.
   Inductive t : Type := 
      make : DEX_Method -> DEX_PC -> DEX_Registers.t -> t.
 End DEX_Frame.

 (** Domain of call stacks *)
 Module Type DEX_CALLSTACK.
   Definition t : Type := list DEX_Frame.t.
 End DEX_CALLSTACK.

 Module DEX_CallStack.
   Definition t : Type := list DEX_Frame.t.
 End DEX_CallStack.

 (** Domain of states *)
 Module Type DEX_STATE.
   Inductive t : Type := 
      normal : DEX_Heap.t -> DEX_Frame.t -> DEX_CallStack.t -> t.
   Definition get_sf  (s:t) : DEX_CallStack.t :=
     match s with
       normal _ _ sf => sf
     end.
   Definition get_m (s:t) : DEX_Method :=
     match s with
       normal _ (DEX_Frame.make m _ _)_ => m
     end.
 End DEX_STATE.

 Module DEX_State.
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
 End DEX_State.
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

End DEX_Dom.