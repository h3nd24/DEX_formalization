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

 Inductive DEX_num : Set :=
   | I : Int.t -> DEX_num
   | B : Byte.t -> DEX_num
   | Sh : Short.t -> DEX_num.

 Inductive DEX_value : Set :=
   | Num : DEX_num -> DEX_value.

 Definition init_value (t:DEX_type) : DEX_value :=
    match t with
     | DEX_PrimitiveType _ => Num (I (Int.const 0))
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
      normal : DEX_Frame.t -> DEX_CallStack.t -> t.
   Definition get_sf  (s:t) : DEX_CallStack.t :=
     match s with
       normal _ sf => sf
     end.
   Definition get_m (s:t) : DEX_Method :=
     match s with
       normal (DEX_Frame.make m _ _)_ => m
     end.
 End DEX_STATE.

 Module DEX_State.
  Inductive t : Type := 
      normal : DEX_Frame.t -> DEX_CallStack.t -> t.
   Definition get_sf (s:t) : DEX_CallStack.t :=
     match s with
       normal _ sf => sf
     end.
   Definition get_m (s:t) : DEX_Method :=
     match s with
       normal (DEX_Frame.make m _ _)_ => m
     end.
 End DEX_State.
 (** Some notations *)
 Notation St := DEX_State.normal.
 Notation Fr := DEX_Frame.make.

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : DEX_ValKind -> DEX_value -> Prop :=
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
  Inductive assign_compatible (p:DEX_Program) : DEX_value -> DEX_type -> Prop :=
   | assign_compatible_num_val : forall (n:DEX_num) (t:DEX_primitiveType),
       assign_compatible_num n t -> assign_compatible p (*h*) (Num n) (DEX_PrimitiveType t).

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