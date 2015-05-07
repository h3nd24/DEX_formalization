(** * Bicolano: Semantic domains (interface implementation) *)

Require Export ImplemProgramWithMap.
Require Export Domain.

 
Ltac caseeq t := generalize (refl_equal t); pattern t at -1 in |- * ; case t.

(** All semantic domains and basic operation are encapsulated in a module signature *)

Module Dom <: SEMANTIC_DOMAIN.

 (** We depend on the choices done for program data structures *)
 Module Prog := ImplemProgramWithMap.Make.
 Import Prog.

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

 Inductive num : Set :=
   | I : Int.t -> num
   | B : Byte.t -> num
   | Sh : Short.t -> num.
 
 (** Location is the domain of adresses in the heap *)
 Definition Location : Set := N.
 Definition Location_dec : forall loc1 loc2:Location,{loc1=loc2}+{~loc1=loc2} :=
   (Aeq_Dec _ _ Neq_spec).

 Inductive value : Set :=
   | Num : num -> value
   | Ref: Location -> value
   | Null : value.

 Definition init_value (t:type) : value :=
    match t with
     | ReferenceType _ => Null
     | PrimitiveType _ => Num (I (Int.const 0))
    end.

 Definition init_field_value (f:Field) : value :=
   match FIELD.initValue f with
    | FIELD.Int z => Num (I (Int.const z))
    | FIELD.NULL => Null
    | FIELD.UNDEF => init_value (FIELDSIGNATURE.type (FIELD.signature f))
  end.
 
 (** Domain of local variables *)
 Module Type LOCALVAR.
   Parameter t : Type.
   Parameter get : t-> Var -> option value.
   Parameter update : t -> Var -> value -> t.
   Parameter ret : Var.
   Parameter ex : Var.
   Parameter get_update_new : forall l x v, get (update l x v) x = Some v.
   Parameter get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
 End LOCALVAR.

 Module MapVar <: MAP with Definition key := Var := BinNatMap.

 Module LocalVar <: LOCALVAR.
   Definition t := MapVar.t value.
   Definition get : t -> Var -> option value := @MapVar.get value.
   Definition update : t -> Var -> value -> t := @MapVar.update value.
   Definition ret := Npos (xO (xO (xO (xO (xO (xO (xO (xO 
     (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))).
   Definition ex := Npos (xI (xO (xO (xO (xO (xO (xO (xO 
     (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))).  
   Lemma get_update_new : forall l x v, get (update l x v) x = Some v.
   Proof. exact (MapVar.get_update1 value). Qed.
   Lemma get_update_old : forall l x y v,
     x<>y -> get (update l x v) y = get l y.
   Proof. 
    intros;refine (MapVar.get_update2 value _ _ _ _ _). 
    intro;apply H;subst;trivial.
  Qed.
  Definition empty := MapVar.empty value.
 End LocalVar.

 Fixpoint listvar2localvar_rec
    (l_ori:LocalVar.t) (n:nat) (lv:list Var) (l:LocalVar.t) {struct n}: LocalVar.t :=
   match n with 
   | O => l
   | S n =>
     match lv with 
     | nil => l
     | h :: t =>
       match LocalVar.get l_ori h with
       | None =>
         listvar2localvar_rec l_ori n t l
       | Some v => 
         listvar2localvar_rec l_ori n t (LocalVar.update l (N_toVar n) v)
       end
     end
   end.
 Definition listvar2localvar (l_ori:LocalVar.t) (n:nat) (lv:list Var)
   := listvar2localvar_rec l_ori n lv LocalVar.empty.
(*
 (* Domain of operand stacks *) 
 Module Type OPERANDSTACK.
   Definition t : Set := list value.
   Definition empty : t := nil.
   Definition push : value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option value := fun s n => nth_error s n.
 End OPERANDSTACK.

 Module OperandStack <: OPERANDSTACK.
   Definition t : Set := list value.
   Definition empty : t := nil.
   Definition push : value -> t -> t := fun v t => cons v t.
   Definition size : t -> nat := fun t  => length t .
   Definition get_nth : t -> nat -> option value := fun s n => nth_error s n.
  End OperandStack.

 (** Transfert fonction between operand stack and local variables necessary for invoke instructions *)
  
 Fixpoint stack2localvar_rec
    (os:OperandStack.t) (n:nat) (l:LocalVar.t) {struct n}: LocalVar.t :=
   match n with 
   | O => l
   | S n => 
      match os with
      | nil => l
      | v::os => 
         stack2localvar_rec os n (LocalVar.update l (N_toVar n) v)
      end
   end.
 Definition stack2localvar os n := stack2localvar_rec os n LocalVar.empty.

 Lemma stack2locvar_rec_prop1 :
   forall n l os x, (n <= Var_toN x)%nat -> 
     LocalVar.get (stack2localvar_rec  os n l) x = LocalVar.get l x.
 Proof.
  induction n;simpl;intros;trivial.
  destruct os;simpl;intros;trivial.
  assert (n <= Var_toN x)%nat. omega.
  rewrite IHn;trivial.
  unfold LocalVar.get, LocalVar.update;rewrite MapVar.get_update2;trivial.
  intro Heq;rewrite Heq in H.
  rewrite Var_toN_bij2 in H;omega.
 Qed.

 Lemma stack2locvar_prop1 :
   forall s n x, (n <= Var_toN x)%nat -> LocalVar.get (stack2localvar s n) x = None.
 Proof.
   unfold stack2localvar;intros.
   rewrite stack2locvar_rec_prop1;trivial.
   exact (MapVar.get_empty _ _).
 Qed.

 Lemma stack2locvar_rec_prop2 :
   forall n os l x, (Var_toN x < n)%nat ->
     (forall y, (Var_toN y < n)%nat -> LocalVar.get l y = None) ->
     LocalVar.get (stack2localvar_rec os n l) x = 
       OperandStack.get_nth os (n-(Var_toN x)-1)%nat.
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
   rewrite LocalVar.get_update_new.
   replace (S n - Var_toN x - 1)%nat with O;try omega.
   simpl;trivial.
   rewrite IHn;trivial.
   replace (S n - Var_toN x - 1)%nat with (S (n - Var_toN x - 1))%nat;try omega.
   simpl;trivial.
   intros;rewrite LocalVar.get_update_old.
   apply H0;omega.
   intro Heq;rewrite <-Heq in H2;rewrite Var_toN_bij2 in H2;omega.
  Qed.
   
 Lemma stack2locvar_prop2 :
   forall s n x, (Var_toN x < n)%nat ->
     LocalVar.get (stack2localvar s n) x = OperandStack.get_nth s (n-(Var_toN x)-1)%nat.
 Proof.
  unfold stack2localvar;intros;apply stack2locvar_rec_prop2;trivial.
  intros;exact (MapVar.get_empty _ _).
 Qed.
*)

 Fixpoint all_super_classes (p:Program) (c:Class) (n:nat) {struct n} : option (list Class) :=
   match n with
     | O => None
     | S n =>
       match CLASS.superClass c with
         | None => Some nil
         | Some super_name => 
           match PROG.class p super_name with
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
   PROG.defined_Class p c -> 
   forall c', subclass p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros c l; case_eq (CLASS.superClass c).
   intros c' H'.
   case_eq (PROG.class p c'); try (intros; discriminate).
   intros c'' H''.
   case_eq (all_super_classes p c'' n); try (intros; discriminate).
   intros.
   inv H0.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H0 as [c0 [T1 T2]].
   clear H2.
   inv T1.
   unfold PROG.defined_Class in *.
   assert (c0 = c'') by congruence.
   assert (c'=CLASS.name c'') by congruence.
   subst.
   clear H2 H3 H1.
   right; apply (IHn _ _ H H'' _ T2).

   intros.
   destruct (subclass_left _ _ _ H2); auto.
   destruct H3 as [c0 [T1 T2]].
   inv T1.
   congruence.
 Qed.

 Fixpoint all_super_interfaces (p:Program) (n:nat) {struct n} : 
                          Interface -> option (list Interface) :=
   match n with
     | O => fun _ => None
     | S n => fun c =>
       List.fold_left 
         (fun o iname =>
           match o with
             | None => None
             | Some l => 
               match PROG.interface p iname with
                 | None => None
                 | Some itf => 
                   match all_super_interfaces p n itf with
                     | None => None
                     | Some l' => Some (itf::l++l')
                   end
               end
           end) 
         (INTERFACE.superInterfaces c)
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
     (fun (o : option (list Interface)) (iname : InterfaceName) =>
      match o with
      | Some l6 => 
             match PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l6 ++ l')
                 | None => None (A:=list Interface)
                 end
             | None => None (A:=list Interface)
             end
      | None => None (A:=list Interface)
      end) l3 None=None.
Proof.
  induction l3; simpl; auto.
Qed.

Lemma all_super_interfaces_aux' : forall p n l0 l1 l2,
     fold_left
        (fun (o : option (list Interface)) (iname : InterfaceName) =>
         match o with
         | Some l =>
             match PROG.interface p iname with
             | Some itf =>
                 match all_super_interfaces p n itf with
                 | Some l' => Some (itf :: l ++ l')
                 | None => None (A:=list Interface)
                 end
             | None => None (A:=list Interface)
             end
         | None => None (A:=list Interface)
         end) l0 (Some l1) = Some l2 -> incl l1 l2.
Proof.
  induction l0; simpl.
  intros.
  inversion H; subst; intro; auto.
  destruct (PROG.interface p a); try (intros; discriminate).
  destruct (all_super_interfaces p n i); try (intros; discriminate).
  intros.
  assert (IH:=IHl0 _ _ H); clear H IHl0.
  repeat intro; apply IH.
  right; auto with datatypes.
  rewrite all_super_interfaces_aux; intros; discriminate.
  rewrite all_super_interfaces_aux; intros; discriminate.
 Qed.


 Definition all_super_interfaces_correct : forall p n c l,
   all_super_interfaces p n c = Some l ->
   PROG.defined_Interface p c -> 
   forall c', subinterface p c c' -> In c' (c::l).
 Proof.
   induction n; simpl.
   intros; discriminate.
   intros.
   destruct (subinterface_left _ _ _ H1); clear H1; auto.
   right; destruct H2 as [c0 [T1 T2]].
   inv T1.
   generalize dependent (Some (c::nil)).
   generalize dependent (INTERFACE.superInterfaces c).
   induction l0; simpl; intros.
   elim H3.
   destruct o; simpl in H; try discriminate.
   case_eq (PROG.interface p a); intros.   
   rewrite H4 in H.
   case_eq (all_super_interfaces p n i); intros.
   rewrite H5 in H.
   destruct H3; subst.
   unfold PROG.defined_Interface in *.
   assert (c0=i) by congruence; clear H4; subst.
   generalize (IHn _ _ H5 H2 _ T2).
   assert (T:=all_super_interfaces_aux' _ _ _ _ _ H).
   simpl; intros.
   apply T.
   destruct H3.
   left; auto.
   right; auto with datatypes.
   apply IHl0 with (Some (i :: l1 ++ l2)); auto.
   rewrite H5 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite H4 in H.
   rewrite all_super_interfaces_aux in H; discriminate.
   rewrite all_super_interfaces_aux in H; discriminate.
 Qed.

  Definition all_interfaces (p:Program) (n:nat) (c:Class) : option (list Interface) :=
    List.fold_left 
    (fun o iname =>
      match o with
        | None => None
        | Some l => 
          match PROG.interface p iname with
            | None => None
            | Some itf => 
              match all_super_interfaces p n itf with
                | None => None
                | Some l' => Some (itf::l++l')
              end
          end
      end) 
    (CLASS.superInterfaces c)
    (Some nil).

  Lemma all_interfaces_correct : forall p n c l,
    all_interfaces p n c = Some l -> forall i I I',
      In i (CLASS.superInterfaces c) ->
      PROG.interface p i = Some I ->
      subinterface p I I' -> 
      In I l.
  Proof.
    unfold all_interfaces.
    intros p n c.
    generalize (@nil Interface).
    generalize (CLASS.superInterfaces c).
    induction l; simpl.
    intuition.
    intros l0; case_eq (PROG.interface p a).
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

 Module Type HEAP.
   Parameter t : Type.

   Inductive AdressingMode : Set :=
     | StaticField : FieldSignature -> AdressingMode
     | DynamicField : Location -> FieldSignature -> AdressingMode
     | ArrayElement : Location -> Z -> AdressingMode.

   Inductive LocationType : Type :=
     | LocationObject : ClassName -> LocationType  
     | LocationArray : Int.t -> type -> Method*PC -> LocationType.
   (** (LocationArray length element_type) *)

   Parameter get : t -> AdressingMode -> option value.
   Parameter update : t -> AdressingMode -> value -> t.
   Parameter typeof : t -> Location -> option LocationType.   
     (** typeof h loc = None -> no object, no array allocated at location loc *)
   Parameter new : t -> Program -> LocationType -> option (Location * t).
     (** program is required to compute the size of the allocated element, i.e. to know
        the Class associated with a ClassName  *)

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : AdressingMode -> Prop :=
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

   Parameter new_fresh_location : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.

   Parameter new_typeof : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.

   Parameter new_typeof_old : forall (h:t) (p:Program) (lt:LocationType) (loc loc':Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.

   Parameter new_defined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (f:Field) (loc:Location) (h':t), 
     new h p (LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DynamicField loc fs) = Some (init_field_value f).

   Parameter new_undefined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (loc:Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DynamicField loc fs) = None.
 
  Parameter new_object_no_change : 
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:FieldSignature), am <> (DynamicField loc fs)) ->
     get h' am = get h am.

  Parameter new_valid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = Some (init_value tp).

  Parameter new_unvalid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     ~ 0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = None.

  Parameter new_array_no_change : 
     forall (h:t) (p:Program) (length:Int.t) (tp:type) a (loc:Location) (h':t) (am:AdressingMode),
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

 End HEAP.

Module Heap <: HEAP.
  Module Object.
    Record t : Type := Obj { class : ClassName; fieldsval : MapFieldSignature.t value }.
    Definition get (o:t) := MapFieldSignature.get value o.(fieldsval).
    Definition op_get (o:option t) :=
      match o with
        | Some o => get o
        | None => fun f => None
      end.
    Definition op_update (f:FieldSignature) (v:value) (o:option t) : option t :=
      match o with
        | None => None
        | Some o => Some (Obj o.(class) (MapFieldSignature.update _ o.(fieldsval) f v))
      end.

    Definition init_fields :  list (ClassName*Field) -> MapFieldSignature.t value :=
      @fold_right (MapFieldSignature.t value) _
        (fun f m => MapFieldSignature.update _ m (fst f,FIELD.signature (snd f)) (init_field_value (snd f)))
        (MapFieldSignature.empty _).

    Definition default (c:Class) : t :=
      Obj
      (CLASS.name c) 
      (init_fields (List.map (fun f => (CLASS.name c,f)) (CLASS.definedFields c))).

  End Object.
  Module Array.
    Record t : Type := Arr {
      length : Int.t;
      element_type : type; 
      elements : BinNatMap.t value;
      creation_point : Method * PC
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
            | Lt => BinNatMap.get value a.(elements) n
            | _ => None
          end
        | None => None
      end.
    Definition op_get (a:option (t)) :=
      match a with
        | Some a => get a
        | None => fun i => None
      end.
    Definition op_update (i:Z) (v:value) (a:option t) : option t :=
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

    Fixpoint init_array_rec (n:nat) (v:value) {struct n} : BinNatMap.t value :=
      match n with 
        | O => BinNatMap.empty _
        | S p => BinNatMap.update _ (init_array_rec p v) (N_of_nat p) v
      end.

    Definition default (lgth:Int.t) (n:nat) (tp:type) (a:Method*PC): t:=
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


  End Array.

  Module LocMap := BinNatMap.

  Record t_ : Type := hp {
    statics : MapFieldSignature.t value;
    objects : LocMap.t Object.t;
    arrays : LocMap.t Array.t;
    next_loc : Location
  }.
  Definition t : Type := t_.
  
  Inductive AdressingMode : Set :=
  | StaticField : FieldSignature -> AdressingMode
  | DynamicField : Location -> FieldSignature -> AdressingMode
  | ArrayElement : Location -> Z -> AdressingMode.

  Inductive LocationType : Type :=
  | LocationObject : ClassName -> LocationType 
  | LocationArray : Int.t -> type -> Method*PC -> LocationType.

   Definition typeof (h:t) (l:Location) : option (LocationType) :=
     match LocMap.get _ h.(objects) l with
       | Some o => Some (LocationObject o.(Object.class))
       | None =>
         match LocMap.get _ h.(arrays) l with
           | Some a => Some (LocationArray a.(Array.length) a.(Array.element_type) a.(Array.creation_point))
           | None => None
         end
     end.

   (** Compatibility between a heap and an adress *)
   Inductive Compat (h:t) : AdressingMode -> Prop :=
     | CompatStatic : forall f,
         Compat h (StaticField f)
     | CompatObject : forall cn loc f,
         typeof h loc = Some (LocationObject cn) ->
         Compat h (DynamicField loc f)
     | CompatArray : forall length tp loc i a,
         0 <= i < Int.toZ length ->
         typeof h loc = Some (LocationArray length tp a) ->
         Compat h (ArrayElement loc i).

   Definition check_compat (h:t) (am:AdressingMode) : bool :=
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
     case_eq (typeof h l); intros.
     destruct l0.
     econstructor; eauto.
     intro T; inversion T; subst.
     rewrite H1 in H; discriminate.
     intro T; inversion T; subst.
     rewrite H1 in H; discriminate.
     case_eq (typeof h l); intros.
     destruct l0.
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

  Definition get (h:t) (am:AdressingMode) : option value :=
    if check_compat h am then
      match am with
        | StaticField f =>  MapFieldSignature.get _ h.(statics) f
        | DynamicField l f => Object.op_get (LocMap.get _ h.(objects) l) f
        | ArrayElement l i => Array.op_get (LocMap.get _ h.(arrays) l) i 
      end
      else None.
  Definition update (h:t) (am:AdressingMode) (v:value) : t :=
    if check_compat h am then
      match am with
        | StaticField f => 
          hp
          (MapFieldSignature.update _ h.(statics) f v)
          h.(objects)
          h.(arrays)
          h.(next_loc)
        | DynamicField l f => 
          hp
          h.(statics)
          (LocMap.modify _ h.(objects) l (Object.op_update f v))
          h.(arrays)              
          h.(next_loc)
        | ArrayElement l i => 
          hp
          h.(statics)
          h.(objects)
          (LocMap.modify _ h.(arrays) l (Array.op_update i v))
          h.(next_loc)
      end else h.     

   Definition Int_to_nat (i:Int.t) : option nat :=
     match Int.toZ i with
       | Zpos p => Some (nat_of_P p)
       | Z0 => Some O
       | Zneg _ => None
     end.

   Definition check_fresh (h:t) (l:Location) : bool :=
     match LocMap.get _ h.(objects) l with
       | Some _ => false
       | _ =>      
         match LocMap.get _ h.(arrays) l with
           | Some _ => false
           | _ => true
         end
     end.

   Lemma check_fresh_correct : forall h l,
     check_fresh h l = true ->
       (LocMap.get _ h.(objects) l = None
        /\ LocMap.get _ h.(arrays) l = None).
   Proof.
     unfold check_fresh; intros.
     destruct (LocMap.get _ (objects h) l); try discriminate.
     destruct (LocMap.get _ (arrays h) l); try discriminate.
     auto.
   Qed.

   Definition new (h:t) (p:Program) (ltp:LocationType) : option (Location * t) :=
     if check_fresh h h.(next_loc) then
       match ltp with
         | LocationObject cn => 
           match PROG.class p cn with
             | None => None
             | Some c => 
                 Some
                 (h.(next_loc),
                   hp
                   h.(statics)
                   (LocMap.update _ h.(objects) h.(next_loc) (Object.default c))
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
                   (LocMap.update _ h.(arrays) h.(next_loc) (Array.default lgth n tp a))
                   (Nsucc h.(next_loc)))
             end
       end
       else None.

   Lemma pos_Ncase : forall i:Z,
     0<=i -> exists n, Array.Ncase i = Some n.
   Proof.
     destruct i; simpl; intros; eauto.
     elim H; auto.
   Qed.

   Lemma case_Ncase : forall i:Z,
     Array.Ncase i = None \/
     exists n, Array.Ncase i = Some n /\ 0<=i.
   Proof.
     destruct i; simpl; eauto with zarith.
   Qed.

   Lemma Ncase_inj : forall i j,
     Array.Ncase i = Array.Ncase j -> Array.Ncase i <> None -> i = j.
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
     rewrite LocMap.get_modify1; auto.
     unfold LocMap.get in H.
     unfold LocMap.get in *.
     case_eq (BinNatMap_Base.get Object.t (objects h) loc); intros.
     rewrite H0 in H.
     reflexivity.
     rewrite H0 in H.
     reflexivity.
     
     rewrite LocMap.get_modify2; auto.

     destruct (PC_eq_dec loc0 loc); subst.
     rewrite LocMap.get_modify1; auto.
     unfold typeof in *.
     destruct (LocMap.get Object.t (objects h) loc); try reflexivity.
     unfold LocMap.get in *.
     case_eq (BinNatMap_Base.get _ (arrays h) loc); simpl; intros.
     rewrite H1 in H0.
     inversion H0; clear H0; subst.
     elim (@pos_Ncase i); [intros n H2|omega].
     rewrite H2.
     rewrite bounded_compare; try omega.
     reflexivity.
     reflexivity.
     rewrite LocMap.get_modify2; auto.

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
     rewrite MapFieldSignature.get_update1; auto.
     rewrite LocMap.get_modify1; auto.
     caseeq (BinNatMap_Base.get Object.t (objects h) loc); intros; simpl.
     unfold Object.get; simpl.
     rewrite MapFieldSignature.get_update1; auto.
     unfold typeof in H.
     replace LocMap.get with BinNatMap_Base.get in H; auto.
     rewrite H0 in H.
     destruct (BinNatMap_Base.get (Array.t) (arrays h) loc); discriminate.

     unfold typeof in H0.
     replace LocMap.get with BinNatMap_Base.get in *; auto.
     caseeq (BinNatMap_Base.get Object.t (objects h) loc); intros; simpl.
     rewrite H1 in H0.
     inversion H0.
     rewrite H1 in *.
     rewrite LocMap.get_modify1; auto.
     unfold Array.op_update, Array.op_get, Array.get.
     caseeq (BinNatMap_Base.get _ (arrays h) loc); intros.
     rewrite H2 in H0.
     injection H0; intros; subst; clear H0.
     destruct (Array.elements t0).
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
     rewrite MapFieldSignature.get_update2; auto; congruence.

     destruct (PC_eq_dec loc l); subst.
     rewrite LocMap.get_modify1; auto.
     unfold typeof,LocMap.get in *.
     destruct (BinNatMap_Base.get Object.t (objects h) l); simpl in *.
     unfold Object.get; simpl.
     rewrite MapFieldSignature.get_update2; auto; congruence.
     auto.
     rewrite LocMap.get_modify2; auto.

     destruct (PC_eq_dec loc l); subst.
     unfold typeof in H1.
     caseeq (LocMap.get _ (objects h) l); intros; simpl; auto.
     rewrite H2 in H1; inversion H1.
     rewrite H2 in H1.
     unfold LocMap.get in *.
     rewrite LocMap.get_modify1; auto.
     clear H2.
     caseeq (BinNatMap_Base.get Array.t (arrays h) l); intros; simpl; auto.
     rewrite H2 in H1; try discriminate.
     inversion H1; subst; clear H1.
     destruct (case_Ncase i).
     rewrite H1; auto.
     destruct H1 as [n [H1 H3]]; rewrite H1.
     destruct (case_compare i (Int.toZ (Array.length t0))).
     destruct H4 as [H4 H5]; rewrite H4.
     simpl.
     unfold Array.get.
     destruct (case_Ncase z).
     rewrite H6; auto.
     destruct H6 as [n' [H6 H7]]; rewrite H6; simpl.
     destruct (case_compare z (Int.toZ (Array.length t0))).
     destruct H8 as [H8 H9]; rewrite H8.
     rewrite BinNatMap.get_update2; auto.
     intro; assert (i=z) by (apply Ncase_inj; congruence).
     elim H; congruence.
     destruct H8; rewrite H8; auto.
     destruct H4; rewrite H4; auto.
     rewrite LocMap.get_modify2; auto.
   Qed.
     
   Lemma get_uncompat : forall h am, ~ Compat h am -> get h am = None.
   Proof.
     unfold get; intros.
     generalize (check_compat_correct h am);
       destruct (check_compat h am); intuition.
   Qed.

   Lemma new_fresh_location : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h loc = None.
   Proof.
     unfold new; intros.
     generalize (check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     intros T; destruct (T (refl_equal _)); clear T.
     unfold typeof; destruct lt.
     destruct (PROG.class p c); try discriminate.
     inversion H; clear H; subst.
     rewrite H0; rewrite H1; reflexivity.
     destruct (Int_to_nat t0); try discriminate.
     inversion H; clear H; subst.
     rewrite H0; rewrite H1; reflexivity.
   Qed.
     
   Lemma new_typeof : forall (h:t) (p:Program) (lt:LocationType) (loc:Location) (h':t),
     new h p lt = Some (loc,h') ->
     typeof h' loc = Some lt.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct lt.
     case_eq (PROG.class p c); intros.
     rewrite H0 in H.
     inversion H; clear H; subst.
     simpl.
     rewrite LocMap.get_update1.
     generalize (PROG.name_class_invariant1 _ _ _ H0).
     unfold Object.default; simpl.
     intros; congruence.
     rewrite H0 in H; discriminate.
     destruct (Int_to_nat t0); inversion H; clear H; subst; simpl.
     destruct (T (refl_equal _)) as [T1 T2]; clear T.
     rewrite T1.
     rewrite LocMap.get_update1.
     reflexivity.
   Qed.

   Lemma new_typeof_old : forall (h:t) (p:Program) (lt:LocationType) (loc loc':Location) (h':t),
     new h p lt = Some (loc,h') ->
     loc <> loc' ->
     typeof h' loc' = typeof h loc'.
   Proof.
     unfold new, typeof; intros.
     assert (T:=check_fresh_correct h (next_loc h)).
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (T (refl_equal _)) as [T1 T2]; clear T.
     destruct lt.
     destruct (PROG.class p c); try discriminate.
     inversion H; clear H; subst.
     simpl.
     rewrite LocMap.get_update2; auto.
     destruct (Int_to_nat t0); inversion H; clear H; subst; simpl.
     rewrite LocMap.get_update2; auto.
   Qed.

   Lemma Compat_new_obj1 :
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
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
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:FieldSignature), am <> (DynamicField loc fs)) ->
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
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:FieldSignature), am <> (DynamicField loc fs)) ->
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
     forall (h:t) (p:Program) i tp a (loc:Location) (h':t) (am:AdressingMode),
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
     forall (h:t) (p:Program) i tp a (loc:Location) (h':t) (am:AdressingMode),
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
     forall (h:t) (p:Program) i tp a (loc:Location) (h':t) am,
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

   Parameter new_defined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (f:Field) (loc:Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     is_defined_field p cn fs f ->
     get h' (DynamicField loc fs) = Some (init_field_value f).

   Axiom new_undefined_object_field : forall (h:t) (p:Program) (cn:ClassName) (fs:FieldSignature) (loc:Location) (h':t),
     new h p (LocationObject cn) = Some (loc,h') ->
     ~ defined_field p cn fs ->
     get h' (DynamicField loc fs) = None.
 
  Lemma new_object_no_change : 
     forall (h:t) (p:Program) (cn:ClassName) (loc:Location) (h':t) (am:AdressingMode),
     new h p (LocationObject cn) = Some (loc,h') ->
     (forall (fs:FieldSignature), am <> (DynamicField loc fs)) ->
     get h' am = get h am.
   Proof.
     unfold get; intros.
     rewrite (@check_compat_new_obj _ _ _ _ _ _ H H0).
     assert (T:=check_compat_correct h am).
     destruct (check_compat h am); try reflexivity.
     unfold new in *.
     destruct (check_fresh h (next_loc h)); try discriminate.
     destruct (PROG.class p cn); try discriminate.
     inversion H; clear H; subst.
     destruct T; simpl.
     reflexivity.
     rewrite LocMap.get_update2; auto.
     intro; subst; elim (H0 f); auto.
     auto.
   Qed.

  Lemma new_valid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
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
     rewrite LocMap.get_update1.
     simpl.
     unfold Array.default; simpl.
     unfold Array.get; simpl.
     unfold Array.Ncase.
     rewrite H1.
     rewrite bounded_compare.
     destruct i.
     apply Array.get_init_array_rec. 
     simpl.
     apply lt_O_nat_of_P.
     apply Array.get_init_array_rec. 
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

  Lemma new_unvalid_array_index : forall (h:t) (p:Program) (length:Int.t) (tp:type) a (i:Z) (loc:Location) (h':t),
     new h p (LocationArray length tp a) = Some (loc,h') ->
     ~ 0 <= i < Int.toZ length ->
     get h' (ArrayElement loc i) = None.
  Proof.
     unfold get; intros.
     assert (T:=check_compat_correct h' (ArrayElement loc i)).
     destruct (check_compat h' (ArrayElement loc i)).
     unfold new in *; simpl.
     destruct (check_fresh h (next_loc h)); try discriminate.
     unfold Array.op_get, Array.get.
     inversion T; clear T; subst.
     case_eq (Int_to_nat length); intros.
     rewrite H1 in H; try discriminate.
     inversion H; clear H; subst.
     simpl.
     rewrite LocMap.get_update1.
     elim (@pos_Ncase  i); [intros|omega].
     rewrite H.
     simpl.
     unfold typeof in H4.
     simpl in H4.
     destruct (LocMap.get Object.t (objects h) (next_loc h)); try discriminate.
     rewrite LocMap.get_update1 in H4.
     inversion H4; clear H4; subst.
     elim H0; auto.
     rewrite H1 in H; discriminate.
     reflexivity.
   Qed.

  Lemma new_array_no_change : 
     forall (h:t) (p:Program) (length:Int.t) (tp:type) a (loc:Location) (h':t) (am:AdressingMode),
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
     rewrite LocMap.get_update2; auto.
     intro; subst; elim (H0 i); auto.
   Qed.

 End Heap.

Opaque Heap.update.
  Inductive ReturnVal : Set :=
   | Normal : option value -> ReturnVal
   | Exception : Location -> ReturnVal.

 (** Domain of frames *)
 Module Type FRAME.
   Inductive t : Type := 
      make : Method -> PC -> (*OperandStack.t ->*) LocalVar.t -> t.
 End FRAME.
 
 Module Frame.
   Inductive t : Type := 
      make : Method -> PC -> (*OperandStack.t ->*) LocalVar.t -> t.
 End Frame.

 (** Domain of call stacks *)
 Module Type CALLSTACK.
   Definition t : Type := list Frame.t.
 End CALLSTACK.

 Module CallStack.
   Definition t : Type := list Frame.t.
 End CallStack.

 Module Type EXCEPTION_FRAME.
   Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
 End EXCEPTION_FRAME.
 Module ExceptionFrame.
    Inductive t : Type := 
      make : Method -> PC -> Location -> LocalVar.t -> t.
  End ExceptionFrame.
 
 (** Domain of states *)
 Module Type STATE.
   Inductive t : Type := 
      normal : Heap.t -> Frame.t -> CallStack.t -> t
    | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t.
   Definition get_sf  (s:t) : CallStack.t :=
     match s with
       normal _ _ sf => sf
     | exception _ _ sf => sf
     end.
   Definition get_m (s:t) : Method :=
     match s with
       normal _ (Frame.make m _ _)_ => m
     | exception _ (ExceptionFrame.make m _ _ _) _ => m
     end.
 End STATE.

 Module State.
  Inductive t : Type := 
      normal : Heap.t -> Frame.t -> CallStack.t -> t
    | exception : Heap.t -> ExceptionFrame.t -> CallStack.t -> t.
   Definition get_sf (s:t) : CallStack.t :=
     match s with
       normal _ _ sf => sf
     | exception _ _ sf => sf
     end.
   Definition get_m (s:t) : Method :=
     match s with
       normal _ (Frame.make m _ _)_ => m
     | exception _ (ExceptionFrame.make m _ _ _) _ => m
     end.
 End State.
 (** Some notations *)
 Notation St := State.normal.
 Notation StE := State.exception.
 Notation Fr := Frame.make.
 Notation FrE := ExceptionFrame.make.

  (** compatibility between ArrayKind and type *) 
  Inductive compat_ArrayKind_type : ArrayKind -> type -> Prop :=
    | compat_ArrayKind_type_ref : forall rt,
        compat_ArrayKind_type Aarray (ReferenceType rt)
    | compat_ArrayKind_type_int : 
        compat_ArrayKind_type Iarray (PrimitiveType INT)
    | compat_ArrayKind_type_byte : 
        compat_ArrayKind_type Barray (PrimitiveType BYTE)
    | compat_ArrayKind_type_bool : 
        compat_ArrayKind_type Barray (PrimitiveType BOOLEAN)
    | compat_ArrayKind_type_short : 
        compat_ArrayKind_type Sarray (PrimitiveType SHORT).

  Inductive isReference : value -> Prop :=
  | isReference_null : isReference Null
  | isReference_ref : forall loc, isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : ValKind -> value -> Prop :=
    | compat_ValKind_value_ref : forall v,
        isReference v -> compat_ValKind_value Aval v
    | compat_ValKind_value_int : forall n,
        compat_ValKind_value Ival (Num (I n)).

  (** compatibility between ArrayKind and value *) 
  Inductive compat_ArrayKind_value : ArrayKind -> value -> Prop :=
    | compat_ArrayKind_value_ref : forall v,
        isReference v -> compat_ArrayKind_value Aarray v
    | compat_ArrayKind_value_int : forall n,
        compat_ArrayKind_value Iarray (Num (I n))
    | compat_ArrayKind_value_byte : forall n,
        compat_ArrayKind_value Barray (Num (B n))
    | compat_ArrayKind_value_short : forall n,
        compat_ArrayKind_value Sarray (Num (Sh n)).

  (* convert a value to be pushed on the stack *)
  Definition conv_for_stack (v:value) : value :=
    match v with
    | Num (B b) => Num (I (b2i b))
    | Num (Sh s) => Num (I (s2i s))
    | _ => v
    end.

  (* convert a value to be store in an array *)
  Definition conv_for_array (v:value) (t:type) : value :=
    match v with
    | Ref loc => v
    | Num (I i) =>
       match t with
         ReferenceType _ => v (* impossible case *)
       | PrimitiveType INT => v
       | PrimitiveType BOOLEAN => Num (B (i2bool i))
       | PrimitiveType BYTE => Num (B (i2b i))
       | PrimitiveType SHORT => Num (Sh (i2s i))         
       end
    | _ => v (* impossible case *)
    end.

  (** [assign_compatible_num source target] holds if a numeric value [source] can be 
    assigned to a variable of type [target]. This point is not clear in the JVM spec. *)
  Inductive assign_compatible_num : num -> primitiveType -> Prop :=
   | assign_compatible_int_int : forall i, assign_compatible_num (I i) INT
   | assign_compatible_short_int : forall sh, assign_compatible_num (Sh sh) INT
   | assign_compatible_byte_int : forall b, assign_compatible_num (B b) INT
   | assign_compatible_short_short : forall sh, assign_compatible_num (Sh sh) SHORT
   | assign_compatible_byte_byte : forall b, assign_compatible_num (B b) BYTE
   | assign_compatible_byte_boolean : forall b, assign_compatible_num (B b) BOOLEAN.

  (** [assign_compatible h source target] holds if a value [source] can be 
    assigned to a variable of type [target] *)
  Inductive assign_compatible (p:Program) (h:Heap.t) : value -> type -> Prop :=
   | assign_compatible_null : forall t, assign_compatible p h Null (ReferenceType t)
   | assign_compatible_ref_object_val : forall (loc:Location) (t:refType) (cn:ClassName), 
       Heap.typeof h loc = Some (Heap.LocationObject cn) ->
       compat_refType p (ClassType cn) t ->
       assign_compatible p h (Ref loc) (ReferenceType t)
   | assign_compatible_ref_array_val : forall (loc:Location) (t:refType) (length:Int.t) (tp:type) a, 
       Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
       compat_refType p (ArrayType tp) t ->
       assign_compatible p h (Ref loc) (ReferenceType t)
   | assign_compatible_num_val : forall (n:num) (t:primitiveType),
       assign_compatible_num n t -> assign_compatible p h (Num n) (PrimitiveType t).

  Inductive SemCompRef : CompRef -> value -> value -> Prop :=
  | SemCompRef_eq : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 = v2 ->
     (****************************************************)
          SemCompRef EqRef v1 v2
  | SemCompRef_ne : forall v1 v2,
       isReference v1 -> isReference v2 -> v1 <> v2 ->
     (****************************************************)
          SemCompRef NeRef v1 v2.

  Definition SemCompInt (cmp:CompInt) (z1 z2: Z) : Prop :=
    match cmp with
      EqInt =>  z1=z2
    | NeInt => z1<>z2
    | LtInt => z1<z2
    | LeInt => z1<=z2
    | GtInt => z1>z2
    | GeInt => z1>=z2
    end.

  Definition SemBinopInt (op:BinopInt) (i1 i2:Int.t) : Int.t :=
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
(*
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
End Dom.

