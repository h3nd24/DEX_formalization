(** * Annotated.v: Syntax of JVM program extended with security type annotations *)

(* Hendra: Added annotation for DEX program as well, but removed exceptions *)
Require Export LoadBicolano.
Require Export Level.
Require Export Axioms.

Import DEX_BigStep.DEX_BigStep.DEX_Dom.DEX_Prog.
(* Hendra 11082016 focus on DEX I - Import JVM_BigStep.JVM_BigStep.JVM_Dom.JVM_Prog. *)

Record DEX_sign : Set := make_DEX_sign {
  DEX_lvt : DEX_Reg -> L.t;
  DEX_resType : option L.t;
  (* DEX resExceptionType : ClassName -> L.t;*)
  (*DEX_heapEffect : L.t*)
}.

(* Hendra 11082016 focus on DEX I
Record JVM_sign : Set := make_JVM_sign {
  JVM_lvt : JVM_Var -> L.t';
  JVM_resType : option L.t';
  (* DEX resExceptionType : ClassName -> L.t;*)
  JVM_heapEffect : L.t
}.
*)

Definition DEX_default_signature : DEX_sign :=
  make_DEX_sign
    (fun _ => (*L.Simple*)L.bot)
    None
    (* DEX (fun _ => L.bot) *)
    (*L.bot*).    

(* Hendra 11082016 focus on DEX I
Definition JVM_default_signature : JVM_sign :=
  make_JVM_sign
    (fun _ => L.Simple L.bot)
    None
    (* DEX (fun _ => L.bot) *)
    L.bot. 
*)

Record DEX_ExtendedProgram : Type := DEX_extP {
  DEX_prog :> DEX_Program;
  DEX_newArT : DEX_Method * DEX_PC -> L.t';
  DEX_static_signature : DEX_ShortMethodSignature -> DEX_sign;
  DEX_virtual_signature : DEX_ShortMethodSignature -> L.t -> DEX_sign;
  DEX_ft : DEX_FieldSignature -> L.t';
  locR : DEX_ShortMethodSignature -> list DEX_Reg
}.

(* Hendra 11082016 focus on DEX I
Record JVM_ExtendedProgram : Type := JVM_extP {
  JVM_prog :> JVM_Program;
  JVM_newArT : JVM_Method * JVM_PC -> L.t';
  JVM_static_signature : JVM_ShortMethodSignature -> JVM_sign;
  JVM_virtual_signature : JVM_ShortMethodSignature -> L.t -> JVM_sign;
  JVM_ft : JVM_FieldSignature -> L.t'
}.
*)

(* DEX
Definition throwableBy (p:Program) := PROG.throwableBy p.
*)

(*
Definition static_signature (p:ExtendedProgram) mid : sign :=
  match MapShortMethSign.get _ p.(signatures) mid with
    | Some sgn => sgn
    | None => default_signature
  end.

Definition  virtual_signature (p:ExtendedProgram) mid (k:L.t) : sign :=
  static_signature p mid.
*)

(* Hendra 11082016 focus on DEX I
Definition well_formed_lookupswitch m := forall pc def l i o1 o2,
  instructionAt m pc = Some (JVM_Lookupswitch def l) ->
  In (i, o1) l -> In (i, o2) l -> o1=o2.
*)

(* DEX
Definition np := (javaLang,NullPointerException).
Definition cc := (javaLang,ClassCastException).
Definition ae := (javaLang,ArithmeticException).
Definition nase := (javaLang,NegativeArraySizeException).
Definition iob := (javaLang,ArrayIndexOutOfBoundsException).
Definition ase := (javaLang,ArrayStoreException).
*)

Definition DEX_tag := option DEX_ClassName.
(* Hendra 11082016 focus on DEX I - Definition JVM_tag := option JVM_ClassName. *)

(* Hendra 15082016 - focus on DEX I - Definition TypeStack := list L.t'.*)

Module VarMap := BinNatMap.
Definition TypeRegisters := VarMap.t L.t(* focus on DEX I'*).

(* Hendra 11082016 focus on DEX I
Fixpoint base_rt_rec (max_locals:nat) (lvt:JVM_Var->L.t') (rt:TypeRegisters) 
  : TypeRegisters := 
  match max_locals with
    | O => rt
    | S n => VarMap.update _ (base_rt_rec n lvt rt) (N_toVar n) (lvt (N_toVar n))
  end.


Definition base_rt (max_locals:nat) (lvt:JVM_Var->L.t') : TypeRegisters :=
  base_rt_rec (max_locals) (lvt) (VarMap.empty L.t').

Fixpoint translate_st_rt_rec (st:TypeStack) (max_locals:nat) (rt:VarMap.t L.t')
  : TypeRegisters :=
  match st with
    | nil => rt
    | h :: t => VarMap.update _ (translate_st_rt_rec (t) (max_locals) (rt))
                  (N_toVar (length st) + N_toVar max_locals - 1)%N h
(*
                let newRT := VarMap.update _ rt (N_toVar (length st) + 
                    N_toVar max_locals - 1)%N h in
                translate_st_rt_rec (t) (max_locals) (newRT)
*)
  end.

Definition translate_st_rt (st:TypeStack) (max_locals:nat) 
  (lvt:JVM_Var -> L.t') : TypeRegisters :=
  translate_st_rt_rec (st) (max_locals) (base_rt (max_locals) (lvt)).
*)

Module MapAddress' := MapPair_Base MapN MapN.
Module MapAddress := Map_Of_MapBase MapAddress'. (* for intermediate compilation *)

Definition update_op (rt:TypeRegisters) (key:VarMap.key) (k:option L.t(*'*)) :=
  match k with
    | Some v => BinNatMap.update _ rt key v
    | None => rt
  end.

(* Hendra 11082016 focus on DEX I
Definition compat_type_st_lvt (s:JVM_sign) (st:TypeStack) (n:nat) : Prop :=
  forall x, ((Var_toN x)<n)%nat -> exists k,
    nth_error st (n-(Var_toN x)-1)%nat = Some k /\
    L.leql' k (JVM_lvt s x).
*)
Fixpoint In_test (a:DEX_Reg) (l:list DEX_Reg) {struct l} :=
  match l with
    | nil => false
    | h::t => Neq h a || In_test a t
  end.

Lemma In_In_test: forall a l, In a l <-> In_test a l = true.
Proof.
  intros. split; intros.
  (* -> *)
  induction l.
  inversion H.
  apply in_inv in H. inversion H; auto. 
    simpl. destruct (Neq a0 a) eqn:Heq; auto.
    generalize (Neq_spec a0 a); intros. rewrite Heq in H1; contradiction.
    simpl. apply IHl in H0; rewrite H0; auto. apply orb_true_r.
  (* <- *)
  induction l. inversion H.
  inversion H.
  apply orb_prop in H1. inversion H1.
    generalize (Neq_spec a0 a); intros Heq; rewrite H0 in Heq. 
    rewrite Heq; apply in_eq.
    apply IHl in H0.
    apply in_cons; eauto.
Qed. 
      
Fixpoint make_rt_from_lvt_rec (s:DEX_sign) (p:list DEX_Reg) (valid_regs:list DEX_Reg) (default:L.t) {struct valid_regs} : TypeRegisters:=
  match valid_regs with
    | r::t => 
        if In_test r p then
          let k := DEX_lvt s r in
          VarMap.update _ (make_rt_from_lvt_rec s p t default) r k 
        else
          VarMap.update _ (make_rt_from_lvt_rec s p t default) r default 
    | nil => VarMap.empty L.t
  end.

(* Lemma lvt_rt : forall p r s rt k, 
  make_rt_from_lvt_rec s p = rt ->
  In r p -> 
  VarMap.get _ rt r = Some k -> DEX_lvt s r = k.
Proof. 
  intro p.
  induction p; intros. inversion H0.
  unfold make_rt_from_lvt_rec in H.
  assert (((fix make_rt_from_lvt_rec (s : DEX_sign) (p : list DEX_Reg) {struct p} : TypeRegisters :=
          match p with
          | nil => VarMap.empty L.t
          | r :: t => VarMap.update L.t (make_rt_from_lvt_rec s t) r (DEX_lvt s r)
          end) s p) = make_rt_from_lvt_rec s p). auto.
  rewrite H2 in H. clear H2.  
  destruct Reg_eq_dec with r a.
  rewrite <- H in H1.
  rewrite <- H2 in H1.
  rewrite VarMap.get_update1 in H1. inversion H1; auto.
  rewrite <- H in H1.
  rewrite VarMap.get_update2 in H1; auto.
  apply IHp with (rt:=make_rt_from_lvt_rec s p); auto.
  inversion H0; auto. symmetry in H3; contradiction.
Qed. *)

Definition compat_type_rt_lvt (s:DEX_sign) (rt:TypeRegisters) 
  (p:list DEX_Reg) (n:nat) : Prop :=
  forall x, ((Reg_toN x)<n)%nat ->
    exists r k, nth_error p (Reg_toN x) = Some r /\ BinNatMap.get _ rt r = Some k /\
    L.leql(*'*) k (DEX_lvt s x).

(* DEX
Definition elift m pc k st :=
  match throwableAt m pc with
    | nil => st
    | _ => lift k st
  end.
*)

