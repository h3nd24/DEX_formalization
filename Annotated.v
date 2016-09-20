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

Lemma not_In_In_test : forall a l, ~In a l <-> In_test a l = false.
Proof.
  intros. split; intros.
  (* -> *)
  induction l; auto.
  apply not_in_cons in H. inversion H. unfold In_test.
  apply orb_false_intro; auto. 
  generalize (Neq_spec a0 a); intros Heq. destruct (Neq a0 a); auto. apply False_ind; auto.
  (* <- *)
  induction l; auto.
  inversion H. apply orb_false_elim in H1; inversion H1.
  unfold not; intros.
  inversion H3; auto.
  generalize (Neq_spec a0 a); intros Heq; rewrite H0 in Heq; auto.
  apply IHl in H2; auto.
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

Lemma make_rt_from_lvt_prop1 : forall s v p d r, 
  (forall k, In r p -> Some k = VarMap.get _ (make_rt_from_lvt_rec s p v d) r -> k = (DEX_lvt s r)).
Proof.
  intros.
  induction v.
  intros. simpl in H0. rewrite VarMap.get_empty in H0. inversion H0.
  intros.
  generalize (Neq_spec a r); intros Heq.
  destruct (Neq a r). subst.
  simpl in H0. 
  apply In_In_test in H. rewrite H in H0.
  rewrite VarMap.get_update1 in H0; auto. inversion H0; auto.
  simpl in H0.
  destruct (In_test a p).
  rewrite VarMap.get_update2 in H0; auto.
  rewrite VarMap.get_update2 in H0; auto.
Qed.

Lemma make_rt_from_lvt_prop2 : forall s p v d r,
  In r v -> ~In r p -> Some d = VarMap.get _ (make_rt_from_lvt_rec s p v d) r.
Proof.
  intros.
  induction v.
  inversion H.
  inversion H.
  subst. simpl. apply not_In_In_test in H0. rewrite H0.
  rewrite VarMap.get_update1; auto.
  apply IHv in H1.
  simpl. 
  generalize (Neq_spec a r); intros Heq.
  destruct (Neq a r). subst. 
  apply not_In_In_test in H0. rewrite H0. rewrite VarMap.get_update1; auto.
  destruct (In_test a p).
  subst; rewrite VarMap.get_update2; auto.
  rewrite VarMap.get_update2; auto.
Qed.

Fixpoint eq_set_r_test (regs dom1 dom2:@list DEX_PC) : bool :=
  match regs with
    | nil => true
    | h::t => In_test h dom2 && In_test h dom1 && eq_set_r_test t dom1 dom2
  end.

Definition eq_set_test (dom1 dom2:list DEX_PC) : bool :=
  beq_nat (length dom1) (length dom2) && 
    eq_set_r_test dom1 dom1 dom2 && eq_set_r_test dom2 dom1 dom2.

Inductive eq_set (dom1 dom2:@list DEX_PC) : Prop :=
  forall_set : length (dom1) = length (dom2) -> (forall r, In r dom1 <-> In r dom2) -> eq_set dom1 dom2.

Lemma eq_set_prop_aux' : forall l dom1 dom2 r, eq_set_r_test l dom1 dom2 = true ->
  In r l -> In r dom1 /\ In r dom2.
Proof.
  intro l; induction l; intros.
  inversion H0.
  split.
    specialize IHl with (dom1:=dom1) (dom2:=dom2) (r:=r).
    inversion H. elim (andb_prop _ _ H2); intros. elim (andb_prop _ _ H1); intros. 
    (* generalize (Neq_spec a r); destruct (Neq a r); intros.
    subst; apply In_In_test; auto. *)
    inversion H0. subst; apply In_In_test; auto.
      apply IHl in H3; auto. inversion H3; auto.
  specialize IHl with (dom1:=dom1) (dom2:=dom2) (r:=r).
    inversion H. elim (andb_prop _ _ H2); intros. elim (andb_prop _ _ H1); intros. 
    (* generalize (Neq_spec a r); destruct (Neq a r); intros.
    subst; apply In_In_test; auto. *)
    inversion H0. subst; apply In_In_test; auto.
      apply IHl in H3; auto. inversion H3; auto.
Qed.
 
Ltac flatten_bool :=
     repeat match goal with
       [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
     end.

Lemma eq_set_prop_aux : forall dom1 dom2, eq_set_test dom1 dom2 = true ->
  forall r, (In r dom2 -> In r dom1) /\ (In r dom1 -> In r dom2).
Proof.
  split; intros.
  unfold eq_set_test in H. flatten_bool.
  apply eq_set_prop_aux' with (r:=r) in H2; inversion H2; auto.
  unfold eq_set_test in H. flatten_bool.
  apply eq_set_prop_aux' with (r:=r) in H3; inversion H3; auto.
Qed.

(* Lemma eq_set_prop_aux2 : forall dom1 dom2, eq_set_test dom1 dom2 = true ->
  length (dom1) = length (dom2).
Proof.
  intro dom1; induction dom1; intro dom2; induction dom2; intros; auto.
  unfold eq_set_test in H. flatten_bool. inversion H1. flatten_bool. inversion H4.
  unfold eq_set_test in H. flatten_bool. inversion H0.
  assert (forall (a:DEX_PC) l, length (a::l) = S (length l)). auto.
  rewrite H0. rewrite H0.
  apply eq_S. 
  unfold eq_set_test in H. flatten_bool.
apply IHdom1; auto.
Qed. *)

Lemma eq_set_refl : reflexive (@list DEX_PC) eq_set.
Proof. unfold reflexive; intros; constructor; split; auto. Qed.
Lemma eq_set_sym : symmetric (@list DEX_PC) eq_set.
Proof. unfold symmetric; intros; inversion H; econstructor. 
  congruence. 
  split; apply H1.
Qed.
Lemma eq_set_trans : transitive (@list DEX_PC) eq_set.
Proof. unfold transitive; intros.
  inversion H; inversion H0.
  constructor. congruence. 
  split; intros.
    apply H4; apply H2; auto.
    apply H2; apply H4; auto.
Qed.
Require Import Setoid.
Theorem set_setoid: Setoid_Theory (@list DEX_PC) eq_set.
 split.
 exact eq_set_refl.
 exact eq_set_sym.
 exact eq_set_trans.
Qed.
Add Setoid (@list DEX_PC) eq_set set_setoid as eq_set_rel.

Add Morphism (@In DEX_PC) : In_set_r_morphism. 
  split; intros H0; inversion H as [H1 H2]; apply H2; auto.
Qed.

Lemma eq_set_test_prop : forall dom1 dom2, eq_set_test dom1 dom2= true -> eq_set dom1 dom2.
Proof.
  intros. constructor.
  unfold eq_set_test in H. flatten_bool.
  apply beq_nat_true; auto.
  intros.
  apply eq_set_prop_aux with (r:=r) in H. inversion H; split; auto.
Qed.

(* 

  intros dom1; induction dom1; intros dom2; induction dom2; auto. 
  split; intros; auto.
  (* -> *)
    constructor; auto.
    split; intros H1; inversion H1.
    split; intros. inversion H. inversion H0.
    inversion H.
    split; intros. inversion H. inversion H0.
    inversion H.
    split; intros.
    inversion H.
    (* generalize (Neq_spec a a0); intros; destruct (Neq a a0).
    subst. destruct H1 with a0. *)
    unfold eq_set_test. repeat (apply andb_true_intro; split).
    specialize H1 with a. assert (In a (a0::dom2)). apply H1. apply in_eq.
    apply In_In_test; auto.
    specialize H1 with a0. assert (In a0 (a::dom1)). apply H1. apply in_eq.
    apply In_In_test; auto.
    specialize H1 with a.
      
  (* <- *) *)
 

Inductive eq_rt (rt1 rt2:VarMap.t L.t) : Prop :=
  forall_rt : eq_set (VarMap.dom L.t rt1) (VarMap.dom L.t rt2) ->
    (forall r, In r (VarMap.dom L.t rt1) -> In r (VarMap.dom L.t rt2) ->
    forall k1 k2, Some k1 = VarMap.get _ rt1 r -> Some k2 = VarMap.get _ rt2 r -> k1 = k2) -> eq_rt rt1 rt2.

Lemma eq_rt_refl : reflexive (@VarMap.t L.t) eq_rt.
Proof.
  unfold reflexive.
  constructor; intros. 
  apply eq_set_refl.
  congruence.
Qed.

Lemma eq_rt_sym : symmetric (@VarMap.t L.t) eq_rt.
Proof.
  unfold symmetric.
  constructor; intros;
    inversion H. apply eq_set_sym; auto.
  specialize H5 with (r:=r).
  apply H5 with (k1:=k2) (k2:=k1) in H1; auto.
Qed.

Lemma eq_rt_trans : transitive (@VarMap.t L.t) eq_rt.
Proof.
  unfold transitive.
  constructor; intros;
  inversion H; inversion H0.
    apply eq_set_trans with (x:=VarMap.dom L.t x) (y:=VarMap.dom L.t y) (z:=VarMap.dom L.t z); auto.
  specialize H6 with (r:=r); specialize H8 with (r:=r).
  assert (H2':=H2).
  rewrite <- H7 in H2.
  assert (exists ky, Some ky = VarMap.get L.t y r).
    apply VarMap.in_dom_get_some in H2. destruct (VarMap.get L.t y r).
    exists t; auto. elim H2; auto.
  destruct H9.
  specialize H6 with (1:=H1) (2:=H2) (3:=H3) (4:=H9) (k1:=k1) (k2:=x0);
  specialize H8 with (1:=H2) (2:=H2') (3:=H9) (4:=H4) (k1:=x0) (k2:=k2).
  congruence.
Qed.

Lemma eq_rt_get : forall rt1 rt2 r, eq_rt (rt1) (rt2) -> 
  In r (VarMap.dom L.t rt1) -> In r (VarMap.dom L.t rt2) -> 
  VarMap.get L.t rt1 r = VarMap.get L.t rt2 r.
Proof.
  intros.
  inversion H.
  specialize H3 with (1:=H0) (2:=H1).
  destruct (VarMap.get L.t rt1 r) eqn:Hrt1; destruct (VarMap.get L.t rt2 r) eqn:Hrt2; auto.
  assert (t = t0). apply H3 with (k1:=t) (k2:=t0); auto. 
  congruence.
  apply VarMap.in_dom_get_some in H1; apply False_ind; auto.
  apply VarMap.in_dom_get_some in H0; apply False_ind; auto.
Qed.

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

