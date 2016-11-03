(** * Annotated.v: Syntax of JVM program extended with security type annotations *)

(* Hendra: Added annotation for DEX program as well, but removed exceptions *)
Require Export LoadBicolano.
Require Export Level.
Require Export Axioms.

Import DEX_BigStep.DEX_BigStep.DEX_Dom.DEX_Prog.

Record DEX_sign : Set := make_DEX_sign {
  DEX_lvt : DEX_Reg -> L.t;
  DEX_resType : option L.t;
}.

Definition DEX_default_signature : DEX_sign :=
  make_DEX_sign
    (fun _ => L.bot)
    None.    

Record DEX_ExtendedProgram : Type := DEX_extP {
  DEX_prog :> DEX_Program;
  DEX_newArT : DEX_Method * DEX_PC -> L.t';
  DEX_static_signature : DEX_ShortMethodSignature -> DEX_sign;
  DEX_virtual_signature : DEX_ShortMethodSignature -> L.t -> DEX_sign;
  DEX_ft : DEX_FieldSignature -> L.t';
  locR : DEX_ShortMethodSignature -> list DEX_Reg
}.

Definition DEX_tag := option DEX_ClassName.

Definition well_formed_lookupswitch m := forall pc reg l size i o1 o2,
  instructionAt m pc = Some (DEX_SparseSwitch reg size l) ->
  In (i, o1) l -> In (i, o2) l -> o1=o2.

Module VarMap := MapList.
Definition TypeRegisters := MapList.t L.t(* focus on DEX I'*).

Definition update_op (rt:TypeRegisters) (key:MapList.key) (k:option L.t(*'*)) :=
  match k with
    | Some v => MapList.update rt key v
    | None => rt
  end.

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
        MapList.update (make_rt_from_lvt_rec s p t default) r (if In_test r p then DEX_lvt s r else default)
    | nil => MapList.empty L.t
  end.

Lemma make_rt_from_lvt_prop4 : forall s v p d r, In r (MapList.dom (make_rt_from_lvt_rec s p v d)) -> In r v.
Proof.
  induction v; intros.
  inversion H.
  simpl in H.
  unfold MapList.dom in H. 

Lemma make_rt_from_lvt_prop1 : forall s v p d r, 
  (forall k, In r p -> Some k = MapList.get (make_rt_from_lvt_rec s p v d) r -> k = (DEX_lvt s r)).
Proof.
  intros.
  induction v.
  inversion H0.
  simpl in H0. 
  generalize (Neq_spec a r); destruct (Neq a r) eqn:Heq; intros.
  apply In_In_test in H. subst. rewrite H in H0.
  rewrite MapList.get_update1 in H0; auto. inversion H0; auto.
  destruct (In_test a p).
  rewrite MapList.get_update2 in H0; auto.
  rewrite MapList.get_update2 in H0; auto.
Qed.

Lemma make_rt_from_lvt_prop2 : forall s p v d r,
  In r v -> ~In r p -> Some d = MapList.get (make_rt_from_lvt_rec s p v d) r.
Proof.
  intros.
  induction v.
  inversion H.
  inversion H.
  subst. simpl. apply not_In_In_test in H0. rewrite H0.
  rewrite MapList.get_update1; auto.
  apply IHv in H1.
  simpl. 
  generalize (Neq_spec a r); intros Heq.
  destruct (Neq a r). subst. 
  apply not_In_In_test in H0. rewrite H0. rewrite MapList.get_update1; auto.
  destruct (In_test a p).
  subst; rewrite MapList.get_update2; auto.
  rewrite MapList.get_update2; auto.
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
    inversion H0. subst; apply In_In_test; auto.
      apply IHl in H3; auto. inversion H3; auto.
  specialize IHl with (dom1:=dom1) (dom2:=dom2) (r:=r).
    inversion H. elim (andb_prop _ _ H2); intros. elim (andb_prop _ _ H1); intros. 
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
 

Inductive eq_rt (rt1 rt2:MapList.t L.t) : Prop :=
  forall_rt : eq_set (MapList.dom rt1) (MapList.dom rt2) ->
    (forall r, In r (MapList.dom rt1) -> In r (MapList.dom rt2) ->
    forall k1 k2, Some k1 = MapList.get rt1 r -> Some k2 = MapList.get rt2 r -> k1 = k2) -> eq_rt rt1 rt2.

Lemma eq_rt_refl : reflexive (@MapList.t L.t) eq_rt.
Proof.
  unfold reflexive.
  constructor; intros. 
  apply eq_set_refl.
  congruence.
Qed.

Lemma eq_rt_sym : symmetric (@MapList.t L.t) eq_rt.
Proof.
  unfold symmetric.
  constructor; intros;
    inversion H. apply eq_set_sym; auto.
  specialize H5 with (r:=r).
  apply H5 with (k1:=k2) (k2:=k1) in H1; auto.
Qed.

Lemma eq_rt_trans : transitive (@MapList.t L.t) eq_rt.
Proof.
  unfold transitive.
  constructor; intros;
  inversion H; inversion H0.
    apply eq_set_trans with (x:=MapList.dom x) (y:=MapList.dom y) (z:=MapList.dom z); auto.
  specialize H6 with (r:=r); specialize H8 with (r:=r).
  assert (H2':=H2).
  rewrite <- H7 in H2.
  assert (exists ky, Some ky = MapList.get y r).
    apply MapList.in_dom_get_some in H2. destruct (MapList.get y r).
    exists t; auto. elim H2; auto.
  destruct H9.
  specialize H6 with (1:=H1) (2:=H2) (3:=H3) (4:=H9) (k1:=k1) (k2:=x0);
  specialize H8 with (1:=H2) (2:=H2') (3:=H9) (4:=H4) (k1:=x0) (k2:=k2).
  congruence.
Qed.

Lemma eq_rt_get : forall rt1 rt2 r, eq_rt (rt1) (rt2) -> 
  In r (MapList.dom rt1) -> In r (MapList.dom rt2) -> 
  MapList.get rt1 r = MapList.get rt2 r.
Proof.
  intros.
  inversion H.
  specialize H3 with (1:=H0) (2:=H1).
  destruct (MapList.get rt1 r) eqn:Hrt1; destruct (MapList.get rt2 r) eqn:Hrt2; auto.
  assert (t = t0). apply H3 with (k1:=t) (k2:=t0); auto. 
  congruence.
  apply MapList.in_dom_get_some in H1; apply False_ind; auto.
  apply MapList.in_dom_get_some in H0; apply False_ind; auto.
Qed.

Lemma dom_length_update_nodup : forall m a v, ~In a (MapList.dom m) ->  
  length (MapList.dom (MapList.update m a v)) = S (length (@MapList.dom L.t m)).
Proof.
  induction m; intros; auto.
  simpl in *. 
  generalize (Neq_spec a0 (fst a)); destruct (Neq a0 (fst a)) eqn:Heq; intros.
  apply False_ind; auto.
  simpl. rewrite IHm; auto.
Qed.

Lemma In_dom_update' : forall a m l v,  ~In a (MapList.dom m) -> 
  eq_set (MapList.dom m) (l) ->
  eq_set (@MapList.dom L.t (MapList.update m a v)) (a::l).
  
Proof.
  split; intros. inversion H0.
  (* making sure the length is equal *)
  rewrite dom_length_update_nodup; auto. simpl; auto.
  (* dealing with the content *)
  split; intros. auto.
  apply MapList.in_dom_get_some in H1.
  generalize (Neq_spec a r); destruct (Neq a r); intros.
  subst; apply in_eq.
  rewrite MapList.get_update2 in H1; auto.
  apply MapList.get_some_in_dom in H1.
  apply in_cons. rewrite H0 in H1; auto.
  generalize (Neq_spec a r); destruct (Neq a r); intros.
  apply MapList.get_some_in_dom. subst.
  rewrite MapList.get_update1; auto. unfold not; intros. inversion H2.
  inversion H1. apply False_ind; auto.
  apply MapList.get_some_in_dom. 
  rewrite MapList.get_update2; auto.
  apply MapList.in_dom_get_some.
  rewrite H0; auto.
Qed.

Lemma make_rt_from_lvt_prop3 : forall s p v d, NoDup v ->
  eq_set (MapList.dom (make_rt_from_lvt_rec s p v d)) (v).
Proof.
  induction v; auto; intros.
  constructor; auto. intros.
  simpl. split; intros; contradiction.
  simpl.
  inversion H. apply IHv with (d:=d) in H3.
  inversion H3. 
  constructor. rewrite dom_length_update_nodup; auto. 
    simpl. rewrite <- H4; auto.
  rewrite H3; auto.
  split; intros. 
  specialize H5 with r. 
  generalize (Neq_spec r a); destruct (Neq r a); intros.
  subst. apply in_eq.
  apply In_dom_update' with (a:=a) (v:=(if In_test a p then DEX_lvt s a else d)) in H3; auto.
  rewrite <- H3; auto.
  rewrite H3; auto.
  apply In_dom_update' with (a:=a) (v:=(if In_test a p then DEX_lvt s a else d)) in H3; auto.
    inversion H3. apply H8; auto.
    rewrite H3; auto.
Qed.

  Definition tsub_rt (rt1 rt2 : MapList.t L.t) : bool :=
  (eq_set_test (MapList.dom rt1) (MapList.dom rt2)) &&
  tsub_rec (rt1) (rt2) (MapList.dom rt2).

  Lemma tsub_rec_leq_aux : forall r rt1 rt2, In r (MapList.dom rt2) -> 
    tsub_rec rt1 rt2 (MapList.dom rt2) = true -> tsub_element rt1 rt2 r = true.
  Proof.
    intros. unfold tsub_rec in H0.
    induction (MapList.dom rt2).
      inversion H.
    elim (andb_prop _ _ H0); intros.
    destruct (reg_eq_dec a r).
      rewrite <- e; auto.
    inversion H. contradiction.
    apply IHl in H3; auto.
  Qed.

  Lemma tsub_rec_leq : forall r rt1 rt2 k1 k2, In r (MapList.dom rt2) ->
    tsub_rec rt1 rt2 (MapList.dom rt2) = true ->
    Some k1 = MapList.get rt1 r ->
    Some k2 = MapList.get rt2 r ->
    L.leql k1 k2.
  Proof.
    intros. apply tsub_rec_leq_aux with (rt1:=rt1) in H; auto.
    unfold tsub_element in H. 
    rewrite <- H1 in H.
    rewrite <- H2 in H.
    generalize (L.leql_t_spec); intros.
    specialize H3 with k1 k2. rewrite H in H3; auto.
  Qed.