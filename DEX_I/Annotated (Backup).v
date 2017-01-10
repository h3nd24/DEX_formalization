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

Module VarMap := BinNatMap.
Definition TypeRegisters := VarMap.t L.t(* focus on DEX I'*).

Definition update_op (rt:TypeRegisters) (key:VarMap.key) (k:option L.t(*'*)) :=
  match k with
    | Some v => BinNatMap.update _ rt key v
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
        VarMap.update _ (make_rt_from_lvt_rec s p t default) r (if In_test r p then DEX_lvt s r else default)
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

Lemma fold_rec_subst_leaf_1 : forall p v n acc, (length (fold_rec L.t (list BinNatMap_Base.key)
        (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) => N.pos p0 :: b)
        (subst_leaf (option L.t) None p (Some v)) n acc)) = S (length acc)%nat.
Proof.
  induction p; auto; intros; try (simpl; apply IHp).
Qed.

Lemma fold_subst_leaf_1 : forall p v, length (BinMap_Base.fold L.t (list BinNatMap_Base.key)
        (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) => N.pos p0 :: b)
        (subst_leaf (option L.t) None p (Some v)) nil) = 1%nat.
Proof.
  unfold BinMap_Base.fold. unfold fold. intros.
  apply fold_rec_subst_leaf_1 with (p:=p) (v:=v) (n:=1).
Qed.

Lemma fold_rec_unroll_None : forall (A B:Type) f t1 t2 n acc,
  fold_rec A B f (node (option A) (@None A) t1 t2) n acc =
    fold_rec A B f t2 n~1 (fold_rec A B f t1 n~0 acc).
Proof. auto. Qed.

Lemma fold_rec_unroll_Some : forall (A B:Type) a f t1 t2 n acc,
  fold_rec A B f (node (option A) (Some a) t1 t2) n acc =
    fold_rec A B f t2 n~1 (f (inv_pos n 1) a (fold_rec A B f t1 n~0 acc)).
Proof. auto. Qed.

Lemma modify_tree_unroll : forall (A:Type) (bot:option A) p a t1 t2 f,
  modify_tree (option A) bot (node (option A) a t1 t2) p f =
   match p with
      | p'~1 => node _ a t1 (modify_tree _ bot t2 p' f)
      | p'~0 => node _ a (modify_tree _ bot t1 p' f) t2
      | 1 => node _ (f a) t1 t2
      end.
Proof. auto. Qed.
 
Lemma length_fold_rec_split : forall t2 n acc,
  length
(fold_rec L.t (list BinNatMap_Base.key)
   (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
    N.pos p0 :: b)
   (t2) n acc) = (length
(fold_rec L.t (list BinNatMap_Base.key)
   (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
    N.pos p0 :: b)
   (t2) n nil ) + length (acc))%nat.
Proof.
  induction t2; auto; intros.
  destruct a.
  (* a is Some *)
  rewrite fold_rec_unroll_Some.
  rewrite IHt2_2.
  rewrite fold_rec_unroll_Some.
  replace (length
 (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
     N.pos p0 :: b) t2_2 n~1
    (N.pos (inv_pos n 1)
     :: fold_rec L.t (list BinNatMap_Base.key)
          (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
           => N.pos p0 :: b) t2_1 n~0 nil))) with
    (length
 (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
     N.pos p0 :: b) t2_2 n~1 nil) + 
    length
 (N.pos (inv_pos n 1)
     :: fold_rec L.t (list BinNatMap_Base.key)
          (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
           => N.pos p0 :: b) t2_1 n~0 nil))%nat; auto.
  simpl.
  rewrite IHt2_1. rewrite <- plus_assoc. auto.
  (* a is None *)
  rewrite fold_rec_unroll_None. 
  rewrite IHt2_2. 
  rewrite fold_rec_unroll_None. 
  replace (length (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
     N.pos p0 :: b) t2_2 n~1
    (fold_rec L.t (list BinNatMap_Base.key)
       (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
        N.pos p0 :: b) t2_1 n~0 nil)))
  with ((length (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
     N.pos p0 :: b) t2_2 n~1 nil) + 
      length 
        (fold_rec L.t (list BinNatMap_Base.key)
       (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
        N.pos p0 :: b) t2_1 n~0 nil))%nat ); auto.
  rewrite IHt2_1. apply Nat.add_assoc.
  Qed. 

(*Lemma length_modify_tree_S : forall t2 p n v acc, length
(fold_rec L.t (list BinNatMap_Base.key)
   (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
    N.pos p0 :: b)
   (modify_tree (option L.t) None t2 p (fun _ : option L.t => Some v)) n acc) = 
S (length
(fold_rec L.t (list BinNatMap_Base.key)
   (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
    N.pos p0 :: b) t2 n acc)).
Proof.
  induction t2; auto; intros.
  simpl. rewrite fold_rec_subst_leaf_1; auto.
  rewrite modify_tree_unroll.
  destruct p. destruct a.
  rewrite fold_rec_unroll_Some. 
  rewrite length_fold_rec_split. rewrite IHt2_2.
  rewrite fold_rec_unroll_Some with (t1:=t2_1) (t2:=t2_2).
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:=(N.pos (inv_pos n 1)
       :: fold_rec L.t (list BinNatMap_Base.key)
            (fun (p0 : BinMap_Base.key) (_ : L.t)
               (b : list BinNatMap_Base.key) => N.pos p0 :: b) t2_1 n~0 acc)).
  rewrite plus_Sn_m; auto.
  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split. rewrite IHt2_2.
  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split with (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  rewrite plus_Sn_m; auto.
  destruct a.
  rewrite fold_rec_unroll_Some. 
  rewrite length_fold_rec_split. simpl. rewrite IHt2_1.
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:=(N.pos (inv_pos n 1)
       :: fold_rec L.t (list BinNatMap_Base.key)
            (fun (p0 : BinMap_Base.key) (_ : L.t)
               (b : list BinNatMap_Base.key) => N.pos p0 :: b) t2_1 n~0 acc)).
  simpl. omega.
  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split. simpl. rewrite IHt2_1.
  rewrite length_fold_rec_split with (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  omega.
  destruct a.
  rewrite ?fold_rec_unroll_Some.
  admit.
  rewrite ?fold_rec_unroll_Some.
  rewrite ?fold_rec_unroll_None.
  rewrite length_fold_rec_split.
(*     simpl.  *)
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  simpl. omega.
Admitted.*)

Lemma L1_aux : forall l1 l2 x, In x (fold_right (fun (pa : positive * L.t) (b0 : list N) =>
      let (p0, _) := pa in N.pos p0 :: b0) (x::l1) (l2)).
Proof.
  induction l1; induction l2; intros; simpl; auto.
  destruct a; apply in_cons; apply IHl2.
  destruct a0; apply in_cons; apply IHl2.
Qed.

Lemma L2_aux : forall l1 l2 x, In x l1 ->
  In x (fold_right (fun (pa : positive * L.t) (b0 : list N) =>
      let (p0, _) := pa in N.pos p0 :: b0) (l1) (l2)).
Proof.
  induction l1; induction l2; intros; simpl; auto.
  destruct a; apply in_cons; apply IHl2; auto.
  destruct a0; apply in_cons; apply IHl2; auto.
Qed.
 
Lemma L3_aux : forall (l1:list N) (l2:list (positive*L.t)) (x:positive), 
  (exists a, In (x,a) l2) ->
  In (N.pos x) (fold_right (fun (pa : positive * L.t) (b0 : list N) =>
      let (p0, _) := pa in N.pos p0 :: b0) (l1) (l2)).
Proof.
  induction l1; induction l2; intros; simpl. inversion H. inversion H0.
  destruct H. destruct a. inversion H.
  inversion H0; subst. apply in_eq.
  apply in_cons. apply IHl2; auto.
  exists x0; auto.
  destruct H. inversion H.
  destruct a0. destruct H; inversion H. inversion H0.
  subst; apply in_eq.
  apply in_cons; apply IHl2; auto. exists x0; auto.
Qed.

Lemma L3_aux' : forall (x:positive) (l:list (positive*L.t)), 
  In (N.pos x) (fold_right (fun (pa : positive * L.t) (b0 : list N) =>
      let (p0, _) := pa in N.pos p0 :: b0) nil (l))
  ->  (exists a, In (x,a) l).
Proof.
  intros until l.
  rewrite <- fold_right_eq2 with (f1:=(fun (pa:prod positive L.t) (b0:list N) => Npos (fst pa)::b0)).
    rewrite in_fold_cons; intros.
    destruct (in_map_inv _ _ _ _ _ H).
    destruct x0; simpl in *; intuition; subst; eauto.
    inversion H1; subst; eauto.
    destruct a; simpl; auto.
Qed.
 
Lemma L1 : forall t1 t2 v acc, In 1%N
  (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
    N.pos p :: b) (node (option L.t) (Some v) t1 t2) 1 acc).
Proof.
  intros; simpl.
  rewrite <- fold_rec_prop with (l:=nil) (b1:=1%N
    :: fold_rec L.t (list BinNatMap_Base.key)
         (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
          N.pos p :: b) t1 2 acc); auto.
  apply L1_aux.
Qed.

Variable length_modify_tree_S : forall t2 p n v acc,
(*    (~In (N.pos p) (fold L.t (list BinNatMap_Base.key)
            (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
             N.pos p :: b) t2 nil)) ->    *)
length
  (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
      N.pos p0 :: b)
    (modify_tree (option L.t) None t2 p (fun _ : option L.t => Some v)) n acc) = 
  S (length
    (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
      N.pos p0 :: b) t2 n acc)).
(*
Lemma length_modify_tree_S : forall t2 p n v acc, 
   (~In (N.pos p) (fold L.t (list BinNatMap_Base.key)
            (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
             N.pos p :: b) t2 nil)) ->  
length
  (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
      N.pos p0 :: b)
    (modify_tree (option L.t) None t2 p (fun _ : option L.t => Some v)) n acc) = 
  S (length
    (fold_rec L.t (list BinNatMap_Base.key)
    (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
      N.pos p0 :: b) t2 n acc)).
Proof.
  (* old proof *)
  induction t2; auto; intros.
  simpl. rewrite fold_rec_subst_leaf_1; auto.
  rewrite modify_tree_unroll.
  destruct p.

  destruct a.
  rewrite fold_rec_unroll_Some. 
  rewrite length_fold_rec_split. rewrite IHt2_2.
  rewrite fold_rec_unroll_Some with (t1:=t2_1) (t2:=t2_2); auto.
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:=(N.pos (inv_pos n 1)
       :: fold_rec L.t (list BinNatMap_Base.key)
            (fun (p0 : BinMap_Base.key) (_ : L.t)
               (b : list BinNatMap_Base.key) => N.pos p0 :: b) t2_1 n~0 acc)).
  rewrite plus_Sn_m; auto. 
  (* dealing with the stupid key *)
  auto.
  unfold not; intros; unfold not in H; apply H.
  clear H.
(* Lemma random: forall t2 t1 v p,
  In (N.pos p)
       (fold L.t (list BinNatMap_Base.key)
          (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
           N.pos p :: b) t2 nil) ->
  In (N.pos p~1)
  (fold L.t (list BinNatMap_Base.key)
     (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
      N.pos p0 :: b) (node (option L.t) (Some v) t1 t2) nil).
  Proof.
    intros t2 t1 v p.
    rewrite <- ?fold_prop.
    intro H. apply L3_aux' in H.
    apply L3_aux.
    destruct H.
    exists x. auto.
    unfold elements. unfold elements in H.
    simpl.
    simpl in H.
    intros; unfold fold; simpl; auto. *)
    

  unfold fold in H0. 
  unfold fold. simpl.
  
(*   rewrite <- fold_rec_prop  with (l := nil) (b1:=(N.pos (inv_pos 1 1)
      :: fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
            N.pos p0 :: b) t2_1 2 nil)).
  simpl. admit. *)
  rewrite <- fold_rec_prop with (l:=nil) (b1:= (N.pos (inv_pos 1 1)
      :: fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
            N.pos p0 :: b) t2_1 2 nil)); auto.
  apply L3_aux; auto.
  rewrite <- fold_rec_prop with (l:=nil) (b1:=nil) in H0; auto.
  simpl.
  apply L3_aux' in H0. destruct H0.
  Lemma random : forall p t v,
    In (p, v) (elements_rec L.t t 1 nil) ->
    In (p~1, v) (elements_rec L.t t 3 nil).
  Proof.
    induction p; induction t; intros; auto.
    admit. admit.   
    
    Lemma L3: forall t p x v, 
    In (p, v) (elements_rec L.t t x nil) ->
    In (p~1, v) (elements_rec L.t t x~1 nil).
  Proof.
    (* induction x;  *) induction t; intros; simpl; auto.
    destruct a; auto. simpl. (* simpl in H1. contradiction. *)
    simpl. (* simpl in H1. destruct o.
    apply IHx. *)
(* 
destruct o. apply IHp in H. 
    induction t; simpl; intros; auto. *)
(*       with (acc:=((inv_pos x 1, t) :: elements_rec L.t t1 x~0 acc)); auto. *)
(*     destruct a. *)
    simpl.
    Lemma L4: forall t x k v acc, In (k, v) (elements_rec L.t t x acc) ->
      In (k, v) (elements_rec L.t t x nil) \/ In (k,v) acc.
    Proof. induction t; simpl; auto.
      destruct a.
      simpl; intros. apply IHt2 in H.
      inversion H. left. 
      Lemma L5 : forall t acc x k v, 
        In (k, v) (elements_rec L.t t x nil) ->
        In (k, v) (elements_rec L.t t x acc).
      Proof.
        induction t as [| a t0 IHt0 t2 IHt2]; simpl in |- *; intros; auto.
        inversion H.
        destruct a. apply IHt2; auto. admit.
        apply IHt2. admit.
      Admitted.
      apply L5; auto.
      inversion H0. rewrite H1. left. 
        apply in_elements_rec_in_acc. apply in_eq.
      apply IHt1 in H1.
      inversion H1. left.  apply in_elements_rec_in_acc. apply in_cons; auto. 
      right; auto. simpl; intros. apply IHt2 in H.
      inversion H. left.
      apply L5; auto.
      apply IHt1 in H0.
      inversion H0. left. apply in_elements_rec_in_acc; auto.
      right; auto.
    Qed.
    simpl in H. 
    apply L4 in H. inversion H.
    apply IHt2 in H0. admit. 
    apply in_elements_rec_in_acc; auto. 
    inversion H0. inversion H1. subst. 
    assert (forall x, (inv_pos x 1)~1 = inv_pos x 3); auto.
    clear. intros. induction x; simpl; auto.
    admit. admit. rewrite H2; apply in_eq.
    apply in_cons; auto.  apply IHt1 in H1. admit.
    apply L4 in H. inversion H.
    apply IHt2 in H0. admit.
    apply in_elements_rec_in_acc; auto.
    apply IHt1 in H0.
    admit.
  Admitted.
  exists x.
  apply L3; auto.
    apply L4.
    

      right. inversion H0.
        unfold not. unfold not in H. intros; apply H. 
        
        apply IHacc in H.
        unfold elements_rec.
        destruct t. simpl in H. apply in_cons; auto.
        destruct o. simpl.
      induction ((inv_pos x 1, t) :: elements_rec L.t t1 x~0 nil); auto.
      simpl.
      simpl.
       
  admit.
  admit.
  destruct a. rewrite fold_rec_unroll_Some. 
  rewrite length_fold_rec_split. simpl. rewrite IHt2_1.
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:=(N.pos (inv_pos n 1)
       :: fold_rec L.t (list BinNatMap_Base.key)
            (fun (p0 : BinMap_Base.key) (_ : L.t)
               (b : list BinNatMap_Base.key) => N.pos p0 :: b) t2_1 n~0 acc)).
  simpl. auto. 
  unfold not; unfold not in H. intros; apply H. 

  rewrite <- fold_rec_prop with (l:=nil) (b1:= (N.pos (inv_pos 1 1)
      :: fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
            N.pos p0 :: b) t2_1 2 nil)); auto.

    induction acc. inversion H0. contradiction. 
    destruct a. apply IHt2. 
    
    subst; auto.
    apply IHt2.

    induction t; simpl; intros; auto.
    admit.
    destruct a.
    apply IHt2; auto.
    destruct (elements_rec L.t t1 x~0 acc).
    destruct (elements_rec L.t t1 x~1~0 acc). 
    admit.
    apply IHt2; auto.
    elements_rec
  Admitted. 

  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split. rewrite IHt2_2.
  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split with (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  rewrite plus_Sn_m; auto.
  unfold not; intros; unfold not in H; apply H.
  unfold fold in H0.
  unfold fold.
  rewrite fold_rec_unroll_None.
  admit.

  destruct a.
  rewrite fold_rec_unroll_Some. 
  rewrite length_fold_rec_split. simpl. rewrite IHt2_1.
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:=(N.pos (inv_pos n 1)
       :: fold_rec L.t (list BinNatMap_Base.key)
            (fun (p0 : BinMap_Base.key) (_ : L.t)
               (b : list BinNatMap_Base.key) => N.pos p0 :: b) t2_1 n~0 acc)).
  simpl. omega.
  (* dealing with the key *)
  unfold not; intros; unfold not in H; apply H.
  unfold fold in H0.
  unfold fold.
  rewrite fold_rec_unroll_Some.
  rewrite <- fold_rec_prop  with (l := nil) (b1:=(N.pos (inv_pos 1 1)
      :: fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
            N.pos p0 :: b) t2_1 2 nil)); auto.
  apply L2_aux. apply in_cons.
  rewrite <- fold_rec_prop with (l:=nil) (b1:=nil); auto. 
  rewrite <- fold_rec_prop with (l:=nil) (b1:=nil) in H0; auto.
(*   destruct t2_1. inversion H0.
(*   simpl in H0. destruct o. simpl. *)
(*   apply BinMap.in_fold_cons in H0. *) *)
  
    
  admit.

  rewrite fold_rec_unroll_None.
  rewrite length_fold_rec_split. simpl. rewrite IHt2_1.
  rewrite length_fold_rec_split with (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  omega.
  unfold not; intros; unfold not in H; apply H.
  unfold fold in H0.
  unfold fold.
  rewrite fold_rec_unroll_None.
  rewrite <- fold_rec_prop  with (l := nil) (b1:= fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key) =>
            N.pos p0 :: b) t2_1 2 nil); auto.
  apply L2_aux.
  rewrite <- fold_rec_prop with (l:=nil) (b1:=nil); auto.
  rewrite <- fold_rec_prop with (l:=nil) (b1:=nil) in H0; auto.
  apply L3_aux .
  apply L3_aux' in H0.
  admit.

  destruct a.
  apply False_ind.
  unfold not in H. apply H.
  apply L1.
  rewrite ?fold_rec_unroll_Some.
  rewrite ?fold_rec_unroll_None.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (t2:=t2_2) (acc:= (fold_rec L.t (list BinNatMap_Base.key)
         (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
          => N.pos p0 :: b) t2_1 n~0 acc)).
  simpl. omega.
Admitted.  *)

Lemma dom_length_update_nodup : forall m a v, ~In a (VarMap.dom L.t m) ->  
  length (VarMap.dom L.t (VarMap.update L.t m a v)) = S (length (VarMap.dom L.t m)).
Proof. 
  intro m. 
  destruct m; induction t; auto; intros.
  destruct o; auto. 
  destruct a; simpl. contradiction H; simpl; auto.
  rewrite fold_subst_leaf_1; auto.
  destruct a; simpl; auto.
  rewrite fold_subst_leaf_1; auto.
  (* IH *)
  (* old proof *)
  destruct o; destruct a0.
  contradiction H; simpl; auto.
  unfold VarMap.dom;
  unfold BinNatMap_Base.fold;
  unfold BinMap_Base.fold;
  unfold VarMap.update; unfold BinNatMap_Base.modify; unfold BinMap_Base.modify.
  destruct a. 
  (* case where the fold_rec_unroll_Some *)
  rewrite modify_tree_unroll.
  destruct p.
  (* case of p *)
  unfold fold.
  rewrite fold_rec_unroll_Some.
  rewrite fold_rec_unroll_Some. simpl.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:= (N.pos (inv_pos 1 1)
         :: fold_rec L.t (list BinNatMap_Base.key)
              (fun (p0 : BinMap_Base.key) (_ : L.t)
                 (b : list BinNatMap_Base.key) => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite <- plus_Sn_m. 
  simpl; auto.
  rewrite length_modify_tree_S; auto.
  (* case of p~0 *)
  unfold fold.
  rewrite ?fold_rec_unroll_Some. simpl.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:=(N.pos (inv_pos 1 1)
         :: fold_rec L.t (list BinNatMap_Base.key)
              (fun (p0 : BinMap_Base.key) (_ : L.t)
                 (b : list BinNatMap_Base.key) => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite length_modify_tree_S. omega.
  (* case of xI *)
  apply False_ind. 
  apply H. simpl. right.
  apply L1.
  (* case where the fold_rec_unroll_None *)
  unfold fold;
  rewrite modify_tree_unroll.
  destruct p.
  (* case of p *)
  rewrite fold_rec_unroll_None.
  rewrite fold_rec_unroll_None.
  simpl. rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:= (fold_rec L.t (list BinNatMap_Base.key)
              (fun (p0 : BinMap_Base.key) (_ : L.t)
                 (b : list BinNatMap_Base.key) => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite <- plus_Sn_m.  rewrite length_modify_tree_S; simpl; auto.
  (* case of p~0 *)
  rewrite ?fold_rec_unroll_None. simpl.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:=(fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
            => N.pos p0 :: b) t1 2 nil)).
  rewrite length_modify_tree_S. omega.
  (* case of xI *)
  rewrite fold_rec_unroll_Some.
  rewrite fold_rec_unroll_None. simpl. 
  rewrite length_fold_rec_split. simpl. rewrite length_fold_rec_split with (acc:=(fold_rec L.t (list BinNatMap_Base.key)
           (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
            => N.pos p :: b) t1 2 nil)).
  rewrite <- plus_n_Sm. auto.
  (* *)
  simpl; auto.
  (* *)
  unfold VarMap.dom;
  unfold BinNatMap_Base.fold;
  unfold BinMap_Base.fold;
  unfold VarMap.update; unfold BinNatMap_Base.modify; unfold BinMap_Base.modify.
  destruct a. 
  (* case where the fold_rec_unroll_Some *)
  rewrite modify_tree_unroll.
  destruct p.
  (* case of p *)
  unfold fold.
  rewrite ?fold_rec_unroll_Some.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:= (N.pos (inv_pos 1 1)
         :: fold_rec L.t (list BinNatMap_Base.key)
              (fun (p0 : BinMap_Base.key) (_ : L.t)
                 (b : list BinNatMap_Base.key) => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite <- plus_Sn_m. apply Nat.add_cancel_r. 
  rewrite length_modify_tree_S; auto.
  (* case of p~0 *)
  unfold fold.
  rewrite ?fold_rec_unroll_Some.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:=(N.pos (inv_pos 1 1)
         :: fold_rec L.t (list BinNatMap_Base.key)
              (fun (p0 : BinMap_Base.key) (_ : L.t)
                 (b : list BinNatMap_Base.key) => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite length_modify_tree_S. omega.
  (* case of xI *)
  apply False_ind.
  apply H. apply L1.
  (* case where the fold_rec_unroll_None *)
  rewrite modify_tree_unroll.
  destruct p.
  (* case of p *)
  unfold fold.
  rewrite ?fold_rec_unroll_None.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:=(fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
            => N.pos p0 :: b) t1 2 nil)).
  simpl. rewrite <- plus_Sn_m. apply Nat.add_cancel_r.
  apply length_modify_tree_S.
  (* case of p~0 *)
  unfold fold.
  rewrite ?fold_rec_unroll_None.
  rewrite length_fold_rec_split.
  rewrite length_fold_rec_split with (acc:=(fold_rec L.t (list BinNatMap_Base.key)
           (fun (p0 : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
            => N.pos p0 :: b) t1 2 nil)).
  rewrite length_modify_tree_S. omega.
  (* case of xI *)
  unfold fold.
  rewrite fold_rec_unroll_Some.
  rewrite fold_rec_unroll_None. 
  rewrite length_fold_rec_split. simpl. rewrite length_fold_rec_split with (acc:=(fold_rec L.t (list BinNatMap_Base.key)
           (fun (p : BinMap_Base.key) (_ : L.t) (b : list BinNatMap_Base.key)
            => N.pos p :: b) t1 2 nil)).
  rewrite plus_n_Sm. auto.
Qed.

Lemma In_dom_update' : forall a m l v,  ~In a (VarMap.dom L.t m) -> 
  eq_set (VarMap.dom L.t m) (l) ->
  eq_set (VarMap.dom L.t (VarMap.update L.t m a v)) (a::l).
  
Proof.
  split; intros. inversion H0.
  (* making sure the length is equal *)
  rewrite dom_length_update_nodup; auto. simpl; auto.
  (* dealing with the content *)
  split; intros. auto.
  apply VarMap.in_dom_get_some in H1.
  generalize (Neq_spec a r); destruct (Neq a r); intros.
  subst; apply in_eq.
  rewrite VarMap.get_update2 in H1; auto.
  apply VarMap.get_some_in_dom in H1.
  apply in_cons. rewrite H0 in H1; auto.
  generalize (Neq_spec a r); destruct (Neq a r); intros.
  apply VarMap.get_some_in_dom. subst.
  rewrite VarMap.get_update1; auto. unfold not; intros. inversion H2.
  inversion H1. apply False_ind; auto.
  apply VarMap.get_some_in_dom. 
  rewrite VarMap.get_update2; auto.
  apply VarMap.in_dom_get_some.
  rewrite H0; auto.
Qed.

Lemma make_rt_from_lvt_prop3 : forall s p v d, NoDup v ->
  eq_set (VarMap.dom _ (make_rt_from_lvt_rec s p v d)) (v).
Proof.
  intros.
  induction v; constructor; auto.
  split; intros H0; inversion H0.
  assert (make_rt_from_lvt_rec s p (a::v) d = 
    VarMap.update _ (make_rt_from_lvt_rec s p v d) a (if In_test a p then DEX_lvt s a else d)). auto.
  rewrite H0. inversion H. apply IHv in H4.
  inversion H4. inversion H0.
    rewrite dom_length_update_nodup. simpl; auto.
    rewrite H4; auto.
  inversion H. apply IHv in H3.
  inversion H3; split; intros.
  assert (make_rt_from_lvt_rec s p (a::v) d = 
    VarMap.update _ (make_rt_from_lvt_rec s p v d) a (if In_test a p then DEX_lvt s a else d)). auto.
  generalize (Neq_spec r a); destruct (Neq r a); intros. 
    subst; apply in_eq.
    rewrite H7 in H6.
    apply In_dom_update' with (a:=a) (v:=(if In_test a p then DEX_lvt s a else d)) in H3; auto.
    inversion H3. apply H10; auto. 
    (* *)
    unfold not. intros. rewrite H3 in H9. contradiction.  
  assert (make_rt_from_lvt_rec s p (a::v) d = 
    VarMap.update _ (make_rt_from_lvt_rec s p v d) a (if In_test a p then DEX_lvt s a else d)). auto.
  rewrite H7.
   apply In_dom_update' with (a:=a) (v:=(if In_test a p then DEX_lvt s a else d)) in H3; auto.
    inversion H3. apply H9; auto.
    unfold not; intros. rewrite H3 in H8; contradiction. 
Qed.

  Definition tsub_rt (rt1 rt2 : VarMap.t L.t) : bool :=
  (eq_set_test (VarMap.dom _ rt1) (VarMap.dom _ rt2)) &&
  tsub_rec (rt1) (rt2) (VarMap.dom _ rt2).

  Lemma tsub_rec_leq_aux : forall r rt1 rt2, In r (VarMap.dom _ rt2) -> 
    tsub_rec rt1 rt2 (VarMap.dom _ rt2) = true -> tsub_element rt1 rt2 r = true.
  Proof.
    intros. unfold tsub_rec in H0.
    induction (VarMap.dom L.t rt2).
      inversion H.
    elim (andb_prop _ _ H0); intros.
    destruct (reg_eq_dec a r).
      rewrite <- e; auto.
    inversion H. contradiction.
    apply IHl in H3; auto.
  Qed.

  Lemma tsub_rec_leq : forall r rt1 rt2 k1 k2, In r (VarMap.dom _ rt2) ->
    tsub_rec rt1 rt2 (VarMap.dom _ rt2) = true ->
    Some k1 = VarMap.get _ rt1 r ->
    Some k2 = VarMap.get _ rt2 r ->
    L.leql k1 k2.
  Proof.
    intros. apply tsub_rec_leq_aux with (rt1:=rt1) in H; auto.
    unfold tsub_element in H. 
    rewrite <- H1 in H.
    rewrite <- H2 in H.
    generalize (L.leql_t_spec); intros.
    specialize H3 with k1 k2. rewrite H in H3; auto.
  Qed.