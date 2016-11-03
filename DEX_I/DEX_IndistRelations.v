(** * IndistRelations.v: indistinguishability relation for annotated programs *)
(*Require FFun.*)
Require Export DEX_BigStepAnnot.
Require Export Annotated.

Open Scope type_scope.

Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Inductive Value_in : DEX_value -> DEX_value -> Prop :=
| Value_in_num: forall n,
  Value_in (Num n) (Num n).

Inductive Value_in_opt : 
  option DEX_value -> option DEX_value -> Prop :=
| Value_in_opt_some: 
  forall v v',
    Value_in v v' -> 
    Value_in_opt (Some v) (Some v')
| Value_in_opt_none: Value_in_opt None None.

Inductive Reg_in (observable:L.t) (r r': DEX_Registers.t) (rt rt': TypeRegisters) (rn:DEX_Reg) : Prop :=
| Reg_high_in : forall k k', MapList.get rt rn = Some k -> MapList.get rt' rn = Some k' ->
    ~(L.leql k observable) -> ~(L.leql k' observable) -> Reg_in observable r r' rt rt' rn
| Reg_nhigh_in : Value_in_opt (DEX_Registers.get r rn) (DEX_Registers.get r' rn) -> Reg_in observable r r' rt rt' rn.

Inductive Regs_in (observable:L.t) (r r': DEX_Registers.t) (rt rt': TypeRegisters) : Prop :=
| Build_Regs_in : eq_set (MapList.dom rt) (MapList.dom rt') ->
  (forall (rn:DEX_Reg), Reg_in observable r r' rt rt' rn) -> Regs_in observable r r' rt rt'.

Inductive st_in (observable:L.t) (rt rt':TypeRegisters) :   
  DEX_PC * DEX_Registers.t ->
  DEX_PC * DEX_Registers.t -> Prop := 
| Build_st_in: forall pc pc' r r',
    Regs_in observable r r' rt rt' ->
    st_in observable rt rt' (pc,r) (pc',r').

Inductive indist_return_value (observable:L.t) (s:DEX_sign) : 
    DEX_ReturnVal -> DEX_ReturnVal -> Prop :=
| indist_return_val : forall v1 v2 k,
  s.(DEX_resType) = Some k ->
  (L.leql k observable -> Value_in v1 v2) ->
  indist_return_value observable s (Normal (Some v1)) (Normal (Some v2))
| indist_return_void : 
  s.(DEX_resType) = None ->
  indist_return_value observable s (Normal None) (Normal None).

Inductive high_result (observable:L.t) (s:DEX_sign) : DEX_ReturnVal -> Prop :=
| high_result_void : 
  s.(DEX_resType) = None ->
  high_result observable s (Normal None)
| high_result_value : forall v k,
  s.(DEX_resType) = Some k ->
  ~ L.leql k observable ->
  high_result observable s (Normal (Some v)).

Inductive state : Type :=
  intra : DEX_IntraNormalState -> TypeRegisters -> state
| ret : DEX_ReturnVal -> state.

Inductive indist (observable:L.t) (p:DEX_ExtendedProgram) (m:DEX_Method) (sgn:DEX_sign) : state -> state -> Prop :=
| indist_intra : forall pc pc' r r' rt rt',
  st_in observable rt rt' (pc,r) (pc',r') ->
  indist observable p m sgn (intra (pc,r) rt) (intra (pc',r') rt')
| indist_return : forall v v',
  indist_return_value observable sgn v v'->
  indist observable p m sgn (ret v) (ret v').


 (** Indistinguishability relations *)

Section p.
  Variable kobs : L.t.
  Variable p : DEX_ExtendedProgram.

 (** Basic results on indistinguishability relations *)

  Lemma Value_in_sym : forall v1 v2,
    Value_in v1 v2 ->
    Value_in v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
  Qed.

  Lemma Value_in_opt_sym : forall v1 v2,
    Value_in_opt v1 v2 ->
    Value_in_opt v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
    apply Value_in_sym; auto.
  Qed.

  Lemma Value_in_trans : forall v1 v2 v3,
    Value_in v1 v2 ->
    Value_in v2 v3 ->
    Value_in v1 v3.
  Proof.
    intros.
    inversion H0; inversion H; subst; rewrite H4; constructor.
  Qed.

  Lemma Value_in_opt_trans : forall v1 v2 v3,
    Value_in_opt v1 v2->
    Value_in_opt v2 v3 ->
    Value_in_opt v1 v3.
  Proof.
    intros.
    inversion_clear H in H0; inversion_clear H0; try constructor.
    eapply Value_in_trans; eauto.
  Qed. 

  Lemma leql_join1 : forall k1 k2 k3,
    L.leql k2 k3 ->
    L.leql k2 (L.join k1 k3).
  Proof.
    intros.
    apply L.leql_trans with (1:=H).
    apply L.join_right.
  Qed.

  Lemma leql_join2 : forall k1 k2 k3,
    L.leql k2 k1 ->
    L.leql k2 (L.join k1 k3).
  Proof.
    intros.
    apply L.leql_trans with (1:=H).
    apply L.join_left.
  Qed.

  Lemma not_leql_trans : forall k1 k2 k3,
    ~ L.leql k1 k3 ->
    L.leql k1 k2 ->
    ~ L.leql k2 k3.
  Proof.
    red; intros.
    elim H.
    apply L.leql_trans with (1:=H0); auto.
  Qed.

  Lemma not_leql_join1 : forall k1 k2 k3,
    ~ L.leql k1 k3 ->
    ~ L.leql (L.join k1 k2) k3.
  Proof.
    intros; apply not_leql_trans with k1; auto.
    apply L.join_left.
  Qed.

  Lemma not_leql_join2 : forall k1 k2 k3,
    ~ L.leql k2 k3 ->
    ~ L.leql (L.join k1 k2) k3.
  Proof.
    intros; apply not_leql_trans with k2; auto.
    apply L.join_right.
  Qed.

  Lemma leql_join_each: forall k k1 k2, L.leql (L.join k k1) k2 -> L.leql k k2 /\ L.leql k1 k2.
  Proof. intros.
    split. apply L.leql_trans with (l2:=L.join k k1); auto. apply L.join_left.
    apply L.leql_trans with (l2:=L.join k k1); auto. apply L.join_right.
  Qed.

  Lemma Reg_in_sym : forall obs r r' rt rt' rn, 
    Reg_in obs r r' rt rt' rn -> 
    Reg_in obs r' r rt' rt rn.
  Proof.
    intros.
    inversion H.
      constructor 1 with (k:=k') (k':=k); auto.
      constructor 2; auto.
      apply Value_in_opt_sym; auto.
  Qed.  

 Lemma Regs_in_sym : forall r1 r2 rt1 rt2,
    Regs_in kobs r1 r2 rt1 rt2 ->
    Regs_in kobs r2 r1 rt2 rt1.
  Proof.
    induction 1.
    constructor. apply eq_set_sym; auto.
    intros.
    apply Reg_in_sym; auto.
  Qed.

  Lemma st_in_sym : forall rt rt' r r',
    st_in kobs rt rt' r r' ->
    st_in kobs rt' rt r' r.
  Proof.
    intros.
    inversion_clear H; constructor.
    apply Regs_in_sym; auto.
  Qed.
  Implicit Arguments st_in_sym.

  Lemma Value_in_opt_some_aux: forall ov ov' v v', 
    Value_in v v' -> 
    ov=(Some v)  -> 
    ov'= (Some v') -> 
    Value_in_opt ov ov'.
  Proof.
    intros;  subst; constructor; auto.
  Qed.

  Lemma ex_comp_Z : forall x y z:Z,
    (x <= y < z \/ ~ x <= y < z)%Z.
  Proof.
    intros.
    destruct (Z_le_dec x y).
    destruct (Z_lt_dec y z); intuition.
    intuition.
  Qed.

  Lemma nth_error_none_length : forall (A:Set) (l:list A) i,
    nth_error l i = None -> (length l <= i)%nat.
  Proof.
    induction l; destruct i; simpl; intros; try omega. 
    discriminate.
    generalize (IHl _ H); omega.
  Qed.

  Lemma nth_error_some_length : forall (A:Set) (l:list A) i a,
    nth_error l i = Some a -> (length l > i)%nat.
  Proof.
    induction l; destruct i; simpl; intros; try discriminate; try omega. 
    generalize (IHl _ _ H); omega.
  Qed.
End p.

  Hint Resolve 
    not_leql_join1 not_leql_join2 not_leql_trans 
    L.join_left L.join_right
    L.leql_trans : lattice.