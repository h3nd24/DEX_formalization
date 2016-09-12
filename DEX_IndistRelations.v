(** * IndistRelations.v: indistinguishability relation for annotated programs *)
(*Require FFun.*)
Require Export DEX_BigStepAnnot.
Require Export Annotated.

Open Scope type_scope.

Import DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

(* Hendra 12082016 - remove beta function, focus on DEX I *)
Inductive Value_in  (*b b':FFun.t Location*) : DEX_value -> DEX_value -> Prop :=
(*| Value_in_null: Value_in (*b b'*) Null Null *)
| Value_in_num: forall n,
  Value_in (*b b'*) (Num n) (Num n)
(*| Value_in_ref: forall loc loc' n, 
  b n = Some loc ->
  b' n = Some loc' ->
  Value_in b b' (Ref loc) (Ref loc')*).

Inductive Value_in_opt (*b b':FFun.t Location*) : 
  option DEX_value -> option DEX_value -> Prop :=
| Value_in_opt_some: 
  forall v v',
    Value_in (*b b'*) v v' -> 
    Value_in_opt (*b b'*) (Some v) (Some v')
| Value_in_opt_none: Value_in_opt (*b b'*) None None.

(*
Definition localvar_in (observable:L.t) (lvt:Var->L.t') (*b b'*) l l' := 
  forall x:Var, L.leql (lvt x) observable -> 
  Value_in_opt b b' (LocalVar.get l x) (LocalVar.get l' x).
*)
(*
Inductive high_st (observable:L.t) : OperandStack.t -> TypeStack ->  Prop := 
  high_nil :  high_st observable nil nil
| high_cons: forall s v st (k:L.t'),
  ~(L.leql k observable) ->
  high_st observable s st -> 
  high_st observable (v::s) (k::st).
*)

Inductive Reg_in (observable:L.t) :
  L.t -> L.t -> DEX_value -> DEX_value -> Prop :=
| Reg_high_in : forall k k' v v', ~(L.leql k observable) -> ~(L.leql k' observable) ->
    Reg_in observable k k' v v'
| Reg_nhigh_in : forall k k' v v', Value_in v v' -> Reg_in observable k k' v v'.

Inductive Regs_in (observable:L.t) (r r': DEX_Registers.t) (rt rt': TypeRegisters) : Prop :=
| Build_Regs_in : VarMap.dom _ rt = VarMap.dom _ rt' ->
  (forall (rn:DEX_Reg),
  In rn (VarMap.dom _ rt) -> In rn (VarMap.dom _ rt') -> 
  (forall v v' k k',
  Some v = DEX_Registers.get r rn -> Some v' = DEX_Registers.get r' rn ->
  Some k = VarMap.get _ rt rn -> Some k' = VarMap.get _ rt' rn ->
  Reg_in observable k k' v v')) -> Regs_in observable r r' rt rt'.

(* Inductive Regs_in (observable:L.t) (r r': DEX_Registers.t) (rt rt': TypeRegisters) : Prop :=
| High_Regs_in : 
  (forall (rn:DEX_Reg) k k',
  Some k = VarMap.get _ rt rn -> Some k' = VarMap.get _ rt' rn ->
  ~(L.leql k observable) /\ ~(L.leql k' observable)) -> Regs_in observable r r' rt rt'
| nHigh_Regs_in : 
  (forall (rn:DEX_Reg) v v' k k',
(*   In rn (DEX_Registers.dom r) -> In rn (DEX_Registers.dom r') -> *)
  Some v = DEX_Registers.get r rn -> Some v' = DEX_Registers.get r' rn ->
  Some k = VarMap.get _ rt rn -> Some k' = VarMap.get _ rt' rn ->
  Value_in v v') -> Regs_in observable r r' rt rt'. *)

Inductive st_in (observable:L.t) (*newArT : Method * PC -> L.t') (ft:FieldSignature -> L.t'*) 
(*lvt:Var->L.t'*)  (*b b':FFun.t Location*) (rt rt':TypeRegisters) :   
  DEX_PC * (*Heap.t * OperandStack.t * LocalVar.t*) DEX_Registers.t ->
  DEX_PC * (*Heap.t * OperandStack.t * LocalVar.t*) DEX_Registers.t -> Prop := 
| Build_st_in: forall (*h h'*) pc pc' (*l l'*) r r',
    (*localvar_in observable lvt (*b b'*) l l' ->*)
    Regs_in observable (*b b'*) r r' rt rt' ->
    (*hp_in observable newArT ft b b' h h' ->*)
    st_in observable (*newArT ft lvt b b'*) rt rt' (pc,r(*,l*)) (pc',r'(*,l'*)).

Inductive indist_return_value (observable:L.t) (s:DEX_sign) (*h1 h2:Heap.t*) : 
    DEX_ReturnVal -> DEX_ReturnVal -> (*FFun.t Location -> FFun.t Location ->*) Prop :=
| indist_return_val : forall v1 v2 (*b1 b2*) k,
  s.(DEX_resType) = Some k ->
  (L.leql k observable -> Value_in (*b1 b2*) v1 v2) ->
  indist_return_value observable s (*h1 h2*) (Normal (Some v1)) (Normal (Some v2)) (*b1 b2 *)
| indist_return_void : (*forall b1 b2 ,*)
  s.(DEX_resType) = None ->
  indist_return_value observable s (*h1 h2*) (Normal None) (Normal None) (*b1 b2 *).

Inductive high_result (observable:L.t) (s:DEX_sign) (*h:Heap.t*) : DEX_ReturnVal -> Prop :=
| high_result_void : 
  s.(DEX_resType) = None ->
  high_result observable s (*h*) (Normal None)
| high_result_value : forall v k,
  s.(DEX_resType) = Some k ->
  ~ L.leql k observable ->
  high_result observable s (*h*) (Normal (Some v)).

Inductive state : Type :=
  intra : DEX_IntraNormalState -> TypeRegisters -> (*FFun.t Location ->*) state
| ret : (*Heap.t ->*) DEX_ReturnVal -> (*FFun.t Location ->*) state.

Inductive indist (observable:L.t) (p:DEX_ExtendedProgram) (m:DEX_Method) (sgn:DEX_sign) : state -> state -> Prop :=
| indist_intra : forall  (*h h'*) pc pc' (*l l'*) r r' rt rt' (*b b'*),
  st_in observable (*newArT p) (ft p sgn.(DEX_lvt) b b'*) rt rt' (pc,(*h,*)r(*,l*)) (pc',(*h',*)r'(*,l'*)) ->
  indist observable p m sgn (intra (pc,((*h,*)r(*,l*))) rt (*b*)) (intra (pc',((*h',*)r'(*,l'*))) rt' (*b'*))
(*| indist_intra_return_case : forall pc h s l st b h' v' b',
  indist_intra_return observable p sgn (pc,(h,s,l)) st b h' v' b' ->
  indist observable p m sgn (intra (pc,(h,s,l)) st b) (ret h' v' b')
| indist_return_intra_case : forall pc h s l st b h' v' b',
  indist_intra_return observable p sgn (pc,(h,s,l)) st b h' v' b' ->
  indist observable p m sgn (ret h' v' b') (intra (pc,(h,s,l)) st b) *)
| indist_return : forall (*b b' h h'*) v v',
  (*hp_in observable (newArT p) (ft p) b b' h h' ->*)
  indist_return_value observable sgn (*h h'*) v v' (*b b'*) ->
  indist observable p m sgn (ret (*h*) v (*b*)) (ret (*h'*) v' (*b'*)).


 (** Indistinguishability relations *)

Section p.
  Variable kobs : L.t.
  Variable p : DEX_ExtendedProgram.
  (*Notation ft := (ft p).
  Notation newArT := (newArT p).*)

 (** Basic results on indistinguishability relations *)

  Lemma Value_in_sym : forall v1 v2 (*b1 b2*),
    Value_in (*b1 b2*) v1 v2 ->
    Value_in (*b2 b1*) v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
    (* Hendra 15082016 - related to beta function - constructor 3 with n; auto.*)
  Qed.

  Lemma Value_in_opt_sym : forall v1 v2 (*b1 b2*),
    Value_in_opt (*b1 b2*) v1 v2 ->
    Value_in_opt (*b2 b1*) v2 v1.
  Proof.
    intros.
    inversion_clear H; try constructor.
    apply Value_in_sym; auto.
  Qed.

  Lemma Value_in_trans : forall v1 v2 v3 (*b1 b2 b3*),
    (*FFun.is_inj b2 ->*)
    Value_in (*b1 b2*) v1 v2 ->
    Value_in (*b2 b3*) v2 v3 ->
    Value_in (*b1 b3*) v1 v3.
  Proof.
    intros.
    inversion H0; inversion H; subst; rewrite H4; constructor.
    (*inversion_clear H0 in H1; inversion_clear H1; try constructor.
    rewrite <- (H _ _ _ H3 H0) in H4.
    constructor 3 with n; auto.*)
  Qed.

  Lemma Value_in_opt_trans : forall v1 v2 v3 (*b1 b2 b3*),
    (*FFun.is_inj b2 ->*)
    Value_in_opt (*b1 b2*) v1 v2->
    Value_in_opt (*b2 b3*) v2 v3 ->
    Value_in_opt (*b1 b3*) v1 v3.
  Proof.
    intros.
    inversion_clear H in H0; inversion_clear H0; try constructor.
    (*inversion_clear H0 in H1; inversion_clear H1; try constructor.*)
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

  Lemma Reg_in_inv : forall obs k k' v v',
    Reg_in obs k k' v v' <->
      (~(L.leql k obs) /\ ~(L.leql k' obs)) \/ (Value_in v v').
  Proof.
    intros. split. 
      intros. inversion H. left; auto. right; auto.
      intros. inversion H.
      apply Reg_high_in; inversion H0; auto.
      apply Reg_nhigh_in; auto.
  Qed.

  Lemma Reg_in_sym : forall obs k k' v v', 
    Reg_in obs k k' v v' -> 
    Reg_in obs k' k v' v.
  Proof.
    intros.
    inversion H.
      constructor 1; auto.
      constructor 2; auto.
      apply Value_in_sym; auto.
  Qed.  

  Lemma Reg_in_refl : forall obs k v, Reg_in obs k k v v.
  Proof. intros. constructor 2. destruct v. constructor; auto. Qed.

  Lemma Reg_in_monotony_left : forall obs k k' v v' k'',
    Reg_in obs k k' v v' ->
    L.leql k k'' -> 
    Reg_in obs k'' k' v v'.
  Proof.
    intros. inversion H; subst. 
    constructor 1; auto. 
    apply not_leql_trans with (k1:=k) (k3:=obs) (k2:=k'') in H1; auto. 
    constructor 2; auto.
  Qed. 

 (* Lemma Regs_in_inv : forall r1 r2 rt1 rt2,
    Regs_in kobs r1 r2 rt1 rt2 -> forall (rn:DEX_Reg), In rn (VarMap.dom _ rt1) -> In rn (VarMap.dom _ rt2) ->
    (forall k k', Some k = VarMap.get _ rt1 rn -> Some k' = VarMap.get _ rt2 rn ->
      (~L.leql k kobs /\ ~L.leql k' kobs)) \/ 
    (forall v v', (Some v = DEX_Registers.get r1 rn /\ Some v' = DEX_Registers.get r2 rn /\ Value_in v v')).
  Proof.
    intros.
    inversion H.
    specialize (H3 rn H0 H1).
    apply VarMap.in_dom_get_some in H0.
    apply VarMap.in_dom_get_some in H1.
    apply not_none_some with (A:=L.t) (a:=VarMap.get L.t rt1 rn) in H0. admit. apply not_none_some with (A:=L.t) in H1.
    destruct H0; destruct H1.
    apply H4 in H0.
    inversion H0.
    
    left; split; auto.
    right. repeat (split; auto). 
    admit. admit.
 subst. admit. split; auto. *)
      

 Lemma Regs_in_sym : forall r1 r2 rt1 rt2,
    Regs_in kobs r1 r2 rt1 rt2 ->
    Regs_in kobs r2 r1 rt2 rt1.
  Proof.
    induction 1.
    constructor.
    intros. auto.
    intros.
    apply H0 with (k:=k') (k':=k) (v:=v') (v':=v) in H3; auto.
    apply Reg_in_sym; auto.
    (*apply Build_Regs_in with (r:=r1) (r':=r2) (rt:=rt1) (rt':=rt2).
    constructor 1 with (rn:=rn) (k:=k') (k':=k) (v:=v') (v':=v); auto.
      constructor 1; auto.
    constructor 1 with (rn:=rn) (k:=k') (k':=k) (v:=v') (v':=v); auto.
      constructor 2; apply Value_in_sym; trivial.*)
  Qed.

  Lemma st_in_sym : forall (*lvt b b'*) rt rt' r r',
    st_in kobs (*newArT ft lvt b b'*) rt rt' r r' ->
    st_in kobs (*newArT ft lvt b' b*) rt' rt r' r.
  Proof.
    intros.
    inversion_clear H; constructor.
    (*apply localvar_in_sym; auto.
    apply os_in_sym; auto.
    apply hp_in_sym; auto.*)
    apply Regs_in_sym; auto.
  Qed.
  Implicit Arguments st_in_sym.

  Lemma Value_in_opt_some_aux: forall ov ov' v v' (*b b'*), 
    Value_in (*b b'*) v v' -> 
    ov=(Some v)  -> 
    ov'= (Some v') -> 
    Value_in_opt (*b b'*) ov ov'.
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

  Hint Resolve 
    not_leql_join1 (*not_leql_join1'*) not_leql_join2 (*not_leql_join2'*) not_leql_trans 
    L.join_left L.join_right (*leql'_leql*)
    L.leql_trans : lattice.


End p.

  Hint Resolve 
    not_leql_join1 (*not_leql_join1'*) not_leql_join2 (*not_leql_join2'*) not_leql_trans 
    L.join_left L.join_right (*leql'_leql*)
    L.leql_trans : lattice.


(* 
*** Local Variables: ***
*** coq-prog-name: "~/Soft/src/coq-8.2pl1/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../Library" "-I" "../Library/Map/") ***
*** End: ***
 *)