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
| Build_Regs_in : 
  (forall (rn:DEX_Reg) v v' k k',
(*   In rn (DEX_Registers.dom r) -> In rn (DEX_Registers.dom r') -> *)
  Some v = DEX_Registers.get r rn -> Some v' = DEX_Registers.get r' rn ->
  Some k = VarMap.get _ rt rn -> Some k' = VarMap.get _ rt' rn ->
  Reg_in observable k k' v v') -> Regs_in observable r r' rt rt'.

(*
Inductive os_in (observable:L.t)  (b b':FFun.t Location) : OperandStack.t -> OperandStack.t -> TypeStack -> TypeStack -> Prop:=
| os_in_high : forall s s' st st', 
  high_st observable s st -> high_st observable s' st' -> 
  os_in observable b b' s s' st st'
| os_in_cons_high:  forall s s' st st' v v' (k k':L.t'),
  ~(L.leql k observable)->
  ~(L.leql k' observable)->
  os_in observable b b' s s' st st' -> 
  os_in observable b b' (v::s)  (v'::s') (k::st) (k'::st')
| os_in_cons:  forall s s' st st' v v' k,
  Value_in b b' v v' ->
  os_in observable b b' s s' st st' -> 
  os_in observable b b' (v::s) (v'::s') (k::st) (k::st').
*)
(*
Definition ffun_heap_compat (b:FFun.t Location) (h:Heap.t) : Prop :=
  forall loc, FFun.image b loc -> Heap.typeof h loc <> None.

Record hp_in (observable:L.t) (newArT : Method * PC -> L.t') (ft:FieldSignature -> L.t')  (b b': FFun.t Location) (h h': Heap.t) : Prop :=
  make_hp_in {
    object_in : forall n loc loc' f cn cn',
      b n = Some loc -> 
      b' n = Some loc' -> 
      Heap.typeof h loc = Some (Heap.LocationObject cn) ->
      Heap.typeof h' loc' = Some (Heap.LocationObject cn') ->
      L.leql (ft f) observable->
      Value_in_opt b b' 
      (Heap.get h (Heap.DynamicField loc f))
      (Heap.get h' (Heap.DynamicField loc' f));
    class_object_in : forall n loc loc',
      b n = Some loc -> 
      b' n = Some loc' -> 
      Heap.typeof h loc = Heap.typeof h' loc';
    compat_ffun : FFun.compat b b';
    static_heap_in : True;
    left_inj : FFun.is_inj b;
    right_inj : FFun.is_inj b';
    left_heap_compat : ffun_heap_compat b h;
    right_heap_compat : ffun_heap_compat b' h';
    array_in_elem : forall  n loc loc' i length tp mpc,
      b n = Some loc -> 
      b' n = Some loc' -> 
      Heap.typeof h loc = Some (Heap.LocationArray length tp mpc) ->
      (0 <= i < Int.toZ length)%Z ->
      L.leql (newArT mpc) observable ->
      Value_in_opt b b' 
      (Heap.get h (Heap.ArrayElement loc i))
      (Heap.get h' (Heap.ArrayElement loc' i))
  }.
*)
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
  indist_return_value observable s (*h1 h2*) (Normal None) (Normal None) (*b1 b2 *)
(*
| indist_return_exception_same_class : forall b1 b2 loc1 loc2 cn,
  Heap.typeof h1 loc1 = Some (Heap.LocationObject cn) ->  
  L.leql (s.(resExceptionType) cn) observable ->
  Value_in b1 b2 (Ref loc1) (Ref loc2) ->
  indist_return_value observable s h1 h2 (Exception loc1) (Exception loc2) b1 b2
| indist_return_exception_value : forall b1 b2 loc1 v2 cn,
  Heap.typeof h1 loc1 = Some (Heap.LocationObject cn) ->  
  ~ L.leql (s.(resExceptionType) cn) observable ->
  indist_return_value observable s h1 h2 (Exception loc1) (Normal v2) b1 b2
| indist_return_value_exception : forall b1 b2 loc2 v1 cn,
  Heap.typeof h2 loc2 = Some (Heap.LocationObject cn) ->  
  ~ L.leql (s.(resExceptionType) cn) observable ->
  indist_return_value observable s h1 h2 (Normal v1) (Exception loc2) b1 b2
| indist_return_exception_high : forall b1 b2 loc1 loc2 cn1 cn2,
  Heap.typeof h1 loc1 = Some (Heap.LocationObject cn1) ->  
  Heap.typeof h2 loc2 = Some (Heap.LocationObject cn2) ->  
  ~ L.leql (s.(resExceptionType) cn1) observable ->
  ~ L.leql (s.(resExceptionType) cn2) observable ->
  indist_return_value observable s h1 h2 (Exception loc1) (Exception loc2) b1 b2
*).

Inductive high_result (observable:L.t) (s:DEX_sign) (*h:Heap.t*) : DEX_ReturnVal -> Prop :=
| high_result_void : 
  s.(DEX_resType) = None ->
  high_result observable s (*h*) (Normal None)
| high_result_value : forall v k,
  s.(DEX_resType) = Some k ->
  ~ L.leql k observable ->
  high_result observable s (*h*) (Normal (Some v))
(*| high_result_exception : forall loc cn,
  Heap.typeof h loc = Some (Heap.LocationObject cn) ->
  ~ L.leql (s.(resExceptionType) cn) observable ->
  high_result observable s h (Exception loc)*).

(* Inductive indist_intra_return (observable:L.t) (p:ExtendedProgram) (s:sign) : 
  DEX_IntraNormalState -> TypeStack -> (*FFun.t Location -> 
  Heap.t ->*) ReturnVal -> (*FFun.t Location ->*) Prop :=
| indist_intra_return_ : forall (*h1 h2*) v2 (*b1 b2*) pc1 rt1 r1,
  (*hp_in observable (newArT p) (ft p) b1 b2 h1 h2 -> *)
  high_result observable s (*h2*) v2 ->
(*   high_st observable s1 st1 -> *)
  indist_intra_return observable p s (pc1,r1) rt1 v2. *)

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

(* Hendra 15082016 focus on DEX I
Record side_effect (newArT : Method * PC -> L.t') (ft:FieldSignature->L.t') (k:L.t)
  (h1 h2:Heap.t) : Prop := make_side_effect
  { side_effect_low_field :
    forall f loc cn,
      ~ L.leql k (ft f) -> 
      Heap.typeof h1 loc = Some (Heap.LocationObject cn) ->
      Heap.get h1 (Heap.DynamicField loc f) =
      Heap.get h2 (Heap.DynamicField loc f);
    side_effect_low_index :
      forall i mpc loc tp length,
        ~ L.leql k (newArT mpc) ->
        Heap.typeof h1 loc = Some (Heap.LocationArray length tp mpc) ->
        Heap.get h1 (Heap.ArrayElement loc i) =
        Heap.get h2 (Heap.ArrayElement loc i);
    side_effect_domain : forall loc, Heap.typeof h2 loc = None -> Heap.typeof h1 loc = None;
    side_effect_typeof : forall loc,
      Heap.typeof h1 loc <> None ->
      Heap.typeof h1 loc = Heap.typeof h2 loc
  }.
Implicit Arguments side_effect_low_field.
Implicit Arguments side_effect_low_index.
Implicit Arguments side_effect_domain.
Implicit Arguments side_effect_typeof.
*)

(* Hendra 15082016 focus on DEX I 
Module ExL. (* Extented levels *)

  Lemma leql_refl : forall l, L.leql' l l.
  Proof.
    destruct l; constructor; apply L.leql_refl.
  Qed.

  Lemma leql_trans : forall l1 l2 l3,
    L.leql' l1 l2 -> L.leql' l2 l3 -> L.leql' l1 l3.
  Proof.
    intros.
    inversion_mine H; inversion_mine H0; constructor; eapply L.leql_trans; eauto.
  Qed.

  Definition eq_dec : forall l l':L.t', {l=l'}+{~l=l'}.
  Proof.
    induction l; destruct l'.
    destruct (L.eq_dec k k0).
    subst; left; constructor.
    right; intro; elim n; inversion_mine H; trivial.
    right; intro; inversion H.
    right; intro; inversion H.
    destruct (L.eq_dec k k0).
    destruct (IHl l').
    subst; left; constructor; auto.
    right; intro; elim n; inversion H; trivial.
    right; intro; elim n; inversion H; trivial.
  Defined.

  Definition leql_dec : forall l l':L.t', {L.leql' l l'}+{~L.leql' l l'}.
  Proof.
    destruct l; destruct l'.
    destruct (L.leql_dec k k0).
    left; constructor; auto.
    right; intro; elim n; inversion_mine H; trivial.
    right; intro; inversion_mine H.
    right; intro; inversion_mine H.
    destruct (L.leql_dec k k0).
    destruct (eq_dec l l').
    subst; left; constructor; auto.
    right; intro; elim n; inversion_mine H; trivial.
    right; intro; elim n; inversion_mine H; trivial.
  Qed.

  Lemma join_left : forall l l', L.leql l (L.head (L.join' l l')).
  Proof.
    destruct l'; simpl; apply L.join_left.
  Qed.

  Lemma join_left' : forall l l', L.leql l (L.join' l l').
  Proof.
    destruct l'; simpl; apply L.join_left.
  Qed.

  Lemma join_right : forall l l', L.leql (L.head l') (L.join' l l').
  Proof.
    destruct l'; simpl; apply L.join_right.
  Qed.

  Lemma join_right' : forall l l', L.leql' l' (L.join' l l').
  Proof.
    destruct l'; simpl; constructor; apply L.join_right.
  Qed.

  Lemma elem_join : forall k1 k2,
    L.elem (L.join' k1 k2) = L.elem k2.
  Proof.
    unfold L.join', L.elem; intros.
    destruct k2; auto.
  Qed.

End ExL.
*)
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

  Lemma Regs_in_sym : forall r1 r2 rt1 rt2,
    Regs_in kobs r1 r2 rt1 rt2 ->
    Regs_in kobs r2 r1 rt2 rt1.
  Proof.
    induction 1.
    constructor.
    intros. apply H with (k:=k') (k':=k) (v:=v') (v':=v) in H0; auto.
    apply Reg_in_sym; auto.
    (*apply Build_Regs_in with (r:=r1) (r':=r2) (rt:=rt1) (rt':=rt2).
    constructor 1 with (rn:=rn) (k:=k') (k':=k) (v:=v') (v':=v); auto.
      constructor 1; auto.
    constructor 1 with (rn:=rn) (k:=k') (k':=k) (v:=v') (v':=v); auto.
      constructor 2; apply Value_in_sym; trivial.*)
  Qed.

(*
  Lemma os_in_sym : forall s1 s2 st1 st2 b1 b2,
    os_in kobs b1 b2 s1 s2 st1 st2-> 
    os_in kobs b2 b1 s2 s1 st2 st1.
  Proof.
    induction 1.
    constructor 1; auto.
    constructor 2; auto.
    constructor 3; auto.
    apply Value_in_sym; auto.
  Qed.

  Lemma os_in_high_high : forall b b' s s' st st',
    os_in kobs b b' s s' st st' ->
    high_st kobs s st -> high_st kobs s' st'.
  Proof.
    induction 1; intros; auto.
    inversion_clear H2; constructor; auto.
    inversion_clear H1; constructor; auto.
  Qed.

  Lemma os_in_trans : forall s1 s2 st1 st2 b1 b2 ,
    os_in kobs b1 b2 s1 s2 st1 st2 -> forall s3 st3 b3,
      os_in kobs b2 b3 s2 s3 st2 st3 ->
      FFun.is_inj b2 ->
      os_in kobs b1 b3 s1 s3 st1 st3.
  Proof.
    induction 1; intros.
    constructor 1; auto.
    eapply os_in_high_high; eauto.
    inversion_mine H2.
    constructor 1; auto.
    constructor; auto.
    assert (HH:=os_in_sym _ _ _ _ _ _ H1).
    inversion_mine H4.
    eapply os_in_high_high; eauto.
    constructor 2; auto.
    constructor 2; auto.
    inversion_mine H1.
    constructor 1; auto.
    inversion_clear H3.
    constructor; auto.
    assert (HH:=os_in_sym _ _ _ _ _ _ H0).
    eapply os_in_high_high; eauto.
    constructor 2; auto.
    constructor 3; auto.
    eapply Value_in_trans; eauto.
  Qed.

  Lemma localvar_in_sym : forall lvt l1 l2 b1 b2,
    localvar_in kobs lvt b1 b2 l1 l2 ->
    localvar_in kobs lvt b2 b1 l2 l1.
  Proof.
    repeat intro.
    apply Value_in_opt_sym; auto.
  Qed.

  Lemma localvar_in_trans : forall lvt l1 l2 l3 b1 b2 b3,
    FFun.is_inj b2 ->
    localvar_in kobs lvt b1 b2 l1 l2 -> 
    localvar_in kobs lvt b2 b3 l2 l3 -> 
    localvar_in kobs lvt b1 b3 l1 l3.
  Proof.
    repeat intro.
    apply Value_in_opt_trans with (LocalVar.get l2 x) b2; auto.
  Qed.

  Lemma hp_in_sym : forall h1 h2 b1 b2,
    hp_in kobs newArT ft b1 b2 h1 h2 -> hp_in kobs newArT ft b2 b1 h2 h1.
  Proof.
    intros.
    destruct H; constructor; auto.
    intros.  
    apply Value_in_opt_sym; auto.
    eapply object_in0; eauto.
    intros.
    rewrite (class_object_in0 n loc' loc); auto.
    intros n; generalize (compat_ffun0 n); intuition.
    intros.  
    apply Value_in_opt_sym; auto.
    eapply array_in_elem0; eauto.
    rewrite (class_object_in0 n loc' loc); eauto.
  Qed.
*)

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

(*
  Lemma hp_in_trans : forall h1 h2 h3 b1 b2 b3,
    hp_in kobs newArT ft b1 b2 h1 h2 -> 
    hp_in kobs newArT ft b2 b3 h2 h3 ->
    hp_in kobs newArT ft b1 b3 h1 h3.
  Proof.
    intros.
    destruct H; destruct H0.
    constructor; auto.
    intros.
    destruct (compat_ffun1 n).
    caseeq (b2 n); intros.
    apply Value_in_opt_trans with 
      (Heap.get h2 (Heap.DynamicField l f)) b2; auto.
    eapply object_in0; eauto.
    rewrite <- (class_object_in0 n loc l); eauto.
    eapply object_in1; eauto.
    rewrite <- (class_object_in0 n loc l); eauto.
    rewrite H4 in H0; auto; discriminate.
    intros.
    destruct (compat_ffun1 n).
    caseeq (b2 n); intros.
    rewrite (class_object_in0 n loc l); auto.
    rewrite (class_object_in1 n l loc'); auto.
    rewrite H1 in H0; auto; discriminate.  
    intros n.
    generalize (compat_ffun0 n); 
      generalize (compat_ffun1 n); intuition.
    intros.
    destruct (compat_ffun1 n).
    caseeq (b2 n); intros.
    apply Value_in_opt_trans with 
      (Heap.get h2 (Heap.ArrayElement l i)) b2; auto.
    eapply array_in_elem0; eauto.
    eapply array_in_elem1; eauto.
    rewrite <- (class_object_in0 _ _ _ H H6); eauto.
    rewrite H4 in H0; auto; discriminate.
  Qed.
*)
  Lemma Value_in_opt_some_aux: forall ov ov' v v' (*b b'*), 
    Value_in (*b b'*) v v' -> 
    ov=(Some v)  -> 
    ov'= (Some v') -> 
    Value_in_opt (*b b'*) ov ov'.
  Proof.
    intros;  subst; constructor; auto.
  Qed.
(*
  Lemma ffun_extends_val_in: forall b b' v v' loc loc',
    Value_in b b' v v' ->
    Value_in (FFun.extends b loc) (FFun.extends b' loc') 
    v v'.
  Proof.
    intros; inversion_clear H; try constructor.
    constructor 3 with n; auto.
    apply FFun.extends_old; auto.
    apply FFun.extends_old; auto.
  Qed.

  Lemma ffun_extends_val_in_opt: forall b b' v v' loc loc',
    Value_in_opt b b' v v' ->
    Value_in_opt (FFun.extends b loc) (FFun.extends b' loc')
    v v'.
  Proof.
    intros; inversion H; subst; try constructor.
    apply ffun_extends_val_in; auto.
  Qed.

  Lemma Value_in_extends_object : forall b1 b2 loc1 loc2 h1 h2,
    ffun_heap_compat b1 h1 ->
    ffun_heap_compat b2 h2 ->
    Heap.typeof h1 loc1 = None ->
    Heap.typeof h2 loc2 = None ->
    FFun.compat b1 b2 ->
    Value_in 
    (FFun.extends b1 loc1) (FFun.extends b2 loc2)
    (Ref loc1) (Ref loc2) .
  Proof.
    intros.
    constructor 3 with (FFun.next b1); auto.
    apply FFun.extends_new.
    rewrite (FFun.compat_implies_next _ b1 b2); auto.
    apply FFun.extends_new.
  Qed.
*)

(*
  Lemma localvar_in_upd_low: 
    forall lvt (v v' : value) (l l' : LocalVar.t) 
      (x : Var) (b b': FFun.t Location), 
      localvar_in kobs lvt b b' l l' -> 
      Value_in b b' v v' -> 
      localvar_in kobs lvt b b' (LocalVar.update l x v) (LocalVar.update l' x v').
  Proof.
    intros; intro; intros.
    case (eq_excluded_middle _ x x0); intros; subst; auto.
    repeat (rewrite LocalVar.get_update_new); repeat split; 
      constructor; auto.
    repeat (rewrite LocalVar.get_update_old); auto.
  Qed.

  Lemma localvar_in_upd_high: forall lvt v v' l l' x b b',
    localvar_in kobs lvt b b' l l' -> 
    ~(L.leql (lvt x) kobs) -> 
    localvar_in kobs lvt b b' (LocalVar.update l x v) (LocalVar.update l' x v').
  Proof.
    intros; intro; intros.
    case (eq_excluded_middle _ x x0); intros; subst.
    rewrite LocalVar.get_update_new; auto.
    rewrite LocalVar.get_update_new; auto.
    intuition. 
    repeat (rewrite LocalVar.get_update_old); auto.
  Qed.

  Lemma localvar_in_upd_high_right: forall lvt v' l l' x b b',
    localvar_in kobs lvt b b' l l' -> 
    ~(L.leql (lvt x) kobs) -> 
    localvar_in kobs lvt b b' l (LocalVar.update l' x v').
  Proof.
    intros; intro; intros.
    case (eq_excluded_middle _ x x0); intros; subst; auto.
    rewrite LocalVar.get_update_new; auto.  
    intros; elim H0; auto.
    repeat (rewrite LocalVar.get_update_old); auto.
  Qed.

  Lemma localvar_in_upd_high_left: forall lvt v l l' x b b',
    localvar_in kobs lvt b b' l l' -> 
    ~(L.leql (lvt x) kobs) -> 
    localvar_in kobs lvt b b' (LocalVar.update l x v) l'.
  Proof.
    intros.
    apply localvar_in_sym; apply localvar_in_upd_high_right; auto.
    apply localvar_in_sym; trivial.
  Qed.

  Lemma ffun_extends_localvar_in:  forall lvt l l' b b' loc loc',
    localvar_in kobs lvt b b' l l'->
    localvar_in kobs lvt (FFun.extends b loc) (FFun.extends b' loc') l l'.
  Proof.
    repeat intro.
    apply ffun_extends_val_in_opt; auto.
  Qed.

  Lemma high_st_length: forall s st,
    high_st kobs s st-> length s=length st.
  Proof.
    intros.
    elim H; intros; auto.
    simpl; auto.
  Qed.

  Lemma os_in_length: forall s s' st st' b b',
    os_in kobs b b' s s' st st' -> 
    length s=length st /\ length s'=length st'.
  Proof.
    intros.
    elim H; intros; auto.
    split; eapply high_st_length; eauto.
    destruct H3; split; simpl; auto.
    destruct H2; split; simpl; auto.
  Qed.

  Lemma os_in_tl: forall s s' v v' st st' k k' b b',
    os_in kobs b b' (v::s) (v'::s') (k::st) (k'::st') -> 
    os_in kobs b b' s s' st st'.
  Proof.
    intros; inversion H; subst; auto.
    inversion H0; inversion H1; inversion H2; inversion H3;
      subst.
    constructor; auto.
  Qed.

  Lemma os_in_hd : forall s s' v v' st st' k k' b b',
    os_in kobs b b' (v::s) (v'::s') (k::st) (k'::st') ->
    (L.leql k kobs \/ L.leql k' kobs) ->
    Value_in b b' v v'.
  Proof.
    intros. 
    inversion H; subst; try (intuition; fail). 
    inversion H2; inversion H1; inversion H3; inversion H4; subst; intuition.
  Qed.

  Lemma lift_os_high: forall st k s,
    high_st kobs s st -> high_st kobs s (lift k st).
  Proof.
    intros.
    elim H; intros.
    simpl; constructor.
    simpl; constructor; auto.
    intro.
    apply H0.
    apply L.leql_trans with (L.head (L.join' k k0)); auto.
    apply ExL.join_right.
  Qed.

  Lemma elift_os_high: forall m pc st k s,
    high_st kobs s st -> high_st kobs s (elift m pc k st).
  Proof.
    unfold elift; intros.
    destruct (throwableAt m pc); auto.
    apply lift_os_high; auto.
  Qed.

  Lemma os_in_lift: forall k b b' s s' st st',
    os_in kobs b b' s s' st st' ->
    os_in kobs b b' s s' (lift k st) (lift k st').
  Proof.
    intros.
    elim H; intros.
    apply os_in_high.
    apply  lift_os_high; auto.
    apply  lift_os_high; auto.

    simpl; apply os_in_cons_high.
    intro.
    elim H0.
    apply L.leql_trans with (L.head (L.join' k k0)); auto.
    apply ExL.join_right.
    intro.
    elim H1.
    apply L.leql_trans with (L.head (L.join' k k')); auto.
    apply ExL.join_right.
    assumption.
    simpl; apply os_in_cons; auto.
  Qed.

  Lemma os_in_elift: forall m pc k b b' s s' st st',
    os_in kobs b b' s s' st st' ->
    os_in kobs b b' s s' (elift m pc k st) (elift m pc k st').
  Proof.
    unfold elift; intros.
    destruct (throwableAt m pc); simpl; auto.
    eapply os_in_lift; eauto.
  Qed.



  Lemma os_in_same_num_hd : forall s s' st st' b b' k n,
    os_in kobs b b' s s' st st' ->
    os_in kobs b b' (Num n::s) (Num n::s') (k::st) (k::st').
  Proof.
    intros.
    constructor 3; auto;  constructor.
  Qed.

  Lemma ffun_extends_os_in: forall s s' st st' b b' loc loc',
    os_in kobs b b' s s' st st' ->
    os_in kobs (FFun.extends b loc) (FFun.extends b' loc') 
    s s' st st'.
  Proof.
    intros.
    induction H; intros; auto.
    constructor; auto.
    apply os_in_cons_high; auto.
    apply os_in_cons; auto.
    apply ffun_extends_val_in; auto.
  Qed.

  Lemma os_in_cons_cases : forall v1 s1 v2 s2 k1 st1 k2 st2 b1 b2,
    os_in kobs b1 b2 (v1::s1) (v2::s2) (k1::st1) (k2::st2)->
    (Value_in b1 b2 v1 v2 /\ k1=k2) \/
    (~ L.leql k1 kobs /\ ~ L.leql k2 kobs).
  Proof.
    intros.
    inversion_clear H; auto.
    inversion_clear H0; inversion_clear H1; inversion_clear H2; inversion_clear H3; auto.
  Qed.

  Lemma os_in_cons_cases2 : forall v1 s1 v2 s2 k1 st1 k2 st2 b1 b2,
    os_in kobs b1 b2 (v1::s1) (v2::s2) (k1::st1) (k2::st2) ->
    (Value_in b1 b2 v1 v2 /\ k1=k2 /\ L.leql k1 kobs) \/
    (~ L.leql k1 kobs /\ ~ L.leql k2 kobs).
  Proof.
    intros.
    destruct (L.leql_dec k1 kobs);
      elim os_in_cons_cases with (1:=H); intros (U1,U2); subst;
        try contradiction; intuition.
  Qed.

  Implicit Arguments os_in_tl.

(****************** USED IN PUTFIELD ************************************)

  Lemma ffun_heap_compat_update : forall h b am v,
    ffun_heap_compat b h ->
    ffun_heap_compat b (Heap.update h am v).
  Proof.
    unfold ffun_heap_compat; intros.
    rewrite Heap.typeof_update_same; auto.
  Qed.

  Lemma ffun_heap_compat_extends : forall h c h' b loc,
    ffun_heap_compat b h ->
    Heap.new h p c = Some (loc,h') ->
    ffun_heap_compat (FFun.extends b loc) h'.
  Proof.
    unfold ffun_heap_compat; intros.
    destruct (Location_dec loc loc0).
    subst.
    rewrite (@Heap.new_typeof h p c loc0 h' H0).
    discriminate.
    rewrite (@Heap.new_typeof_old h p c loc loc0 h' H0); auto.
    apply H.
    destruct H1.
    elim FFun.extends_case with Location b x loc loc0; auto; intros.
    exists x; auto.
    elim n; intuition.
  Qed.

  Lemma ffun_heap_compat_new : forall h c h' b loc,
    ffun_heap_compat b h ->
    Heap.new h p c = Some (loc,h') ->
    ffun_heap_compat b h'.
  Proof.
    unfold ffun_heap_compat; intros.
    destruct (Location_dec loc loc0).
    subst.
    rewrite (@Heap.new_typeof h p c loc0 h' H0).
    discriminate.
    rewrite (@Heap.new_typeof_old h p c loc loc0 h' H0); auto.
  Qed.

  Lemma leql'_leql : forall k1 k2,
    L.leql' k1 k2 -> L.leql k1 k2.
  Proof.
    intros.
    inversion_clear H; simpl; auto.
  Qed.

  Lemma hp_in_arraystore_high_update_left : forall loc b b' h h' i v length tp mpc,
    hp_in kobs newArT ft b b' h h' ->
    ~ L.leql (newArT mpc) kobs ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp mpc) ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.ArrayElement loc i) v) h'.
  Proof.
    intros.
    destruct H; split; auto; intros.
    rewrite Heap.get_update_old; try discriminate.
    eapply object_in0; eauto.
    rewrite Heap.typeof_update_same in H3; eauto.   

    rewrite Heap.typeof_update_same; eauto.

    repeat intro.
    rewrite Heap.typeof_update_same in H2.
    elim (left_heap_compat0 loc0); auto.

    rewrite Heap.typeof_update_same in H3.
    destruct (Location_dec loc loc0); [subst|idtac].
    rewrite H1 in H3; inversion_mine H3; contradiction.
    rewrite Heap.get_update_old.
    eapply array_in_elem0; eauto.
    intros HH; elim n0; inversion_mine HH; auto.
  Qed.

  Lemma hp_in_arraystore_high_update_right : forall loc b b' h h' i v length tp mpc,
    hp_in kobs newArT ft b b' h h' ->
    ~ L.leql (newArT mpc) kobs ->
    Heap.typeof h' loc = Some (Heap.LocationArray length tp mpc) ->
    hp_in kobs newArT ft b b'
    h (Heap.update h' (Heap.ArrayElement loc i) v).
  Proof.
    intros.
    apply hp_in_sym.
    eapply hp_in_arraystore_high_update_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma hp_in_arraystore : forall b b' h h' ke ke' loc loc' length length' tp tp' i v v',
    hp_in kobs newArT ft b b' h h' ->
    Value_in b b' v v' ->
    Value_in b b' (Ref loc) (Ref loc') ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp ke) ->
    Heap.typeof h' loc' = Some (Heap.LocationArray length' tp' ke') ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.ArrayElement loc i) v)
    (Heap.update h' (Heap.ArrayElement loc' i) v').
  Proof.
    intros.
    destruct H; split; intros; auto.

    repeat (rewrite Heap.get_update_old; try discriminate).
    eapply object_in0; eauto.
    rewrite Heap.typeof_update_same in H5; eauto.   
    rewrite Heap.typeof_update_same in H6; eauto.   

    repeat (rewrite Heap.typeof_update_same); eauto.

    repeat intro.
    rewrite Heap.typeof_update_same in H4.
    elim (left_heap_compat0 loc0); auto.

    repeat intro.
    rewrite Heap.typeof_update_same in H4.
    elim (right_heap_compat0 loc0); auto.

    rewrite Heap.typeof_update_same in H5.
    destruct (Location_dec loc loc0); [subst|idtac].
    DiscrimateEq.
    inversion_mine H1.
    assert (loc'=loc'0).
    apply FFun.inv_aux with n0 n b b' loc0 loc0; auto. 
    clear H9 H10; subst.
    rewrite (class_object_in0 _ _ _ H H4) in H5; DiscrimateEq.
    destruct (eq_excluded_middle _ i i0); [subst|idtac].
    repeat (rewrite Heap.get_update_same).
    constructor; auto.
    constructor 3 with length' tp' ke'; trivial.
    constructor 3 with length' tp' ke'; trivial.
    rewrite (class_object_in0 _ _ _ H H4); auto.
    repeat (rewrite Heap.get_update_old).
    eapply array_in_elem0; eauto.
    rewrite (class_object_in0 _ _ _ H H4); eauto.
    intros HH; elim H1; inversion_mine HH; auto.
    intros HH; elim H1; inversion_mine HH; auto.
    repeat (rewrite Heap.get_update_old).
    eapply array_in_elem0; eauto.
    intros HH; inversion_mine HH.
    inversion_mine H1.
    assert (loc0=loc).
    apply FFun.inv_aux with n n1 b' b loc'0 loc'0; auto. 
    subst; intuition.
    intros HH; elim n0; inversion_mine HH; auto.
  Qed.

  Lemma hp_in_putfield_ffun : forall loc loc' b b' h h' f v v' cn cn',
    hp_in kobs newArT ft b b' h h' ->
    Value_in b b' v v' ->
    Value_in b b' (Ref loc) (Ref loc') ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    Heap.typeof h' loc' = Some (Heap.LocationObject cn') ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.DynamicField loc f) v)
    (Heap.update h' (Heap.DynamicField loc' f) v').
  Proof.
    intros; constructor; auto; intros.

    elim (Location_dec loc loc0);
      elim (eq_excluded_middle _ f f0); intros; subst.
    rewrite Heap.get_update_same; auto.
    replace loc'0 with loc'.
    rewrite Heap.get_update_same; auto.
    constructor; auto.
    constructor 2 with cn'; auto.
    inversion_mine H1.
    apply FFun.inv_aux with n0 n b b' loc0 loc0; auto. 
    eapply left_inj; eauto.
    eapply right_inj; eauto.
    constructor 2 with cn; auto.

    rewrite Heap.get_update_old.
    rewrite Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ _ H); eauto.
    rewrite Heap.typeof_update_same in H7; eauto.
    intros HH; elim H9; congruence.
    intros HH; elim H9; congruence.

    rewrite Heap.get_update_old.
    rewrite Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ _ H); eauto.
    rewrite Heap.typeof_update_same in H6; eauto.
    rewrite Heap.typeof_update_same in H7; eauto.
    intros HH; injection HH; intros; subst.
    elim b0.
    inversion_mine H1.
    apply (FFun.inv_aux _ n0 n b' b loc'0 loc loc'0 loc0); auto.
    eapply right_inj; eauto.
    eapply left_inj; eauto.
    intros HH; elim b0; congruence.

    rewrite Heap.get_update_old.
    rewrite Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ _ H); eauto.
    rewrite Heap.typeof_update_same in H6; eauto.
    rewrite Heap.typeof_update_same in H7; eauto.
    intros HH; elim b0; congruence.
    intros HH; elim b0; congruence.

    repeat rewrite Heap.typeof_update_same.
    eapply class_object_in; eauto.
    destruct H; auto.
    destruct H; auto.
    destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.

    rewrite Heap.typeof_update_same in H6.
    rewrite Heap.get_update_old; try discriminate.  
    rewrite Heap.get_update_old; try discriminate.  
    eapply (array_in_elem _ _ _ _ _ _ _ H); eauto.
  Qed.

  Lemma hp_in_putfield_high_update_left : forall loc b b' h h' f v cn,
    hp_in kobs newArT ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.DynamicField loc f) v) h'.
  Proof.
    intros; constructor; auto; intros.
    assert (f<>f0).
    intro; subst; intuition.
    repeat rewrite Heap.get_update_old.
    eapply (object_in _ _ _ _ _ _ _ H); eauto.
    rewrite Heap.typeof_update_same in H4; eauto.
    intros HH; elim H7; congruence.
    rewrite Heap.typeof_update_same.
    eapply class_object_in; eauto.
    destruct H; auto.
    destruct H; auto.
    destruct H; auto.
    apply ffun_heap_compat_update; destruct H; auto.
    destruct H; auto.
    rewrite Heap.get_update_old; try discriminate.
    rewrite Heap.typeof_update_same in H4.
    eapply (array_in_elem _ _ _ _ _ _ _ H); eauto.
  Qed.

  Lemma hp_in_putfield_high_update_right : forall loc b b' h h' f v cn,
    hp_in kobs newArT ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    Heap.typeof h' loc = Some (Heap.LocationObject cn) ->
    hp_in kobs newArT ft b b'
    h (Heap.update h' (Heap.DynamicField loc f) v).
  Proof.
    intros.
    apply hp_in_sym.
    eapply hp_in_putfield_high_update_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma hp_in_putfield_high : forall loc loc' b b' h h' f v v' cn cn',
    hp_in kobs newArT ft b b' h h' ->
    ~ (L.leql (ft f) kobs) ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    Heap.typeof h' loc' = Some (Heap.LocationObject cn') ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.DynamicField loc f) v)
    (Heap.update h' (Heap.DynamicField loc' f) v').
  Proof.
    intros.
    apply hp_in_putfield_high_update_left with cn; auto.
    apply hp_in_putfield_high_update_right with cn'; auto.
  Qed.

  Lemma Compat_ex : forall h am, Heap.Compat h am \/ ~ Heap.Compat h am.
  Proof.
    intros.
    apply excluded_middle.
  Qed.

  Lemma ffun_extends_hp_in: forall c b b' h h' hn hn' loc loc',
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc hn) ->
    Heap.new h' p (Heap.LocationObject c) = Some (pair loc' hn') ->
    hp_in kobs newArT ft (FFun.extends b loc) (FFun.extends b' loc') 
    hn hn'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.
    elim FFun.extends_case with Location b n loc loc0; intros; Cleanand; auto.
    assert (Haux:=FFun.compat_extends _ _ _ _ _ _ _ compat_ffun0 H6 H2).
    apply ffun_extends_val_in_opt.
    rewrite (@Heap.new_object_no_change h p c loc hn); auto.
    rewrite (@Heap.new_object_no_change h' p c loc' hn'); auto.

    assert (Hclass:=class_object_in0 _ _ _ H6 Haux).
    elim Compat_ex with h (@Heap.DynamicField loc0 f); intros Hcomp.
    inversion_clear Hcomp. 
    generalize H7; rewrite Hclass; intros.
    apply object_in0 with n cn0 cn0; auto.
    rewrite (@Heap.get_uncompat h); auto.
    rewrite (@Heap.get_uncompat h').
    constructor.
    intros HH; inversion_clear HH.
    elim Hcomp; constructor 2 with cn0.
    rewrite Hclass; auto.
    intros fs Hi; injection Hi; intros; subst.
    elim right_heap_compat0 with loc'.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H1).
    intros fs Hi; injection Hi; intros; subst.
    elim left_heap_compat0 with loc.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H0).

  (***)

    subst. 
    rewrite (FFun.compat_implies_next _ _ _ compat_ffun0) in H2.
    rewrite FFun.extends_new in H2.
    injection H2; clear H2; intros; subst.
    destruct (excluded_middle (defined_field p c f)) as [d|d].
    inversion_clear d.
    rewrite (@Heap.new_defined_object_field h p c f x loc0 hn); auto.
    rewrite (@Heap.new_defined_object_field h' p c f x loc'0 hn'); auto.
    constructor.
    unfold init_field_value.
    destruct (FIELD.initValue x); try constructor.
    unfold init_value. 
    destruct FIELDSIGNATURE.type; constructor.
    rewrite (@Heap.new_undefined_object_field h p c f loc0 hn); auto.
    rewrite (@Heap.new_undefined_object_field h' p c f loc'0 hn'); auto.
    constructor.

    elim FFun.extends_case with (1:= H); intros.
    assert (b' n = Some loc'0).
    apply FFun.compat_extends with b loc0 loc'; auto.
    destruct (Location_dec loc loc0); destruct (Location_dec loc' loc'0); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationObject c) loc0 hn); auto.
    rewrite (@Heap.new_typeof h' p (Heap.LocationObject c) loc'0 hn'); auto.
    assert (T:=@Heap.new_fresh_location h p (Heap.LocationObject c) loc0 hn H0).
    elim (left_heap_compat0 loc0); auto.
    exists n; auto.
    assert (T:=@Heap.new_fresh_location h' p (Heap.LocationObject c) loc'0 hn' H1).
    elim (right_heap_compat0 loc'0); auto.
    exists n; auto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationObject c) loc loc0 hn); auto.
    rewrite (@Heap.new_typeof_old h' p (Heap.LocationObject c) loc' loc'0 hn'); auto.
    eapply class_object_in0; eauto.
    destruct H3; subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationObject c) loc0 hn); auto.
    rewrite (FFun.compat_implies_next _ _ _ compat_ffun0) in H2.
    rewrite (FFun.extends_new _ b' loc') in H2.
    injection H2; intros; subst.
    rewrite (@Heap.new_typeof h' p (Heap.LocationObject c) loc'0 hn'); auto.
    apply FFun.compat_preserved_by_extends; auto.
    apply FFun.extends_inj; auto.
    intro.
    elim (left_heap_compat0 _ H).
    eapply Heap.new_fresh_location; eauto.
    apply FFun.extends_inj; auto.
    intro.
    elim (right_heap_compat0 _ H).
    eapply Heap.new_fresh_location; eauto.
    apply ffun_heap_compat_extends with (2:=H0); auto.
    apply ffun_heap_compat_extends with (2:=H1); auto.

    elim Location_dec with loc loc0; intros; subst.
    rewrite (@Heap.new_typeof _ _ _ _ _ H0) in H3; discriminate.
    apply ffun_extends_val_in_opt.
    elim FFun.extends_case with Location b n loc loc0; intros; Cleanand; auto.
    rewrite (@Heap.new_object_no_change _ _ _ _ _ (Heap.ArrayElement loc0 i) H0).
    rewrite (@Heap.new_object_no_change _ _ _ _ _ (Heap.ArrayElement loc'0 i) H1).
    eapply array_in_elem0; eauto.
    apply (FFun.compat_extends _ _ _ _ _ _ _ compat_ffun0 H6 H2).
    rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H0 b0) in H3; eauto.
    intros; discriminate.
    intros; discriminate.
    contradiction.
  Qed.
*)
  Lemma ex_comp_Z : forall x y z:Z,
    (x <= y < z \/ ~ x <= y < z)%Z.
  Proof.
    intros.
    destruct (Z_le_dec x y).
    destruct (Z_lt_dec y z); intuition.
    intuition.
  Qed.
(*
  Lemma ffun_extends_hp_in_array: forall length tp x b b' h h' hn hn' loc loc',
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h  p (Heap.LocationArray length tp x) = Some (pair loc hn) ->
    Heap.new h' p (Heap.LocationArray length tp x) = Some (pair loc' hn') ->
    hp_in kobs newArT ft (FFun.extends b loc) (FFun.extends b' loc') 
    hn hn'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.
    elim Location_dec with loc loc0; intros; subst.
    rewrite (@Heap.new_typeof _ _ _ _ _ H0) in H3; discriminate.
    elim Location_dec with loc' loc'0; intros; subst.
    rewrite (@Heap.new_typeof _ _ _ _ _ H1) in H4; discriminate.
    apply ffun_extends_val_in_opt.
    elim FFun.extends_case with Location b n loc loc0; intros; Cleanand; auto.
    rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.DynamicField loc0 f) H0).
    rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.DynamicField loc'0 f) H1).
    eapply object_in0; eauto.
    apply (FFun.compat_extends _ _ _ _ _ _ _ compat_ffun0 H6 H2).
    rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H0 b0) in H3; eauto.
    rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H1 b1) in H4; eauto.
    intros; discriminate.
    intros; discriminate.
    contradiction.

    elim FFun.extends_case with (1:= H); intros.
    assert (b' n = Some loc'0).
    apply FFun.compat_extends with b loc0 loc'; auto.
    destruct (Location_dec loc loc0); destruct (Location_dec loc' loc'0); subst.
    rewrite (@Heap.new_typeof h p  (Heap.LocationArray length tp x) loc0 hn); auto.
    rewrite (@Heap.new_typeof h' p (Heap.LocationArray length tp x) loc'0 hn'); auto.
    assert (T:=@Heap.new_fresh_location h  p (Heap.LocationArray length tp x) loc0 hn H0).
    elim (left_heap_compat0 loc0); auto.
    exists n; auto.
    assert (T:=@Heap.new_fresh_location h' p (Heap.LocationArray length tp x) loc'0 hn' H1).
    elim (right_heap_compat0 loc'0); auto.
    exists n; auto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray length tp x) loc loc0 hn); auto.
    rewrite (@Heap.new_typeof_old h' p (Heap.LocationArray length tp x) loc' loc'0 hn'); auto.
    eapply class_object_in0; eauto.
    destruct H3; subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationArray length tp x) loc0 hn); auto.
    rewrite (FFun.compat_implies_next _ _ _ compat_ffun0) in H2.
    rewrite (FFun.extends_new _ b' loc') in H2.
    injection H2; intros; subst.
    rewrite (@Heap.new_typeof h' p (Heap.LocationArray length tp x) loc'0 hn'); auto.
    apply FFun.compat_preserved_by_extends; auto.
    apply FFun.extends_inj; auto.
    intro.
    elim (left_heap_compat0 _ H).
    eapply Heap.new_fresh_location; eauto.
    apply FFun.extends_inj; auto.
    intro.
    elim (right_heap_compat0 _ H).
    eapply Heap.new_fresh_location; eauto.
    apply ffun_heap_compat_extends with (2:=H0); auto.
    apply ffun_heap_compat_extends with (2:=H1); auto.

    elim FFun.extends_case with Location b n loc loc0; intros; Cleanand; auto.
    assert (loc<>loc0).
    intro; subst.
    elim left_heap_compat0 with loc0.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H0).
    assert (Haux:=FFun.compat_extends _ _ _ _ _ _ _ compat_ffun0 H6 H2).
    assert (loc'<>loc'0).
    intro; subst.
    elim right_heap_compat0 with loc'0.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H1).
    rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.ArrayElement loc0 i) H0).
    rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.ArrayElement loc'0 i) H1).
    apply ffun_extends_val_in_opt.
    eapply array_in_elem0; eauto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray length tp x) loc loc0 hn) in H3; eauto.
    intros; intro HH; injection HH; intuition.
    intros; intro HH; injection HH; intuition.
    subst.
    rewrite (FFun.compat_implies_next _ b b') in H2; auto.
    rewrite FFun.extends_new in H2; inversion_mine H2.
    rewrite (@Heap.new_typeof h p  (Heap.LocationArray length tp x) loc0 hn) in H3; auto.
    inversion_mine H3.
    rewrite (@Heap.new_valid_array_index _ _ _ _ _ i _ _ H0); auto.
    rewrite (@Heap.new_valid_array_index _ _ _ _ _ i _ _ H1); auto.
    constructor.
    destruct tp0; simpl; constructor.
  Qed.

  Lemma ffun_extends_hp_in_newarray_left: forall p tp length x b b' h h' hn loc,
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h p (Heap.LocationArray tp length x) = Some (pair loc hn) ->
    hp_in kobs newArT ft b b' hn h'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.

    destruct (Location_dec loc0 loc); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationArray tp length x) loc hn) in H2; auto; discriminate.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray tp length x) loc loc0 hn) in H2; auto.
    rewrite (@Heap.new_array_no_change h p tp length x loc hn); auto.
    eapply object_in0; eauto.
    intros; intro HH; inversion_mine HH; intuition.
    
    destruct (Location_dec loc0 loc); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationArray tp length x) loc hn); auto.
    elim left_heap_compat0 with loc.
    exists n; auto.
    eapply Heap.new_fresh_location; eauto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray tp length x) loc loc0 hn); auto.
    eauto.
    
    repeat intro.
    elim left_heap_compat0 with loc0; auto.
    destruct (Location_dec loc0 loc); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationArray tp length x) loc hn) in H1; auto; discriminate.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray tp length x) loc loc0 hn) in H1; auto.

    assert (loc<>loc0).
    intro; subst.
    elim left_heap_compat0 with loc0.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H0).
    rewrite (@Heap.new_array_no_change h p tp length x loc hn); auto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationArray tp length x) loc loc0 hn) in H2; auto.
    eauto.
    congruence.
  Qed.

  Lemma ffun_extends_hp_in_newarray_right: forall tp length x b b' h h' hn loc,
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h' p (Heap.LocationArray tp length x) = Some (pair loc hn) ->
    hp_in kobs newArT ft b b' h hn.
  Proof.
    intros.
    apply hp_in_sym.
    eapply ffun_extends_hp_in_newarray_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma ffun_extends_hp_in_newarray_simpl: forall tp length x tp' length' x' b b' h h' hn hn' loc loc',
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h p (Heap.LocationArray tp length x) = Some (pair loc hn) ->
    Heap.new h' p (Heap.LocationArray tp' length' x') = Some (pair loc' hn') ->
    hp_in kobs newArT ft b b' hn hn'.
  Proof.
    intros.
    eapply ffun_extends_hp_in_newarray_left; eauto.
    eapply ffun_extends_hp_in_newarray_right; eauto.
  Qed.


  Lemma ffun_extends_hp_in_new_left: forall c b b' h h' hn loc,
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc hn) ->
    hp_in kobs newArT ft b b' hn h'.
  Proof.
    intros.
    inversion_clear H; constructor; intros; try trivial.
    rewrite (@Heap.new_object_no_change h p c loc hn); auto.
    assert (Hclass:=class_object_in0 _ _ _ H H1).
    elim Compat_ex with h (Heap.DynamicField loc0 f); intros Hcomp.
    inversion_clear Hcomp. 
    generalize H5; rewrite Hclass; intros.
    apply object_in0 with n cn0 cn0; auto.
    rewrite (@Heap.get_uncompat h); auto.
    rewrite (@Heap.get_uncompat h').
    constructor.
    intros HH; inversion_clear HH.
    elim Hcomp; constructor 2 with cn0.
    rewrite Hclass; auto.
    intros fs Hi; injection Hi; intros; subst.
    elim left_heap_compat0 with loc.
    exists n; auto.
    apply Heap.new_fresh_location with (1:=H0).

    
    destruct (Location_dec loc0 loc); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationObject c) loc hn); auto.
    elim left_heap_compat0 with loc.
    exists n; auto.
    eapply Heap.new_fresh_location; eauto.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationObject c) loc loc0 hn); auto.
    eauto.
    
    repeat intro.
    elim left_heap_compat0 with loc0; auto.
    destruct (Location_dec loc0 loc); subst.
    rewrite (@Heap.new_typeof h p (Heap.LocationObject c) loc hn) in H1; auto; discriminate.
    rewrite (@Heap.new_typeof_old h p (Heap.LocationObject c) loc loc0 hn) in H1; auto.

    destruct (Location_dec loc loc0); subst.
    elim left_heap_compat0 with loc0; auto.
    exists n; auto.
    eapply Heap.new_fresh_location; eauto.
    rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H0 n0) in H2; auto.
    rewrite (@Heap.new_object_no_change h p c loc hn); eauto.
    intros; discriminate.
  Qed.

  Lemma ffun_extends_hp_in_new_right: forall c b b' h h' hn' loc,
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h' p (Heap.LocationObject c) = Some (pair loc hn') ->
    hp_in kobs newArT ft b b' h hn'.
  Proof.
    intros.
    apply hp_in_sym; eapply ffun_extends_hp_in_new_left; eauto.
    apply hp_in_sym; auto.
  Qed.

  Lemma ffun_extends_hp_in_simpl: forall c c' b b' h h' hn hn' loc loc',
    hp_in kobs newArT ft b b' h h' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc hn) ->
    Heap.new h' p (Heap.LocationObject c') = Some (pair loc' hn') ->
    hp_in kobs newArT ft b b' hn hn'.
  Proof.
    intros.
    eapply ffun_extends_hp_in_new_left; eauto.
    eapply ffun_extends_hp_in_new_right; eauto.
  Qed.

  Lemma hp_in_array_in_elem : forall h1 h2 loc1 loc2 length1 tp1 b1 b2 i ke,
    Heap.typeof h1 loc1 = Some (Heap.LocationArray length1 tp1 ke) ->
    (0 <= i < Int.toZ length1)%Z ->
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    Value_in b1 b2 (Ref loc1) (Ref loc2) ->
    L.leql (newArT ke) kobs ->
    Value_in_opt b1 b2 
    (Heap.get h1 (Heap.ArrayElement loc1 i))
    (Heap.get h2 (Heap.ArrayElement loc2 i)).
  Proof.
    intros.
    destruct H1.
    inversion_mine H2.
    eapply array_in_elem0; eauto.
  Qed.


  Lemma indist_same_class : forall h1 h2 loc1 loc2 b1 b2,
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    Value_in b1 b2 (Ref loc1) (Ref loc2) ->
    Heap.typeof h1 loc1 = Heap.typeof h2 loc2.
  Proof.
    intros.
    inversion_clear H0.
    apply (class_object_in _ _ _ _ _ _ _ H n) ;auto.
  Qed.

  Lemma leql'_opt_trans : forall k1 k2 k3,
    leql'_opt k1 k2 -> 
    leql'_opt k2 k3 -> 
    leql'_opt k1 k3.
  Proof.
    intros.
    inversion_clear H in H0; inversion_clear H0; constructor.
    apply ExL.leql_trans with k4; auto.
  Qed.

  Lemma os_in_nth_error : forall i s1 s2 st1 st2 b1 b2 v1 v2 k1 k2,
    os_in kobs b1 b2 s1 s2 st1 st2 ->
    nth_error st1 i = Some k1 ->
    nth_error s1 i = Some v1 ->
    nth_error st2 i = Some k2 ->
    nth_error s2 i = Some v2 ->
    L.leql k1 kobs ->
    L.leql k2 kobs ->
    Value_in b1 b2 v1 v2.
  Proof.
    induction i; simpl; intros.
    inversion_mine H.
    inversion_mine H6; try discriminate.
    injection H0; intros; subst; Contradiction.
    injection H0; intros; subst; Contradiction.
    injection H2; injection H3; injection H1; intros; subst; auto.
    destruct st1; try discriminate.
    destruct s1; try discriminate.
    destruct st2; try discriminate.
    destruct s2; try discriminate.
    apply IHi with s1 s2 st1 st2  k1 k2; auto.
    apply (os_in_tl H).
  Qed.
*)  
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
(*
  Lemma os_in_nth_error_opt : forall i s1 s2 st1 st2 b1 b2 k1 k2,
    os_in kobs b1 b2 s1 s2 st1 st2 ->
    nth_error st1 i = Some k1 ->
    nth_error st2 i = Some k2 ->
    L.leql k1 kobs ->
    L.leql k2 kobs ->
    Value_in_opt b1 b2 (nth_error s1 i) (nth_error s2 i).
  Proof.
    intros.
    elim os_in_length with (1:=H); intros.
    caseeq (nth_error s1 i); intros.
    caseeq (nth_error s2 i); intros.
    constructor; eapply os_in_nth_error; eauto.
    assert (T1:=nth_error_none_length _ _ _ H7).
    assert (T2:=nth_error_some_length _ _ _ _ H1).
    apply False_ind; omega.
    assert (T1:=nth_error_none_length _ _ _ H6).
    assert (T2:=nth_error_some_length _ _ _ _ H0).
    apply False_ind; omega.
  Qed.
  
  Definition beta_pre_order (b1 b2:FFun.t Location) : Prop :=
    forall loc n, b1 n = Some loc -> b2 n = Some loc.

  Lemma beta_pre_order_value_in: forall v v' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    Value_in b1 b1' v v'->
    Value_in b2 b2' v v'.
  Proof.
    intros.
    inversion_clear H1; try constructor.
    constructor 3 with n; auto.
  Qed.

  Lemma beta_pre_order_value_in_opt:  forall v v' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    Value_in_opt b1 b1' v v' ->
    Value_in_opt b2 b2' v v'.
  Proof.
    intros.
    inversion_clear H1; constructor.
    eapply beta_pre_order_value_in; eauto.
  Qed.

  Lemma beta_pre_order_localvar_in:  forall lvt l l' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    localvar_in kobs lvt b1 b1' l l' ->
    localvar_in kobs lvt b2 b2' l l'.
  Proof.
    intros; intro; intros.
    intros; eapply beta_pre_order_value_in_opt; eauto.
  Qed.

  Lemma beta_pre_order_os_in:  forall s s' st st' b1 b2 b1' b2',
    beta_pre_order b1 b2 ->
    beta_pre_order b1' b2' ->
    os_in kobs b1 b1' s s' st st' ->
    os_in kobs b2 b2' s s' st st' .
  Proof.
    induction 3.
    constructor 1; auto.
    constructor 2; auto.
    constructor 3; auto.
    eapply beta_pre_order_value_in; eauto.
  Qed.

  Lemma os_in_app1 : forall s1 s2 s1' s2' st1 st2 st1' st2' b b',
    length s1 = length st1 ->
    length s1' = length st1' ->
    length s1 = length s1' ->
    os_in kobs b b' (s1++s2) (s1'++s2') (st1++st2) (st1'++st2') ->
    os_in kobs b b' s2 s2' st2 st2'.
  Proof.
    induction s1; intros; 
      destruct st1; try discriminate;
        destruct s1'; try discriminate;
          destruct st1'; try discriminate.
    auto. 
    apply IHs1 with s1' st1 st1'; simpl in *; try omega.
    apply (os_in_tl H2).
  Qed.

  Lemma length_lift : forall l k,
    length (lift k l) = length l.
  Proof.
    induction l; simpl; intros; auto.
  Qed.


  Lemma lift_high_left: forall st k s,
    length s = length st ->
    ~ L.leql k kobs ->
    high_st kobs s (lift k st).
  Proof.
    intros st.
    elim st; intros.
    simpl in H.
    caseeq s.
    constructor.
    intros.
    subst.
    discriminate.
    simpl.
    caseeq s.
    intros; subst.
    discriminate.
    intros.
    constructor; auto.
    intro.
    apply H1.
    apply L.leql_trans with (L.head (L.join' k a)); auto.
    apply ExL.join_left.
    subst.
    apply H; auto.
  Qed.

  Lemma lift_high_left_os : forall st k s st' s' b b',
    os_in kobs b b' s s' st st' ->
    ~ L.leql k kobs ->
    high_st kobs s (lift k st).
  Proof.
    intros.
    elim os_in_length with (1:=H); intros.
    eapply lift_high_left; eauto.
  Qed.

  Lemma high_st_app : forall s1 s2 st1 st2,
    high_st kobs (s1++s2) (st1++st2) ->
    length s1 = length st1 ->
    high_st kobs s2 st2.
  Proof.
    induction s1; intros.
    destruct st1; try discriminate; auto.
    destruct st1; try discriminate.
    simpl in *; inversion_mine H.
    apply IHs1 with st1; auto.
  Qed.
  Implicit Arguments high_st_app.

  Lemma os_in_lift_high : forall os1 os2 st1 st2 b1 b2 k1 k2,
    length os1 = length st1 ->
    length os2 = length st2 ->
    ~ L.leql k1 kobs ->
    ~ L.leql k2 kobs ->
    os_in kobs b1 b2 os1 os2 (lift k1 st1) (lift k2 st2).
  Proof.
    intros.
    constructor 1.
    apply lift_high_left; auto.
    apply lift_high_left; auto.
  Qed.

  Lemma os_in_lift_high_os : forall os1 os2 st1 st2 b1 b2 k1 k2,
    os_in kobs b1 b2 os1 os2 st1 st2 ->
    ~ L.leql k1 kobs ->
    ~ L.leql k2 kobs ->
    os_in kobs b1 b2 os1 os2 (lift k1 st1) (lift k2 st2).
  Proof.
    intros.
    elim os_in_length with (1:= H); intros.
    apply os_in_lift_high; auto.
  Qed.

  Hint Resolve os_in_lift_high_os.

  Lemma os_in_use_hd : forall b1 b2 k1 k2 st1 st2 st3 st4 v1 v2 s1 s2 s3 s4,
    os_in kobs b1 b2 (v1::s1) (v2::s2) (k1::st1) (k2::st2) ->
    os_in kobs b1 b2 s3 s4 st3 st4 ->
    os_in kobs b1 b2 (v1::s3) (v2::s4) (k1::st3) (k2::st4).
  Proof.
    intros.
    elim os_in_cons_cases2 with (1:=H); 
      [intros (T1,(T2,T3)); inversion_mine T2|intros (T1,T2)].
    constructor 3; auto.
    constructor 2; auto.
  Qed.

  Lemma hp_in_getfield : forall b2 b2' v v0 h2 h2' loc loc0 cn cn0 f,
    Heap.typeof h2 loc = Some (Heap.LocationObject cn) ->
    Heap.get h2 (Heap.DynamicField loc f) = Some v ->
    Heap.typeof h2' loc0 = Some (Heap.LocationObject cn0) ->
    Heap.get h2' (Heap.DynamicField loc0 f) = Some v0 ->
    hp_in kobs newArT ft b2 b2' h2 h2' ->
    L.leql (ft f) kobs ->
    Value_in b2 b2' (Ref loc) (Ref loc0) ->
    Value_in b2 b2' v v0.
  Proof.
    intros.
    inversion_clear H5.
    assert (HH:=object_in _ _ _ _ _ _ _ H3 _ _ _ f cn cn0 H6 H7 H H1 H4).
    rewrite H0 in HH; rewrite H2 in HH.
    inversion_clear HH; auto.
  Qed.

  Lemma Value_in_assign_compatible : forall h1 h2 loc1 loc2 t b1 b2,
    Value_in b1 b2 (Ref loc1) (Ref loc2) ->
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    assign_compatible p h1 (Ref loc1) (ReferenceType t) ->
    assign_compatible p h2 (Ref loc2) (ReferenceType t).
  Proof.
    intros.
    generalize (indist_same_class _ _ _ _ _ _ H0 H); intros.
    inversion_mine H1.
    constructor 2 with cn; auto; congruence.
    constructor 3 with length tp a; auto; congruence.
  Qed.

  Lemma Value_in_assign_compatible' : forall h1 h2 v1 v2 t b1 b2,
    Value_in b1 b2 v1 v2 ->
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    assign_compatible p h1 v1 t ->
    assign_compatible p h2 v2 t.
  Proof.
    intros.
    destruct t.
    destruct v1; destruct v2; try (inversion_mine H; inversion_mine H1; fail).
    eapply Value_in_assign_compatible; eauto.
    constructor.
    inversion_mine H; inversion_mine H1; constructor; auto.
  Qed.

  Lemma Value_in_extends : forall b1 b2 loc1 loc2 h1 h2,
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    Heap.typeof h1 loc1 = None ->
    Heap.typeof h2 loc2 = None ->
    Value_in 
    (FFun.extends b1 loc1) (FFun.extends b2 loc2)
    (Ref loc1) (Ref loc2) .
  Proof.
    intros.
    destruct H.
    eapply Value_in_extends_object; eauto.
  Qed.

  Lemma Value_in_conv_for_stack : forall v1 v2 b1 b2,
    Value_in b1 b2 v1 v2 ->
    Value_in b1 b2 (conv_for_stack v1) (conv_for_stack v2).
  Proof.
    intros.
    inversion_clear H; simpl.
    constructor.
    destruct n; constructor.
    econstructor; eauto.
  Qed.

  Lemma hp_in_arrayload : forall h h' b b' loc loc' i i' length tp k v v',
    hp_in kobs newArT ft b b' h h' ->
    Value_in b b' (Ref loc) (Ref loc') ->
    Value_in b b' (Num (I i)) (Num (I i')) ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp k) ->
    (0 <= Int.toZ i < Int.toZ length)%Z ->
    L.leql (newArT k) kobs ->
    Heap.get h (Heap.ArrayElement loc (Int.toZ i)) = Some v ->
    Heap.get h' (Heap.ArrayElement loc' (Int.toZ  i')) = Some v' ->
    Value_in b b' v v'.
  Proof.
    intros.
    destruct H; inversion_mine H0; inversion_mine H1.
    generalize (array_in_elem0 _ _ _ _ _ _ _ H8 H9 H2 H3 H4).
    rewrite H6; rewrite H5; intros.
    inversion H; auto.
  Qed.

  Lemma Value_in_conv_for_array : forall b2 b2' val t val0,
    Value_in b2 b2' val val0 ->
    Value_in b2 b2' (conv_for_array val t) (conv_for_array val0 t).
  Proof.
    intros.
    inversion_clear H; simpl. 
    constructor.
    destruct n; destruct t; 
      try destruct pt; try constructor.
    econstructor; eauto.
  Qed.

  Lemma SemCompRef_Value_in : forall cmp v1 v2 v0 v3 b2 b2' h1 h2 ft,
    hp_in kobs newArT ft b2 b2' h1 h2 ->
    SemCompRef cmp v1 v2 ->
    Value_in b2 b2' v2 v0 ->
    Value_in b2 b2' v1 v3 ->
    SemCompRef cmp v3 v0.
  Proof.
    intros.
    assert (Il:=left_inj _ _ _ _ _ _ _ H).
    assert (Ir:=right_inj _ _ _ _ _ _ _ H).
    inversion_mine H0;
    inversion_mine H1; inversion_mine H2; econstructor; auto;
      try constructor; try discriminate.
    rewrite (FFun.inv_aux Location n n0 b2 b2' loc loc' loc loc'0); auto.
    intro HH; elim H5; inversion_mine HH.
    rewrite (FFun.inv_aux Location n n0 b2' b2 loc' loc loc' loc0); auto.
  Qed.

  Lemma hp_in_arraystore_high_update : forall loc loc' b b' h h' i i' v v' length length' tp tp' ke ke',
    hp_in kobs newArT ft b b' h h' ->
    ~ L.leql (newArT ke) kobs ->
    ~ L.leql (newArT ke') kobs ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp ke) ->
    Heap.typeof h' loc' = Some (Heap.LocationArray length' tp' ke') ->
    hp_in kobs newArT ft b b'
    (Heap.update h (Heap.ArrayElement loc i) v)
    (Heap.update h' (Heap.ArrayElement loc' i') v').
  Proof.
    intros.
    eapply hp_in_arraystore_high_update_left with (mpc:=ke); eauto.
    eapply hp_in_arraystore_high_update_right; eauto.
  Qed.
*)


  Hint Resolve 
    not_leql_join1 (*not_leql_join1'*) not_leql_join2 (*not_leql_join2'*) not_leql_trans 
    L.join_left L.join_right (*leql'_leql*)
    L.leql_trans : lattice.

(*
  Lemma localvar_in_stack2localvar : forall args args0 mid0 st4 st0 os os0 st3 st5 b1 b0 sgn2,
    os_in kobs b1 b0 (args0 ++ os) (args ++ os0) (st0 ++ st3) (st4 ++ st5) ->
    length args = length (METHODSIGNATURE.parameters mid0) ->
    length args0 = length (METHODSIGNATURE.parameters mid0) ->
    length st4 = length (METHODSIGNATURE.parameters mid0) ->
    compat_type_st_lvt sgn2 (st4 ++ st5) (length st4) ->
    length st0 = length (METHODSIGNATURE.parameters mid0) ->
    compat_type_st_lvt sgn2 (st0 ++ st3) (length st0) ->
    localvar_in kobs (lvt sgn2) b1 b0 (stack2localvar (args0 ++ os) (length args0))
    (stack2localvar (args ++ os0) (length args)).
  Proof.
    intros; intros x.
    destruct (le_lt_dec (length args0) (Var_toN x)).
    repeat (rewrite stack2locvar_prop1; auto).
    repeat constructor.
    replace (length args) with (length args0); auto; congruence.

    repeat (rewrite stack2locvar_prop2; auto).
    unfold OperandStack.get_nth.
    destruct (H3 x) as [k1 [U1 U2]]; auto.
    omega.
    destruct (H5 x) as [k2 [U3 U4]]; auto.
    omega.
    intros.
    replace (length args) with (length args0); intros.
    eapply os_in_nth_error_opt with (k1:=k2) (k2:=k1) (1:=H);
      eauto with lattice.
    congruence.
    congruence.
    congruence.
    omega.
  Qed.

  Lemma localvar_in_stack2localvar_S : forall args args0 mid0 st4 st0 os os0 st3 st5 b1 b0 sgn2 v1 v2 k1 k2,
    os_in kobs b1 b0 (args0 ++ v1 :: os) (args ++ v2 :: os0) (st0 ++ k2 :: st3) (st4 ++ k1 :: st5) ->
    length args = length (METHODSIGNATURE.parameters mid0) ->
    length args0 = length (METHODSIGNATURE.parameters mid0) ->
    length st4 = length (METHODSIGNATURE.parameters mid0) ->
    compat_type_st_lvt sgn2 (st4 ++ k1 :: st5) (1+(length st4)) ->
    length st0 = length (METHODSIGNATURE.parameters mid0) ->
    compat_type_st_lvt sgn2 (st0 ++ k2 :: st3) (1+(length st0)) ->
    localvar_in kobs (lvt sgn2) b1 b0 (stack2localvar (args0 ++ v1:: os) (S (length args0)))
    (stack2localvar (args ++ v2:: os0) (S (length args))).
  Proof.
    intros.
    rewrite (app_cons value args0).
    rewrite (app_cons value args).
    intros x.
    destruct (le_lt_dec (S (length args0)) (Var_toN x)).
    repeat (rewrite stack2locvar_prop1; auto).
    repeat constructor.
    omega.
    repeat (rewrite stack2locvar_prop2; auto).
    unfold OperandStack.get_nth.
    destruct (H3 x) as [k3 [U1 U2]]; auto.
    omega.
    destruct (H5 x) as [k4 [U3 U4]]; auto.
    omega.
    replace (length args) with (length args0).
    repeat rewrite <- app_cons.
    intros.
    simpl plus in *. 
    eapply os_in_nth_error_opt with (k1:=k4) (k2:=k3) (1:=H); congruence || eauto with lattice.
    congruence.
    omega.
  Qed.

  Lemma hp_in_side_effect_trans : forall k h1 h1' b1 h b,
    ~ L.leql k kobs ->
    side_effect newArT ft k h1 h1' ->
    hp_in kobs newArT ft b b1 h h1 ->
    hp_in kobs newArT ft b b1 h h1'.
  Proof.
    intros.
    destruct H1; constructor; intros; auto.
    assert (Heap.typeof h1 loc' = Some (Heap.LocationObject cn')).
    rewrite (side_effect_typeof H0); auto.
    apply right_heap_compat0.
    exists n; auto.
    rewrite <- (@side_effect_low_field _ _ _  _ _ H0 f loc' cn'); auto.
    eapply object_in0; eauto.
    eauto with lattice.
    rewrite <- (side_effect_typeof H0); eauto.
    apply right_heap_compat0.
    exists n; auto.
    repeat intro.
    apply (right_heap_compat0 loc); auto.
    apply (side_effect_domain H0); auto.
    assert (Heap.typeof h1 loc' = Some (Heap.LocationArray length tp mpc)).
    rewrite <- (class_object_in0 _ _ _ H1 H2); auto.
    rewrite <- (@side_effect_low_index _ _ _  _ _ H0 i mpc loc' tp length); auto.
    eapply array_in_elem0; eauto.
    eauto with lattice.
  Qed.

  Lemma hp_in_side_effect_trans2 : forall k h1 h1' h2 h2' b1 b2,
    ~ L.leql k kobs -> 
    side_effect newArT ft k h1 h1' ->
    side_effect newArT ft k h2 h2' ->
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    hp_in kobs newArT ft b1 b2 h1' h2'.
  Proof.
    intros.
    apply hp_in_trans with h1 b1.
    apply hp_in_trans with h2 b2.
    apply hp_in_sym.
    apply hp_in_side_effect_trans with (2:=H0); auto.
    apply hp_in_sym; auto.
    apply hp_in_sym; auto.
    apply hp_in_side_effect_trans with (2:=H1); auto.
  Qed.

  Lemma hp_in_side_effect_trans3 : forall k k' h1 h1' h2 h2' b1 b2,
    ~ L.leql k kobs -> 
    ~ L.leql k' kobs -> 
    side_effect newArT ft k h1 h1' ->
    side_effect newArT ft k' h2 h2' ->
    hp_in kobs newArT ft b1 b2 h1 h2 ->
    hp_in kobs newArT ft b1 b2 h1' h2'.
  Proof.
    intros.
    apply hp_in_trans with h1 b1.
    apply hp_in_trans with h2 b2.
    apply hp_in_sym.
    apply hp_in_side_effect_trans with (2:=H1); auto.
    apply hp_in_sym; auto.
    apply hp_in_sym; auto.
    apply hp_in_side_effect_trans with (2:=H2); auto.
  Qed.

  Lemma hp_in_side_effect_trans_left : forall k h h1 h2 b b1,
    ~ L.leql k kobs -> 
    side_effect newArT ft k h1 h2->
    hp_in kobs newArT ft b1 b h1 h ->
    hp_in kobs newArT ft b1 b h2 h.
  Proof.
    intros; apply hp_in_sym.
    apply hp_in_side_effect_trans with k h1; eauto.
    apply hp_in_sym; auto.
  Qed.
*)
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