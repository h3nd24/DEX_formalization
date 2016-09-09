Require Export DEX_BigStepWithTypes.

Import DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.

Section p.
  Variable p : DEX_ExtendedProgram.

    Inductive compat_value (*h:Heap.t*) : DEX_value -> L.t -> Prop :=
(*       compat_value_array : forall loc k mpc length tp,
        Heap.typeof h loc = Some (Heap.LocationArray length tp mpc) ->
        compat_value h (Ref loc) (L.Array k (newArT p mpc))
    | compat_value_object : forall loc k c,
      Heap.typeof h loc = Some (Heap.LocationObject c) ->
      compat_value h (Ref loc) k *)
    | compat_value_num : forall n k,
      compat_value (* h *) (Num n) k
(*     | compat_value_null : forall k,
      compat_value h Null k *).

     Definition compat_registers (*h:Heap.t*) (regs:DEX_Registers.t) (rt:TypeRegisters) : Prop :=
      forall x v k, DEX_Registers.get regs x = Some v -> 
        BinNatMap.get _ rt x = Some k ->
        compat_value (* h *) v k. 

(*     Definition compat_localvar (*h:Heap.t*) (l:LocalVar.t) (lvt:Var->L.t') : Prop :=
      forall x v, LocalVar.get l x = Some v -> compat_value h v (lvt x). *)

(*     Definition compat_heap (h:Heap.t) (ft:FieldSignature -> L.t') : Prop :=
      (forall loc cn f v,
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        Heap.get h (Heap.DynamicField loc f) = Some v -> compat_value h v (ft f))
      /\
      (forall loc v length tp mpc i,
        Heap.typeof h loc = Some (Heap.LocationArray length tp mpc) ->
        Heap.get h (Heap.ArrayElement loc i) = Some v -> compat_value h v (newArT p mpc)). *)

(*     Definition typeof_stable (h1 h2:Heap.t) : Prop :=
      forall loc,
        Heap.typeof h1 loc <> None ->
        Heap.typeof h1 loc = Heap.typeof h2 loc.

    Definition exec_typeof_rel (s:IntraNormalState) (r:ReturnState) : Prop :=
      match s with (pc,(h,os,l)) =>
        typeof_stable h (fst r)
      end.     *)

    Definition compat_state (sgn:DEX_sign) (s:DEX_IntraNormalState) (rt:TypeRegisters) : Prop :=
      match s with (pc, regs) =>
(*         compat_heap h (ft p) /\ *)
(*         compat_localvar h l sgn.(lvt) /\ *)
        compat_registers regs rt 
      end.
    
    Inductive compat_res (sgn:DEX_sign) : DEX_ReturnState -> Prop :=
    | compat_res_val : forall (* h *) v k,
      sgn.(DEX_resType) = Some k ->
      compat_value (* h *) v k ->
(*       compat_heap h (ft p) -> *)
      compat_res sgn ((* h, *)Normal (Some v))
    | compat_res_void : (* forall h, *)
      sgn.(DEX_resType) = None ->
(*       compat_heap h (ft p) -> *)
      compat_res sgn ((* h, *)Normal None)
(*    | compat_res_exception : forall h loc,
      compat_heap h (ft p) ->
      compat_res sgn (h,Exception loc) *).


(* Ltac inv_compat H :=
destruct H as [(* Hcompat_h [Hcompat_l *) Hcompat_regs(* ] *)]; simpl in Hcompat_regs;
(* elim Hcompat_h; intros Hcompat_h1 Hcompat_h2; *)
repeat match goal with
(*          [ id : compat_value _ (Ref _) _ /\ _  |-_ ] => 
         let h := fresh in (
           destruct id as [h id];
           inversion_mine h; DiscrimateEq) 
       |*) [ id : compat_value _ _ _ /\ _  |-_ ] => 
         let h := fresh in destruct id as [h id]
       end.
Hint Constructors compat_value. *)

Lemma compat_value_join(* ' *) : forall (* h *) a t k,
  compat_value (* h *) a t ->
  compat_value (* h *) a (L.join(* ' *) k t).
Proof.
  intros.
  inversion_clear H. constructor.
Qed.
Hint Resolve compat_value_join(* ' *).

(* Lemma compat_operandstack_lift : forall h s k st,
  compat_operandstack h s st ->
  compat_operandstack h s (lift k st).
Proof.
  induction s; destruct st; simpl; intros; auto.
  split; intuition.
Qed.
Hint Resolve compat_operandstack_lift.
Hint Unfold compat_localvar. *)

(* Lemma compat_operandstack_elift : forall m pc h s k st,
  compat_operandstack h s st ->
  compat_operandstack h s (elift m pc k st).
Proof.
  unfold elift; intros.
  destruct (throwableAt m pc); simpl; auto.
Qed.
Hint Resolve compat_operandstack_elift. *)

(* Lemma compat_value_new_allocation : forall p lt loc h h' ke v,
  Heap.new h p lt = Some (loc, h') ->
  compat_value h v ke ->
  compat_value h' v ke.
Proof.
  intros.
  inversion_mine H0; auto.
  destruct (eq_excluded_middle _ loc loc0); subst.
  rewrite (@Heap.new_fresh_location _ _ _ _ _ H) in H1; discriminate.
  rewrite <- (@Heap.new_typeof_old _ _ _ _ _ _ H H0) in H1.
  eauto.
  destruct (eq_excluded_middle _ loc loc0); subst.
  rewrite (@Heap.new_fresh_location _ _ _ _ _ H) in H1; discriminate.
  rewrite <- (@Heap.new_typeof_old _ _ _ _ _ _ H H0) in H1.
  eauto.
Qed.
Hint Resolve compat_value_new_allocation. *)

(* Lemma compat_heap_new_object : forall ft lt loc h h',
  Heap.new h p.(prog) lt = Some (loc, h') ->
  compat_heap h ft ->
  compat_heap h' ft.
Proof.
  intros.
  destruct lt.
  destruct H0.
  split; intros.
  destruct (eq_excluded_middle _ loc loc0); subst.
  destruct (excluded_middle (defined_field p.(prog) c f)).
  destruct H4.
  rewrite (@Heap.new_defined_object_field _ _ _ _ _ _ _ H H4) in H3; inversion_mine H3.
  unfold init_field_value.
  destruct (FIELD.initValue x); auto.
  destruct (FIELDSIGNATURE.type (FIELD.signature x)); simpl; auto.
  rewrite (@Heap.new_undefined_object_field _ _ _ _ _ _ H H4) in H3; inversion_mine H3.
  rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H H4) in H2.
  rewrite (@Heap.new_object_no_change _ _ _ _ _ (Heap.DynamicField loc0 f) H) in H3.
  eauto.
  red; intros; elim H4.
  inversion_mine H5; auto.
  destruct (eq_excluded_middle _ loc loc0); subst.
  rewrite (@Heap.new_typeof _ _ _ _ _ H) in H2; discriminate.
  rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H H4) in H2.
  rewrite (@Heap.new_object_no_change _ _ _ _ _ (Heap.ArrayElement loc0 i) H) in H3.
  eauto.
  red; intros; elim H4.
  inversion_mine H5; auto.
  destruct H0 as [H0 H00].
  split; intros.
  destruct (eq_excluded_middle _ loc loc0); subst.
  rewrite (@Heap.new_typeof _ _ _ _ _ H) in H1; discriminate.
  rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H H3) in H1.
  rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.DynamicField loc0 f) H) in H2.
  eauto.
  red; intros; elim H3.
  inversion_mine H4; auto.
  destruct (eq_excluded_middle _ loc loc0); subst.
  destruct (excluded_middle (0 <= i < Int.toZ t)%Z).
  rewrite (@Heap.new_valid_array_index _ _ _ _ _ _ _ _ H H3) in H2; inversion_mine H2.
  unfold init_value.
  destruct t0; auto.
  rewrite (@Heap.new_unvalid_array_index _ _ _ _ _ _ _ _ H H3) in H2; discriminate.
  rewrite (@Heap.new_typeof_old _ _ _ _ _ _ H H3) in H1.
  rewrite (@Heap.new_array_no_change _ _ _ _ _ _ _ (Heap.ArrayElement loc0 i) H) in H2.
  eauto.
  red; intros; elim H3.
  inversion_mine H4; auto.
Qed.
Hint Resolve compat_heap_new_object.

Opaque Heap.update. *)

(* Lemma compat_operandstack_new_allocation : forall p lt h h' os st loc,
  Heap.new h p lt = Some (loc, h') ->
  compat_operandstack h os st ->
  compat_operandstack h' os st.
Proof.
  induction os; destruct st; simpl; intuition eauto.
Qed. *)

(* Lemma compat_localvar_new_allocation : forall p lt h h' l lvt loc,
  Heap.new h p lt = Some (loc, h') ->
  compat_localvar h l lvt ->
  compat_localvar h' l lvt.
Proof.
  eauto.
Qed. *)

(* Hint Resolve compat_localvar_new_allocation compat_operandstack_new_allocation. *)

(* Lemma compat_value_heap_update : forall h am v k v0,
  compat_value h v k ->
  compat_value (Heap.update h am v0) v k.
Proof.
  intros.
  inversion_mine H; auto.
  constructor 1 with length tp.
  rewrite Heap.typeof_update_same; auto.
  constructor 2 with c.
  rewrite Heap.typeof_update_same; auto.
Qed.
Hint Resolve compat_value_heap_update.

Lemma compat_localvar_heap_update : forall h am l lvt v,
  compat_localvar h l lvt ->
  compat_localvar (Heap.update h am v) l lvt.
Proof.
  eauto.
Qed.

Lemma compat_operandstack_heap_update : forall h am os st v,
  compat_operandstack h os st ->
  compat_operandstack (Heap.update h am v) os st.
Proof.
  induction os; destruct st; simpl; intuition eauto.
Qed.
Hint Resolve compat_operandstack_heap_update compat_localvar_heap_update. *)

Lemma compat_value_leql(* ' *) : forall (* h *) v k1 k2,
  compat_value (* h *) v k1 -> L.leql(* ' *) k1 k2 ->
  compat_value (* h *) v k2.
Proof.
  intros.
  inversion_mine H0; inversion_mine H; econstructor.
Qed.


(* Lemma compat_heap_update_object : forall h ft loc f v k,
  compat_heap h ft ->
  compat_value h v k -> L.leql' k (ft f) ->
  compat_heap (Heap.update h (Heap.DynamicField loc f) v) ft.
Proof.
  intros.
  destruct H; split; intros.
  apply compat_value_heap_update.
  rewrite Heap.typeof_update_same in H3.
  destruct (eq_excluded_middle _ loc loc0); subst.
  destruct (eq_excluded_middle _ f f0); subst.
  rewrite Heap.get_update_same in H4.
  inversion_mine H4.
  eapply compat_value_leql'; eauto.
  eapply Heap.CompatObject; eauto.
  rewrite Heap.get_update_old in H4.
  eauto.
  intros T; elim H5; inversion_mine T; auto.
  rewrite Heap.get_update_old in H4.
  eauto.
  intros T; elim H5; inversion_mine T; auto.
  rewrite Heap.typeof_update_same in H3.
  rewrite Heap.get_update_old in H4.
  apply compat_value_heap_update; eauto.
  discriminate.
Qed.

Hint Resolve compat_heap_update_object.

Lemma compat_heap_update_array : forall h ft loc i v kv mpc length tp,
  compat_heap h ft ->
  Heap.typeof h loc = Some (Heap.LocationArray length tp mpc) ->
  compat_value h v kv -> 
  L.leql' kv (newArT p mpc) ->
  (0 <= i < Int.toZ length)%Z ->
  compat_heap (Heap.update h (Heap.ArrayElement loc i) v) ft.
Proof.
  intros.
  destruct H; split; intros.
  apply compat_value_heap_update.
  rewrite Heap.typeof_update_same in H5.
  rewrite Heap.get_update_old in H6.
  eauto.
  discriminate.
  rewrite Heap.typeof_update_same in H5.
  destruct (eq_excluded_middle _ loc loc0); subst.
  destruct (eq_excluded_middle _ i i0); subst.
  rewrite Heap.get_update_same in H6.
  inversion_mine H6.
  apply compat_value_heap_update.
  DiscrimateEq.
  eapply compat_value_leql'; eauto.
  eapply Heap.CompatArray; eauto.
  rewrite Heap.get_update_old in H6.
  eauto.
  intros T; elim H7; inversion_mine T; auto.
  rewrite Heap.get_update_old in H6.
  eauto.
  intros T; elim H7; inversion_mine T; auto.
Qed.

Hint Resolve compat_heap_update_array. *)

(* Lemma compat_localvar_update : forall l lvt x v h k,
  compat_value h v k ->
  L.leql' k (lvt x) ->
  compat_localvar h l lvt ->
  compat_localvar h (LocalVar.update l x v) lvt.
Proof.
  intros.
  intros y vy Hy.
  elim (eq_excluded_middle _ x y); intro; subst.
  rewrite LocalVar.get_update_new in Hy; inversion_mine Hy; auto.
  eapply compat_value_leql'; eauto.
  rewrite LocalVar.get_update_old in Hy; auto.
Qed. *)

Lemma compat_registers_n : forall regs rt i k v,
  compat_registers regs rt ->
  BinNatMap.get _ rt i = Some k ->
  DEX_Registers.get regs i = Some v ->
  compat_value v k.
Proof.
  intros. destruct v; econstructor 1.
Qed.

Lemma compat_intra : forall (* kobs *) sgn m region se (* tau *) s1 s2 rt1 rt2 (* h *) i,
  DEX_BigStepWithTypes.exec_intra (* kobs *) (* p *) se region m sgn i (* tau *) s1 rt1 (* b1 *) s2 rt2 (* b2 *) ->
  compat_state sgn s1 rt1 -> 
  compat_state sgn s2 rt2.
Proof.
  intros.
  inversion_mine H.
  destruct i; inversion_mine H1; simpl in H0; simpl; auto; unfold compat_registers;
    intros x' v' k'; try (destruct v'; constructor).
Qed.  

Hint Constructors compat_res.
Hint Resolve compat_value_leql(* ' *).  

Lemma compat_return : forall (* kobs *) sgn m region se (* tau *) s1 r2 rt1 (* b1 b2  *)i,
  DEX_BigStepWithTypes.exec_return (* kobs p *) se region m sgn i (* tau *) s1 rt1 (* b1  *) r2 (* b2 *) ->
  compat_state sgn s1 rt1 -> 
  compat_res sgn r2.
Proof.
  intros.
  inversion_mine H.
  destruct i; inversion_mine H1.
  constructor 2; auto.
  constructor 1 with (k:=kr). symmetry; auto.
  destruct val; constructor.
Qed.  

(* Lemma compat_nth_error : forall h os1 st1 i k1 v1,
  compat_operandstack h os1 st1 ->
  nth_error st1 i = Some k1 ->
  nth_error os1 i = Some v1 ->
  compat_value h v1 k1.
Proof.
  induction os1; destruct st1; simpl in *; intros; intuition.
  destruct i; simpl in H1; try discriminate.
  destruct i; simpl in H0, H1.
  inversion_mine H0; inversion_mine H1; auto.
  eauto.
Qed. *)

(* Lemma compat_stack2localvar : forall sgn h os1 os2 st1 st2,
  length st1 = length os1 ->
  compat_type_st_lvt sgn (st1++st2) (length st1) ->
  compat_operandstack h (os1++os2) (st1++st2) ->
  compat_localvar h (stack2localvar (os1 ++ os2) (length os1)) (lvt sgn).
Proof.
  repeat intro.
  destruct (le_lt_dec (length os1) (Var_toN x)).
  rewrite stack2locvar_prop1 in H2; auto.
  discriminate.
  rewrite stack2locvar_prop2 in H2; auto.
  destruct (H0 x) as [k [T1 T2]].
  rewrite H; auto.
  apply compat_value_leql' with k; auto.
  apply compat_nth_error with (os1++os2) (st1++st2) (length os1 - Var_toN x - 1)%nat; auto.
  rewrite <- H; auto.
Qed. *)

(* Lemma length_app : forall (A:Set) (l1 l2:list A),
  length (l1++l2) = (length l1 + length l2)%nat.
Proof.
  induction l1; simpl; intros; auto.
Qed.

Lemma length_app_cons : forall (A:Set) (l:list A) (a:A),
  length (l++a::nil) = S (length l).
Proof.
  induction l; simpl; auto.
Qed. *)

(* Lemma compat_call_init : forall kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0  b2 tau ret,
  BigStepWithTypes.exec_call kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0 ret b2 tau ->
  compat_state sgn s1 st1 ->
  compat_state sgn2 s0 st0.
Proof.
  intros.
  inversion_mine H; inversion_mine H1; simpl in H0; inv_compat H0;
    (split; [idtac|split]); simpl; auto.
  eapply compat_stack2localvar; eauto.
  congruence.
  replace (args++Ref loc::os) with ((args++(Ref loc::nil))++os).
  replace (S (length args)) with (length (args++(Ref loc::nil))).
  apply compat_stack2localvar with (st0++(L.Simple k::nil)) st'; auto.
  repeat rewrite length_app_cons; simpl; congruence.
  rewrite length_app_cons.
  rewrite app_ass; simpl.
  auto.
  repeat rewrite app_ass; simpl; auto.
  rewrite length_app_cons; congruence.
  repeat rewrite app_ass; simpl; auto.
  eapply compat_stack2localvar; eauto.
  congruence.
  replace (args++Ref loc0::os) with ((args++(Ref loc0::nil))++os).
  replace (S (length args)) with (length (args++(Ref loc0::nil))).
  apply compat_stack2localvar with (st0++(L.Simple k::nil)) st'; auto.
  repeat rewrite length_app_cons; simpl; congruence.
  rewrite length_app_cons.
  rewrite app_ass; simpl.
  auto.
  repeat rewrite app_ass; simpl; auto.
  rewrite length_app_cons; congruence.
  repeat rewrite app_ass; simpl; auto.
  eapply compat_stack2localvar; eauto.
  congruence.
  replace (args++Ref loc0::os) with ((args++(Ref loc0::nil))++os).
  replace (S (length args)) with (length (args++(Ref loc0::nil))).
  apply compat_stack2localvar with (st0++(L.Simple k::nil)) st'; auto.
  repeat rewrite length_app_cons; simpl; congruence.
  rewrite length_app_cons.
  rewrite app_ass; simpl.
  auto.
  repeat rewrite app_ass; simpl; auto.
  rewrite length_app_cons; congruence.
  repeat rewrite app_ass; simpl; auto.
Qed.

Lemma typeof_stable_value : forall h1 h2 v k,
  typeof_stable h1 h2 ->
  compat_value h1 v k ->
  compat_value h2 v k.
Proof.
  intros.
  inversion_mine H0; auto;
  rewrite (H loc) in H1; eauto;
    congruence.
Qed.

Lemma typeof_stable_localvar : forall h1 h2 l lvt,
  typeof_stable h1 h2 ->
  compat_localvar h1 l lvt ->
  compat_localvar h2 l lvt.
Proof.
  intros.
  intros x v H1.
  apply typeof_stable_value with h1; auto.
Qed.

Hint Resolve typeof_stable_localvar.

Lemma typeof_stable_operandstack : forall h1 h2 os st,
  typeof_stable h1 h2 ->
  compat_operandstack h1 os st ->
  compat_operandstack h2 os st.
Proof.
  induction os; destruct st; simpl; intuition.
  apply typeof_stable_value with h1; auto.
Qed.

Hint Resolve typeof_stable_operandstack. *)

(* Lemma compat_operandstack_app : forall h os1 os2 st1 st2,
  compat_operandstack h (os1++os2) (st1++st2) ->
  length os1 = length st1 ->
  compat_operandstack h os2 st2.
Proof.
  induction os1; destruct st1; simpl; intuition eauto.
  discriminate.
  discriminate.  
Qed.

Lemma compat_call : forall kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0 s2 st2 b2 tau,
  BigStepWithTypes.exec_call kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0 (inl _ (s2,st2)) b2 tau ->
  compat_state sgn s1 st1 ->
  compat_res sgn2 r ->
  exec_typeof_rel s0 r ->
  compat_state sgn s2 st2.
Proof.
  intros.
  inversion_mine H; inversion_mine H5; simpl in H0; inv_compat H0; inversion_mine H1;
    simpl in H2;
    (split; [idtac|split]); simpl; eauto.
  rewrite H3; apply compat_operandstack_lift; simpl; split; auto.
  apply typeof_stable_operandstack with h1; auto.
  apply compat_operandstack_app with (1:=Hcompat_os).
  congruence.
  rewrite H3; apply compat_operandstack_lift; simpl.
  apply typeof_stable_operandstack with h1; auto.
  apply compat_operandstack_app with (1:=Hcompat_os).
  congruence.
  rewrite H3; repeat apply compat_operandstack_lift; simpl; split; auto.
  apply typeof_stable_operandstack with h1; auto.
  destruct (compat_operandstack_app _ _ _ _ _ Hcompat_os); auto.
  congruence.
  rewrite H3; repeat apply compat_operandstack_lift; simpl; auto.
  apply typeof_stable_operandstack with h1; auto.
  destruct (compat_operandstack_app _ _ _ _ _ Hcompat_os); auto.
  congruence.
Qed.


Lemma compat_call_ret : forall kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0 r2 b2 tau,
  BigStepWithTypes.exec_call kobs se reg prog m sgn i s1 st1 b1 r br m2 sgn2 s0 st0 b0 (inr _ r2) b2 tau ->
  compat_state sgn s1 st1 ->
  compat_res sgn2 r ->
  exec_typeof_rel s0 r ->
  compat_res sgn r2.
Proof.
  intros.
  inversion_mine H; inversion_mine H5; simpl in H0; inv_compat H0; inversion_mine H1;
    simpl in H2.
  constructor.
  auto.
Qed. *)

End p.