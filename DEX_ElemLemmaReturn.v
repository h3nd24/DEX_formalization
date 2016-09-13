Require Export DEX_ElemLemmas.
(* Require Export ElemLemmaException1. *)
(* Require Export ElemLemmaException2. *)
(* Require Export ElemLemmaException4. *)

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(* Step Consistent *)
Lemma indist1_return_normal : 
 forall kobs p se m sgn pc i r1 rt1 ov2,

   ~ L.leql (se pc) kobs ->
(*    high_st kobs s1 st1 -> *)
   ReturnStep p se m sgn i (pc,r1) rt1 (ov2) ->

  (forall kr, sgn.(DEX_resType) = Some kr -> ~ L.leql kr kobs)
  (* /\ h1=h2 *).
Proof.
  intros.
  inversion H0. rewrite H9 in H1; inversion H1. 
  (* rewrite -> H8 in H1. inversion H1.
  subst. rewrite -> H10 in H1.*) 
(*   inversion H1; subst; auto.  *)
  apply not_leql_trans with (k1:=(se pc)); auto.
  apply leql_join_each in H16; inversion H16; auto.
  rewrite H13 in H1; inversion H1.
  rewrite <- H20; auto.
Qed.

(* Locally Respect *)
Lemma indist2_intra_normal : 
 forall kobs p se m sgn pc i r1 rt1 r1' rt1' ov2 ov2',

   ReturnStep p se m sgn i (pc,r1) rt1 (ov2) ->
   ReturnStep p se m sgn i (pc,r1') rt1' (ov2') ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

(*    hp_in kobs (newArT p) (ft p) b b' h2 h2' /\ *)
   indist_return_value kobs sgn ov2 ov2'.
Proof.
  intros.
  apply inv_st_in in H1.
  inversion H1.
  inversion H; inversion H0; DiscrimateEq; auto. 
  constructor; auto.
(*   inversion H22; subst. *)
  apply H3 with (k':=k2) (v':=val0) (v:=val) (k:=k1) in H23 ; auto.
  constructor 1 with kr0; inversion H6; auto. 
  intros.
  inversion H23; auto.
  apply not_leql_join1 with (k2:=(se pc)) in H16.
  apply L.leql_trans with (l1:=L.join k2 (se pc)) (l3:=kobs) in H4; auto.
  contradiction.
Qed.

(* Implicit Arguments indist2_exception. *)
(* collorary of locally respect? *)
Lemma indist2_return : 
 forall kobs se reg m sgn pc i r1 rt1 r1' rt1' v2 v2' (* kd *) (* kd' *),

   exec_return se reg m sgn i (* kd *) (pc,r1) rt1 (v2) ->
   exec_return se reg m sgn i (* kd' *) (pc,r1') rt1' (v2') ->

   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

(*    hp_in kobs (newArT p) (ft p) b2 b2' h2 h2' /\ *)
   indist_return_value kobs sgn v2 v2'.
Proof.
  intros.
  inversion_mine H; inversion_mine H0.
  eapply indist2_intra_normal; eauto.
  (* inversion_clear H9 in H11; inversion_clear H11; simpl in *; intuition.
  inversion_clear H8 in H11; inversion_clear H11; simpl in *; intuition.
  assert (HH:=indist2_exception pc pc H11 H10 H1).
  destruct (inv_st_in HH) as [Hin [Lin Sin]]; clear HH.
  split; auto.
  case_os_in Sin.
  assert (Heap.typeof h2 loc2 = Heap.typeof h2' loc0).
  eapply indist_same_class; eauto. 
  assert (Ht1:=ExceptionStep_typeof H11).
  assert (Ht2:=ExceptionStep_typeof H10).
  assert (e0=e); [congruence|subst].
  destruct (L.leql_dec (resExceptionType sgn e) kobs).
  constructor 3 with e; auto.
  constructor 6 with e e; auto.
  constructor 6 with e e0; auto.
  eapply ExceptionStep_typeof; eauto.
  eapply ExceptionStep_typeof; eauto.
  eauto with lattice.
  eauto with lattice. *)
Qed.
(*
Implicit Arguments os_in_sym.
Implicit Arguments indist1_exception.

(* exception *)
Lemma high_st_exception : 
 forall kobs p m sgn pc i h2' e' k1'
                   h1' loc2' s1' l1' st1' b1' b2',

   high_st kobs s1' st1' ->
   ExceptionStep kobs p m sgn i (pc,(h1',s1',l1')) st1' b1' (h2',loc2') k1' b2' e' ->
   ~ L.leql k1' kobs.
Proof.
  intros.
  inversion_mine H0.
  inversion_mine H; auto.
  destruct i;
  inversion_mine H13;
  try (match goal with
    [ id : high_st _ (_++?s) (_++?st) |- _ ] =>
    assert (hi:high_st kobs s st); [apply (@high_st_app _ _ _ _ _ id); congruence|idtac]
  end);
  repeat match goal with
      [ id : high_st _ (_::_) (_::_) |- _ ] => inversion_mine id
  end; 
  eauto with lattice.
Qed.
*)

(* it doesn't make sense to state that intra state is indistinguishable from return state *)
(* (* from step consistent *)
Lemma indist1_return : 
 forall kobs p se reg m sgn pc i r1 rt1 r1' rt1' v2' kd' pc1,

   ~ L.leql (se pc) kobs ->
(*    high_st kobs s1' st1' -> *)
   exec_return kobs p se reg m sgn i kd' (pc,r1') rt1' v2'->

   st_in kobs rt1 rt1' (pc1,r1) (pc,r1') ->

(*    hp_in kobs (newArT p) (ft p) b1 b2' h1 h2' /\ *)
   indist_intra_return kobs p sgn (pc1,r1) rt1 v2'.
Proof.
  intros.
  inversion_mine H1.
  elim indist1_return_normal with (1:=H)(3:=H10); auto.
  intros T1 T2; subst.
  destruct (inv_st_in H2) as [Hin [Lin Sin]]; clear H2.
  split; auto.
  constructor; auto.
  inversion_mine H10.
  constructor 1; auto.
  constructor 2 with kr; auto.
  apply os_in_high_high with (1:=os_in_sym Sin); auto.
  assert (HH:=indist1_exception pc H0 H12 H2); inversion_mine HH.
  destruct (inv_st_in H2) as [Hin [Lin Sin]]; clear H2.
  split; auto.
  constructor; auto.
  constructor 3 with e.
  eapply ExceptionStep_typeof; eauto.
  assert (~ L.leql k kobs).
  eapply high_st_exception; eauto.
  eauto with lattice.
  apply os_in_high_high with (1:=os_in_sym Sin); auto.
Qed.

(* from step consistent *)
Lemma indist1_return_return : 
 forall kobs p se reg m sgn pc i h1 h2'  b1 v1
                   h1' s1' l1' st1' b1' b2' v2' kd',

   ~ L.leql (se pc) kobs ->
   high_st kobs s1' st1' ->
   exec_return kobs p se reg m sgn i kd' (pc,(h1',s1',l1')) st1' b1' (h2',v2') b2' ->

   indist_intra_return kobs  p sgn (pc,(h1',s1',l1')) st1' b1' h1 v1 b1 ->

   hp_in kobs (newArT p) (ft p) b1 b2' h1 h2' /\
   indist_return_value kobs sgn h1 h2' v1 v2' b1 b2'.
Proof.
  intros.
  inversion_mine H1.
  elim indist1_return_normal with (1:=H)(3:=H10); auto.
  intros T1 T2; subst.
  inversion_mine H2.
  inversion_mine H10.
  inversion_mine H13; DiscrimateEq; 
  (split; [apply hp_in_sym; auto|try constructor; auto]).
  constructor 4 with cn; auto.
  inversion_mine H13; DiscrimateEq; 
  (split; [apply hp_in_sym; auto|try constructor; auto]).
  constructor 1 with k0; intuition.
  constructor 4 with cn; auto.
  split.
  eapply opstack1_exception_heap; eauto.
  inversion_mine H2; apply hp_in_sym; auto.
  assert (~L.leql k kobs).
  eapply opstack1_exception; eauto.
  assert (Heap.typeof h2' loc2=Some (Heap.LocationObject e)).
  eapply ExceptionStep_typeof; eauto.
  inversion_mine H2.
  inversion_mine H19.
  constructor 5 with e; eauto with lattice.
  constructor 5 with e; eauto with lattice.
  constructor 6 with cn e; eauto with lattice.
Qed. *)

(*
Lemma high_exec_return : 
 forall kobs p se reg m sgn pc i h2' 
                   h1' s1' l1' st1' b1' b2' v2' kd',

   ~ L.leql (se pc) kobs ->
   high_st kobs s1' st1' ->
   exec_return kobs p se reg m sgn i kd' (pc,(h1',s1',l1')) st1' b1' (h2',v2') b2' ->

   b1' = b2'.
Proof.
  intros.
  inversion_mine H1.
  auto.
  eapply high_step_exception; eauto.
Qed.

*)

