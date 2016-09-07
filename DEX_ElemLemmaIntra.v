Require Export DEX_ElemLemmas.
(* Require Export DEX_ElemLemmaNormalIntra1. *)
Require Export DEX_ElemLemmaNormalIntra2.
Require Export DEX_ElemLemmaNormalIntra3.
(*Require Export ElemLemmaException1.
Require Export ElemLemmaException2.
Require Export ElemLemmaException3.
Require Export ElemLemmaException4.
Require Export ElemLemmaNormalIntraException2.*)

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(* Lemma high_exec_intra : 
 forall kobs p se reg m sgn pc i r1 rt1 rt2 r2 pc2 kd,
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1 st1 ->
   exec_intra kobs p se reg m sgn i kd
     (pc,(h1,s1,l1)) st1 b1 (pc2,(h2,s2,l2)) st2 b2 ->
   b1 = b2.
Proof.
  intros.
  inversion_mine H2.
  eapply high_exec_normal; eauto.
  eapply high_step_exception; eauto.
Qed. *)

(* Lemma opstack1_intra : 
 forall kobs p se reg m sgn pc i h1 s1 l1 st1 b1 st2 b2 s2 h2 pc2 l2 kd,
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1 st1 ->
   exec_intra kobs p se reg m sgn i kd
     (pc,(h1,s1,l1)) st1 b1 (pc2,(h2,s2,l2)) st2 b2 ->
   high_st kobs s2 st2.
Proof.
  intros.
  inversion_mine H2.
  eapply opstack1_intra_normal; eauto.
  repeat constructor.
  eapply opstack1_exception; eauto.
Qed. *)

(* Lemma indist1_intra : 
 forall kobs p se reg m sgn pc pc1 pc2' i h1 h2' s1 l1 st1 b1 
                   h1' s1' l1' st1' b1' b2' s2' st2' l2' kd,
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1' st1' ->
   exec_intra kobs p se reg m sgn i kd
     (pc,(h1',s1',l1')) st1' b1' (pc2',(h2',s2',l2')) st2' b2' ->

   st_in kobs (newArT p) (ft p) sgn.(lvt) b1 b1' st1 st1' (pc1,h1,s1,l1) (pc,h1',s1',l1') ->

   st_in kobs (newArT p) (ft p) sgn.(lvt) b1 b2' st1 st2' (pc1,h1,s1,l1) (pc2',h2',s2',l2').
Proof.
  intros.
  inversion_mine H2.
  eapply indist1_intra_normal; eauto.
  eapply indist1_exception; eauto.
Qed. *)

Lemma indist2_intra : 
 forall kobs (p:DEX_ExtendedProgram) se reg m sgn pc pc2 pc2' i r1 rt1 r1' rt1' r2 r2' rt2 rt2' (* kd *) (* kd' *),
   instructionAt m pc = Some i ->

   exec_intra kobs reg m sgn i (* kd *) (pc,r1) rt1 (pc2,r2) rt2 ->
   exec_intra kobs reg m sgn i (* kd' *) (pc,r1') rt1' (pc2',r2') rt2' ->

   st_in se rt1 rt1' (pc,r1) (pc,r1') ->

   st_in se rt2 rt2' (pc2,r2) (pc2',r2').
Proof.
  intros.
  inversion_mine H0; inversion_mine H1.

  eapply indist2_intra_normal; eauto.

  (* elim indist2_normal_exception with (1:=H3) (2:=H16) (3:=H2) (4:=H19).
  intros U1 (U2,(U3,(U4,U5))).
  constructor; auto.
  repeat constructor; auto.

  elim indist2_normal_exception with (1:=H0) (2:=H16) (3:=(st_in_sym kobs p _ _ _ _ _ _ _ H2)) (4:=H19);
  intros U1 (U2,(U3,(U4,U5))).
  constructor; auto.
  apply localvar_in_sym; auto.
  repeat constructor; auto.
  apply hp_in_sym; auto.

  eapply indist2_exception; eauto. *)
Qed.

Lemma soap2_intra : 
 forall kobs (p:DEX_ExtendedProgram) se reg m sgn pc pc2 pc2' i r1 rt1 (* kd *) (* kd' *)
                   r1' rt1' r2 r2' rt2 rt2',
(*                    well_formed_lookupswitch m -> *)
   instructionAt m pc = Some i ->

   exec_intra se reg m sgn i (* kd *) (pc,r1) rt1 (pc2,r2) rt2 ->
   exec_intra se reg m sgn i (* kd' *) (pc,r1') rt1' (pc2',r2') rt2' ->

   pc2<>pc2' ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

(*    high_st kobs s2 st2 /\ *)
   forall j, reg pc (* kd *) j -> ~ L.leql (se j) kobs.
Proof.
  intros.
  inversion_mine H0; inversion_mine H1.

  eapply soap2_intra_normal. eauto. 
  apply H5. eauto. eauto. 
  eauto. eauto.

  (* elim indist2_normal_exception with (1:=H5) (2:=H18) (3:=H4) (4:=H21);
  intros U1 (U2,(U3,(U4,U5))).
  split; auto; intros.

  elim indist2_normal_exception with (1:=H1) (2:=H18) (3:=(st_in_sym _ p _ _ _ _ _ _ _ H4)) (4:=H21);
  intros U1 (U2,(U3,(U4,U5))).
  split; auto; intros.
  repeat constructor; auto.
  generalize (H20 _ H2).
  eauto with lattice.

 
  assert (e<>e0).
  intro; subst; elim H3.
  apply CaughtException_same3 with (1:=H19) (3:=H22).
  rewrite (ExceptionStep_typeof H17); rewrite (ExceptionStep_typeof H18); auto.
  assert (~ L.leql k kobs).
  eapply soap2_exception with (1:=H18) (2:=H17); eauto.
  split; intros.
  repeat constructor; auto.
  generalize (H20 _ H5); eauto with lattice. *)
Qed.





