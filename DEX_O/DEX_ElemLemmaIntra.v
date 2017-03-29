Require Export DEX_ElemLemmas.
Require Export DEX_ElemLemmaNormalIntra2.
Require Export DEX_ElemLemmaNormalIntra3.

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

Lemma indist2_intra : 
 forall kobs (p:DEX_ExtendedProgram) se reg m sgn pc pc2 pc2' i r1 rt1 r1' rt1' 
      r2 r2' rt2 rt2' h1 h1' h2 h2' b1 b1' b2 b2',
   instructionAt m pc = Some i ->

   exec_intra kobs p se reg m sgn i (pc,(h1,r1)) rt1 b1 (pc2,(h2,r2)) rt2 b2 ->
   exec_intra kobs p se reg m sgn i (pc,(h1',r1')) rt1' b1' (pc2',(h2',r2')) rt2' b2' ->

   st_in kobs (DEX_ft p) b1 b1' rt1 rt1' (pc,h1,r1) (pc,h1',r1') ->

   st_in kobs (DEX_ft p) b2 b2' rt2 rt2' (pc2,h2,r2) (pc2',h2',r2').
Proof.
  intros.
  inversion_mine H0; inversion_mine H1.

  eapply indist2_intra_normal; eauto.
Qed.

Lemma soap2_intra : 
 forall kobs (p:DEX_ExtendedProgram) se reg m sgn pc pc2 pc2' i r1 rt1
                   r1' rt1' r2 r2' rt2 rt2' h1 h1' h2 h2' b1 b1' b2 b2',
   well_formed_lookupswitch m ->
   instructionAt m pc = Some i ->

   exec_intra kobs p se reg m sgn i (pc,(h1,r1)) rt1 b1 (pc2,(h2,r2)) rt2 b2 ->
   exec_intra kobs p se reg m sgn i (pc,(h1',r1')) rt1' b1' (pc2',(h2',r2')) rt2' b2' ->

   pc2<>pc2' ->
   st_in kobs (DEX_ft p) b1 b1' rt1 rt1' (pc,h1,r1) (pc,h1',r1') ->

   forall j, reg pc j -> ~ L.leql (se j) kobs.
Proof.
  intros.
  inversion_mine H1; inversion_mine H2.
  eapply soap2_intra_normal. eauto. eauto. apply H6. eauto. 
  eauto. eauto. 
  eauto.
Qed.