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

  eapply soap2_intra_normal. eauto.  apply H5.
  (* apply H5. *) eauto. eauto. 
  eauto. eauto.
Qed.





