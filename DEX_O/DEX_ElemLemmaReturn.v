Require Export DEX_ElemLemmas.

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(* Step Consistent *)
(*Lemma indist1_return_normal : 
 forall kobs p se m sgn pc i r1 rt1 ov2,

   ~ L.leql (se pc) kobs ->
   ReturnStep p se m sgn i (pc,r1) rt1 (ov2) ->

  (forall kr, sgn.(DEX_resType) = Some kr -> ~ L.leql kr kobs).
Proof.
  intros.
  inversion H0. rewrite H9 in H1; inversion H1. 
  apply not_leql_trans with (k1:=(se pc)); auto.
  apply leql_join_each in H16; inversion H16; auto.
  rewrite H13 in H1; inversion H1.
  rewrite <- H20; auto.
Qed.*)

(* Locally Respect *)
Lemma indist2_intra_normal : 
 forall kobs p se m sgn pc i r1 rt1 r1' rt1' ov2 ov2' b1 b1' h1 h1' h2 h2',

   ReturnStep p se m sgn i (pc,(h1,r1)) rt1 (h2,ov2) ->
   ReturnStep p se m sgn i (pc,(h1',r1')) rt1' (h2',ov2') ->
   st_in kobs (DEX_ft p) b1 b1' rt1 rt1' (pc,h1,r1) (pc,h1',r1') ->

   indist_return_value kobs h2 h2' sgn ov2 ov2' b1 b1' /\
   hp_in kobs (DEX_ft p) b1 b1' h2 h2'.
Proof.
  intros. split.
  apply inv_st_in in H1.
  inversion H1.
  inversion H; inversion H0; DiscrimateEq; auto. 
  constructor; auto.
  specialize H3 with reg0.
  inversion H3; auto.
  constructor 1 with kr0; try (inversion H6); auto.  
  intros. apply not_leql_join1 with (k2:=(se pc)) in H7.
  rewrite H5 in H32. inversion H32. subst.
  apply L.leql_trans with (l1:=L.join k' (se pc)) (l3:=kobs) in H8; auto. contradiction.
  (* *)
  constructor 1 with kr0; try (inversion H6); auto.
  intros. inversion_mine H4. rewrite <- H6 in H13; inversion H13. 
  rewrite <- H7 in H30; inversion H30. auto. 
  rewrite <- H7 in H13; inversion H13. 
  (* hp_in *)
  inversion H1 as [pc0 pc0' h h' r r' HRegsIn HHpIn]; clear H1; subst.
  inversion H as [h pc0 r rt  Hins Hsig HresType | 
    pc0 h r reg val t k k1 rt kr Hins HinReg HinRT Hsig Hval Hsec Hcompat HresType Hleq]; 
    clear H; subst; 
  inversion H0 as [h pc0 r rt  Hins' Hsig' HresType' | 
    pc0 h r reg' val' t' k' k1' rt kr' Hins' HinReg' HinRT' Hsig' Hval' Hsec' Hcompat' HresType' Hleq'];
    clear H0; subst; auto. 
  (*inversion H19. constructor.
  rewrite <- H19 in H25; inversion H25.*)
Qed.

Lemma indist2_return : 
 forall kobs p se m sgn pc i r1 rt1 r1' rt1' v2 v2' h1 h1' h2 h2' b1 b1' b2 b2',

   exec_return p se m sgn i (pc,(h1,r1)) rt1 b1 (h2,v2) b2 ->
   exec_return p se m sgn i (pc,(h1',r1')) rt1' b1' (h2',v2') b2' ->
   st_in kobs (DEX_ft p) b1 b1' rt1 rt1' (pc,h1,r1) (pc,h1',r1') ->

   indist_return_value kobs h2 h2' sgn v2 v2' b2 b2' /\
      hp_in kobs (DEX_ft p) b2 b2' h2 h2'.
Proof.
  intros.
  inversion_mine H; inversion_mine H0.
  eapply indist2_intra_normal; eauto.
Qed.