Require Export DEX_ElemLemmas.

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(* Step Consistent *)
Lemma indist1_return_normal : 
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
Qed.

(* Locally Respect *)
Lemma indist2_intra_normal : 
 forall kobs p se m sgn pc i r1 rt1 r1' rt1' ov2 ov2',

   ReturnStep p se m sgn i (pc,r1) rt1 (ov2) ->
   ReturnStep p se m sgn i (pc,r1') rt1' (ov2') ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

   indist_return_value kobs sgn ov2 ov2'.
Proof.
  intros.
  apply inv_st_in in H1.
  inversion H1.
  inversion H; inversion H0; DiscrimateEq; auto. 
  constructor; auto.
  specialize H3 with reg0.
  inversion H3; auto.
  constructor 1 with kr0; try (inversion H6); auto.  
  intros. apply not_leql_join1 with (k2:=(se pc)) in H16.
  rewrite H5 in H26. inversion H26. subst.
  apply L.leql_trans with (l1:=L.join k' (se pc)) (l3:=kobs) in H33; auto. contradiction.
  constructor 1 with kr0; try (inversion H6); auto.
  intros. inversion_mine H4. rewrite <- H16 in H10; inversion H10. 
  rewrite <- H17 in H25; inversion H25. inversion H19. constructor.
  rewrite <- H19 in H25; inversion H25.
Qed.

Lemma indist2_return : 
 forall kobs se reg m sgn pc i r1 rt1 r1' rt1' v2 v2',

   exec_return se reg m sgn i (pc,r1) rt1 (v2) ->
   exec_return se reg m sgn i (pc,r1') rt1' (v2') ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

     indist_return_value kobs sgn v2 v2'.
Proof.
  intros.
  inversion_mine H; inversion_mine H0.
  eapply indist2_intra_normal; eauto.
Qed.