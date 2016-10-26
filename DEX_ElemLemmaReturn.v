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
  specialize H3 with reg0.
(*   apply H3 with (k':=k2) (v':=val0) (v:=val) (k:=k1) in H23 ; auto. *)
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
 forall kobs se reg m sgn pc i r1 rt1 r1' rt1' v2 v2' (* kd *) (* kd' *),

   exec_return se reg m sgn i (* kd *) (pc,r1) rt1 (v2) ->
   exec_return se reg m sgn i (* kd' *) (pc,r1') rt1' (v2') ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

     indist_return_value kobs sgn v2 v2'.
Proof.
  intros.
  inversion_mine H; inversion_mine H0.
  eapply indist2_intra_normal; eauto.
Qed.
