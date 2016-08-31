Require Export DEX_ElemLemmas.


Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(*   Opaque BigStep.Dom.Heap.update.
 *)
Section p.

Variable kobs: L.t.
Variable p:DEX_ExtendedProgram.
Variable se : DEX_PC -> L.t.
Variable reg : DEX_PC -> option DEX_ClassName -> DEX_PC -> Prop.
Variable m : DEX_Method.
(* Variable lookupswitch_hyp : well_formed_lookupswitch m. *)

(* High Branching *)
Lemma soap2_intra_normal : 
 forall sgn pc pc2 pc2' i r1 rt1 r1' rt1' r2 r2' rt2 rt2' ,
   instructionAt m pc = Some i ->

   NormalStep se reg m sgn i (pc,r1) rt1 (pc2,r2) rt2 ->
   NormalStep se reg m sgn i (pc,r1') rt1' (pc2',r2') rt2' ->

   pc2 <> pc2' ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

   (*high_st kobs s2 st2 /\*) forall j, reg pc None j -> ~ L.leql (se j) kobs.
Proof.
  intros.
  destruct i; simpl in H, H0, H1, H3; 
(*   try (elim Hs; fail); *)
  inversion_clear H0 in H H1 H2 H3;
  inversion_clear H1 in H2 H3; subst;
(*   destruct (inv_st_in H3) as [Rin]; clear H3; *)
  apply inv_st_in in H3;  
  DiscrimateEq; try (elim H2; reflexivity); try (contradiction). 
  unfold not; intros.
  (* If_icmp *)
  inversion H3.
  apply H17 with (v':=Num (I i3)) (k:=k1) (k':=k0) in H5; auto .
    (* ra *)
    inversion H5. apply H16 in H4.
    apply not_leql_trans with (k2:=se j) in H19; auto. 
    apply leql_join_each in H4; inversion H4; auto.
    (* rb *)
    apply H17 with (v':=Num (I i0)) (k:=k2) (k':=k3) in H6; auto.
    inversion H6. apply H10 in H4.
    apply not_leql_trans with (k2:=se j) in H23; auto.
    apply leql_join_each in H4; inversion H4; auto.
    (* both are low *)
    inversion H18. inversion H23.
    subst; contradiction. 
  inversion H3.
  apply H1 with (v':=Num (I i3)) (k:=k1) (k':=k0) in H6; auto . 
    (* ra *)
    inversion H6. apply H16 in H4.
    apply not_leql_trans with (k2:=se j) in H18; auto. 
    apply leql_join_each in H4; inversion H4; auto.
    (* rb *)
    apply H1 with (v':=Num (I i0)) (k:=k2) (k':=k3) in H7; auto.
    inversion H7. apply H11 in H4.
    apply not_leql_trans with (k2:=se j) in H22; auto.
    apply leql_join_each in H4; inversion H4; auto.
    (* both are low *)
    inversion H17. inversion H22.
    subst; contradiction. 
Qed.
(*
Lemma opstack1_intra_normal : 
 forall sgn pc pc2 i h1 h2 s1 l1 st1 b1 b2 s2 st2 l2,
   
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1 st1 ->
   NormalStep kobs p se reg m sgn i
     (pc,(h1,s1,l1)) st1 b1 (pc2,(h2,s2,l2)) st2 b2 ->
   high_st kobs s2 st2.
Proof.
  intros.
  destruct i; simpl in H2; inversion_mine H2;
  try (match goal with
    [ id : high_st kobs (_++?s) (_++?st) |- _ ] =>
    assert (hi:high_st kobs s st); [apply (@high_st_app _ _ _ _ id); congruence|idtac]
  end);
  repeat match goal with
      [ id : high_st _ (_::_) (_::_) |- _ ] => inversion_mine id
  end;
  repeat constructor; auto;
  try (apply lift_os_high; auto);
  try (apply elift_os_high; auto);
  simpl in *; eauto with lattice.
  destruct op; auto; try (apply lift_os_high; auto).
  try (apply elift_os_high; auto).
  try (apply elift_os_high; auto).
Qed.
*)
End p.




