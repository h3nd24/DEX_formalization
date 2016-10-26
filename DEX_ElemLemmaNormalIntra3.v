Require Export DEX_ElemLemmas.


Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(*   Opaque BigStep.Dom.Heap.update.
 *)
Section p.

Variable kobs: L.t.
Variable p:DEX_ExtendedProgram.
Variable se : DEX_PC -> L.t.
Variable reg : DEX_PC -> (* option DEX_ClassName -> *) DEX_PC -> Prop.
Variable m : DEX_Method.
(* Variable lookupswitch_hyp : well_formed_lookupswitch m. *)

Ltac soap2_intra_normal_aux Hreg_in H Hreg r lvl Hget_ori Hvalue_opt_in k k':=
  specialize Hreg_in with r;
  inversion Hreg_in as [k k' Hget Hget' Hleq Hleq'| Hvalue_opt_in];
  try (apply H in Hreg; apply leql_join_each in Hreg; inversion Hreg as [Hleql1 Hleql1'];
    apply not_leql_trans with (k2:=lvl) in Hleq; auto);
  try (apply H in Hreg; apply not_leql_trans with (k2:=lvl) in Hleq; auto);
  try (rewrite Hget in Hget_ori; inversion Hget_ori; subst; auto).

(* High Branching *)
Lemma soap2_intra_normal : 
 forall sgn pc pc2 pc2' i r1 rt1 r1' rt1' r2 r2' rt2 rt2' ,
   instructionAt m pc = Some i ->
   NormalStep se reg m sgn i (pc,r1) rt1 (pc2,r2) rt2 ->
   NormalStep se reg m sgn i (pc,r1') rt1' (pc2',r2') rt2' ->
   pc2 <> pc2' ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

    forall j, reg pc j -> ~ L.leql (se j) kobs.
Proof.
  intros sgn pc pc2 pc2' i r1 rt1 r1' rt1' r2 r2' rt2 rt2' Hins Hstep Hstep' Hpc Hst_in j Hreg.
  destruct i; simpl in Hins, Hstep, Hstep', Hst_in; 
  inversion_clear Hstep in Hins Hstep' Hpc Hst_in;
  inversion_clear Hstep' in Hpc Hst_in; subst;
  apply inv_st_in in Hst_in;
  DiscrimateEq; try (elim Hpc; reflexivity); try (contradiction).
  (* If_icmp *)
  inversion Hst_in as [Heqset Hreg_in].
    (* ra *)
    assert (Hreg_in':=Hreg_in).
    soap2_intra_normal_aux Hreg_in H8 Hreg ra (se j) H5 Hvalue_opt_in k k'.
    (* rb *)
    soap2_intra_normal_aux Hreg_in' H8 Hreg rb (se j) H6 Hvalue_opt_in' k k'.
    (* both are low *)
    rewrite <- H3 in Hvalue_opt_in; rewrite <- H4 in Hvalue_opt_in'; 
    rewrite <- H14 in Hvalue_opt_in; rewrite <- H15 in Hvalue_opt_in'.
    inversion Hvalue_opt_in as [v v' Hvalue_in | Hnone]; 
    inversion Hvalue_opt_in' as [v2 v2' Hvalue_in' | Hnone'];
    inversion Hvalue_in; inversion Hvalue_in'. 
    subst; contradiction.  
  inversion Hst_in as [Heqset Hreg_in].
    (* ra *)
    assert (Hreg_in':=Hreg_in).
    soap2_intra_normal_aux Hreg_in H9 Hreg ra (se j) H6 Hvalue_opt_in k k'.
    (* rb *)
    soap2_intra_normal_aux Hreg_in' H9 Hreg rb (se j) H7 Hvalue_opt_in' k k'.
    (* both are low *)
    rewrite <- H4 in Hvalue_opt_in; rewrite <- H5 in Hvalue_opt_in'; 
    rewrite <- H14 in Hvalue_opt_in; rewrite <- H15 in Hvalue_opt_in'.
    inversion Hvalue_opt_in as [v v' Hvalue_in | Hnone]; 
    inversion Hvalue_opt_in' as [v2 v2' Hvalue_in' | Hnone'];
    inversion Hvalue_in; inversion Hvalue_in'. 
    subst; contradiction.   
  (* If_z *)
  inversion Hst_in as [Heq_set Hreg_in].
    soap2_intra_normal_aux Hreg_in H4 Hreg r (se j) H2 Hvalue_opt_in k1 k1'.
    rewrite <- H1 in Hvalue_opt_in; rewrite <- H8 in Hvalue_opt_in;
      inversion Hvalue_opt_in as [v v' Hvalue_in | Hnone]; 
      inversion Hvalue_in; subst; contradiction.
  inversion Hst_in as [Heq_set Hreg_in].
    soap2_intra_normal_aux Hreg_in H5 Hreg r (se j) H3 Hvalue_opt_in k1 k1'.
    rewrite <- H2 in Hvalue_opt_in; rewrite <- H8 in Hvalue_opt_in;
      inversion Hvalue_opt_in as [v v' Hvalue_in | Hnone]; 
      inversion Hvalue_in; subst; contradiction.
Qed. 

End p.




