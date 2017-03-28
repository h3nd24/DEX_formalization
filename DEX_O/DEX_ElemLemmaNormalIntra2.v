Require Export DEX_ElemLemmas.

Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

Section p.
  Variable kobs : L.t.
  Variable p : DEX_ExtendedProgram.

Lemma some_eq: forall (A:Type) (x y:A), Some x = Some y -> x = y.
Proof. intros; inversion H; auto. Qed.

Lemma leql_join_eq: forall (k k1 k2: L.t) , k2 = L.join k k1 -> L.leql k k2.
Proof. intros. subst; apply leql_join2; apply L.leql_refl; auto. Qed.

Ltac indist2_intra_normal_aux Hindistreg rn:=
  specialize Hindistreg with rn;
  inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist];
  try (constructor 1 with (k:=lvl) (k':=lvl'); 
  try (rewrite MapList.get_update2; auto); auto);
  try (constructor 2; rewrite ?DEX_Registers.get_update_old; auto).

Lemma indist2_intra_normal : 
 forall se reg m sgn pc pc2 pc2' i r1 rt1 h1 b1 
      r1' rt1' h1' b1' r2 rt2 h2 b2 r2' rt2' h2' b2',
   instructionAt m pc = Some i ->

   NormalStep kobs p se reg m sgn i (pc,(h1,r1)) rt1 b1 (pc2,(h2,r2)) rt2 b2 ->
   NormalStep kobs p se reg m sgn i (pc,(h1',r1')) rt1' b1' (pc2',(h2',r2')) rt2' b2'->
   st_in kobs (DEX_ft p) b1 b1' rt1 rt1' (pc,h1,r1) (pc,h1',r1') ->

   st_in kobs (DEX_ft p) b2 b2' rt2 rt2' (pc2,h2,r2) (pc2',h2',r2').
Proof.
  intros se reg m sgn pc pc2 pc2' i r1 rt1 h1 b1 
      r1' rt1' h1' b1' r2 rt2 h2 b2 r2' rt2' h2' b2'
    Hins Hstep Hstep' Hindist.
  inversion_clear Hindist.
  destruct i; simpl in Hstep, Hstep';
  inversion_clear Hstep in Hins Hstep' H H0;
  inversion_clear Hstep' in H H0;
  constructor; auto. 
  (* DEX_Move *)
  subst.
  inversion H as [Heqset Hindistreg].
  constructor; auto. 
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn.
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=rs).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k0 (se pc)) (k':=L.join k1 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H7; inversion H7; subst; apply not_leql_join1; auto.
    rewrite Hget' in H17; inversion H17; subst; apply not_leql_join1; auto.
    constructor 2. rewrite <- H5 in Hvalueindist; rewrite <- H15 in Hvalueindist.
    rewrite ?DEX_Registers.get_update_new; auto.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_Const *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    constructor 2.
    rewrite ?DEX_Registers.get_update_new.
    constructor 1. constructor.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_Ineg *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=rs).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k (se pc)) (k':=L.join k0 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H5; inversion H5; subst; apply not_leql_join1; auto.
    rewrite Hget' in H14; inversion H14; subst; apply not_leql_join1; auto.
    constructor 2. rewrite <- H4 in Hvalueindist; rewrite <- H13 in Hvalueindist.
    rewrite ?DEX_Registers.get_update_new; auto.
    inversion Hvalueindist. inversion H15. constructor 1; constructor.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_Inot *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=rs).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k (se pc)) (k':=L.join k0 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H5; inversion H5; subst; apply not_leql_join1; auto.
    rewrite Hget' in H14; inversion H14; subst; apply not_leql_join1; auto.
    constructor 2. rewrite <- H4 in Hvalueindist; rewrite <- H13 in Hvalueindist.
    rewrite ?DEX_Registers.get_update_new; auto.
    inversion Hvalueindist. inversion H15. constructor 1; constructor.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX I2b *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=rs).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k (se pc)) (k':=L.join k0 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H5; inversion H5; subst; apply not_leql_join1; auto.
    rewrite Hget' in H14; inversion H14; subst; apply not_leql_join1; auto.
    constructor 2. rewrite <- H4 in Hvalueindist; rewrite <- H13 in Hvalueindist.
    rewrite ?DEX_Registers.get_update_new; auto.
    inversion Hvalueindist. inversion H15. constructor 1; constructor.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_I2s *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=rs).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k (se pc)) (k':=L.join k0 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H5; inversion H5; subst; apply not_leql_join1; auto.
    rewrite Hget' in H14; inversion H14; subst; apply not_leql_join1; auto.
    constructor 2. rewrite <- H4 in Hvalueindist; rewrite <- H13 in Hvalueindist.
    rewrite ?DEX_Registers.get_update_new; auto.
    inversion Hvalueindist. inversion H15. constructor 1; constructor.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_IBinop *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    assert (Hindistreg' := Hindistreg).
    specialize Hindistreg with (rn:=ra).
    specialize Hindistreg' with (rn:=rb).  
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k1 (L.join k2 (se pc))) (k':=L.join k0 (L.join k3 (se pc))); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H8; inversion H8; subst; apply not_leql_join1; auto.
    rewrite Hget' in H21; inversion H21; subst; apply not_leql_join1; auto.
    (* case of register b *)
    inversion Hindistreg' as [lvl2 lvl2' Hget2 Hget2' Hleq2 Hleq2' | Hvalueindist'].
    constructor 1 with (k:=L.join k1 (L.join k2 (se pc))) (k':=L.join k0 (L.join k3 (se pc))); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget2 in H9; inversion H9; subst.
    apply not_leql_join2; apply not_leql_join1; auto.
    rewrite Hget2' in H22; inversion H22; subst.
    apply not_leql_join2; apply not_leql_join1; auto.
    constructor 2. 
    rewrite ?DEX_Registers.get_update_new.
    rewrite <- H6 in Hvalueindist; rewrite <- H19 in Hvalueindist.
    rewrite <- H7 in Hvalueindist'; rewrite <- H20 in Hvalueindist'.
    inversion Hvalueindist as [v v' Hin | Hnone]; inversion Hvalueindist' as [v2 v2' Hin' | Hnone']; 
    inversion Hin; inversion Hin'. repeat (constructor); auto.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.
  (* DEX_IBinopConst *)
  subst.
  inversion Hindist as [Heqset Hindistreg].
  constructor; auto.
  (* proving eq_set *)
  rewrite MapList.domain_inv; auto. rewrite MapList.domain_inv; auto.
  intros rn. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt) as [Hreg | Hreg].
    (* rn = rt *)
    rewrite Hreg.
    specialize Hindistreg with (rn:=r).
    inversion Hindistreg as [lvl lvl' Hget Hget' Hleq Hleq' | Hvalueindist]. 
    constructor 1 with (k:=L.join k (se pc)) (k':=L.join k0 (se pc)); 
      try (rewrite MapList.get_update1; auto); auto.
    rewrite Hget in H5; inversion H5; subst; apply not_leql_join1; auto.
    rewrite Hget' in H14; inversion H14; subst; apply not_leql_join1; auto.
    constructor 2. 
    rewrite ?DEX_Registers.get_update_new.
    rewrite <- H4 in Hvalueindist; rewrite <- H13 in Hvalueindist. 
    inversion Hvalueindist as [val val' Hin | Hnone]; inversion Hin;
    repeat (constructor); auto.
    (* rn <> rt *) 
    indist2_intra_normal_aux Hindistreg rn.

Qed.


End p.