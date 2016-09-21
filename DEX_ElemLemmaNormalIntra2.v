Require Export DEX_ElemLemmas.


Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_BigStep.DEX_Dom DEX_Prog.

(*  Opaque BigStep.Dom.Heap.update.*)

Section p.
  Variable kobs : L.t.
  Variable p : DEX_ExtendedProgram.

Lemma some_eq: forall (A:Type) (x y:A), Some x = Some y -> x = y.
Proof. intros; inversion H; auto. Qed.

Lemma leql_join_eq: forall (k k1 k2: L.t) , k2 = L.join k k1 -> L.leql k k2.
Proof. intros. subst; apply leql_join2; apply L.leql_refl; auto. Qed.

(* Locally Respect *)
Lemma indist2_intra_normal : 
 forall se reg m sgn pc pc2 pc2' i r1 rt1 r1' rt1' r2 r2' rt2 rt2',
   instructionAt m pc = Some i ->

   NormalStep se reg m sgn i (pc,r1) rt1 (pc2,r2) rt2 ->
   NormalStep se reg m sgn i (pc,r1') rt1' (pc2',r2') rt2' ->
   st_in kobs rt1 rt1' (pc,r1) (pc,r1') ->

   st_in kobs rt2 rt2' (pc2,r2) (pc2',r2').
Proof.
  intros.
  destruct i; simpl in H0, H1;
  inversion_clear H0 in H H1 H2;
  inversion_clear H1 in H2;
  apply inv_st_in in H2;  
(*   destruct (inv_st_in H2) as [Rin]; clear H2; *)
  constructor; auto.
  (* DEX_Move *)
  subst.
  inversion H2.
  (* specialize H10 with (rn:=rt).
  apply H6 with (v:=val) (v':=val0) (k:=k0) (k':=k1) in H5; auto. *)
  constructor; auto. 
  (* proving eq_set *)
  rewrite VarMap.domain_inv; auto. rewrite VarMap.domain_inv; auto. 
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
(*     clear H1 H7 H0 H10 H12. *)
    rewrite H25 in H23; rewrite VarMap.get_update1 in H23.
    rewrite H25 in H24; rewrite VarMap.get_update1 in H24.
    rewrite H25 in H21; rewrite DEX_Registers.get_update_new in H21.
    rewrite H25 in H22; rewrite DEX_Registers.get_update_new in H22.
    apply some_eq in H21; apply some_eq in H22; apply some_eq in H23; apply some_eq in H24.
    apply leql_join_eq in H23.
    apply leql_join_eq in H24.
    rewrite H25 in H12; rewrite H25 in H19.
    apply H10 with (v:=v) (v':=v') (k:=k0) (k':=k1) in H16; auto.
    apply Reg_in_monotony_left with (k'' := k2) in H16; auto.
    apply Reg_in_sym in H16. apply Reg_in_monotony_left with (k'' := k') in H16; auto.
    apply Reg_in_sym in H16; auto.
    subst; auto. subst; auto. 
(*  subst; auto.
    apply Reg_in_sym in H22.
    apply Reg_in_monotony_left with (k'' := k') in H22; auto.
    apply Reg_in_sym in H5; subst; trivial. *)
    (* rn <> rt *) 
    rewrite VarMap.get_update2 in H23; auto.
    rewrite VarMap.get_update2 in H24; auto.
    apply VarMap.in_dom_get_some in H12; rewrite VarMap.get_update2 in H12; auto.
    apply VarMap.get_some_in_dom in H12.
    apply VarMap.in_dom_get_some in H19; rewrite VarMap.get_update2 in H19; auto.
    apply VarMap.get_some_in_dom in H19.
    rewrite DEX_Registers.get_update_old in H21; auto.
    rewrite DEX_Registers.get_update_old in H22; auto.
    apply H10 with (k:=k2) (k':=k') (v:=v) (v':=v') in H12; auto.
  (* DEX_Const *)
  subst.
  inversion H2.
  constructor.
  rewrite VarMap.domain_inv; auto. rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H13.
    rewrite VarMap.get_update1 in H14.
    rewrite DEX_Registers.get_update_new in H11.
    rewrite DEX_Registers.get_update_new in H12.
    apply some_eq in H11; apply some_eq in H12; apply some_eq in H13; apply some_eq in H14.
    subst; apply Reg_in_refl.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H13; auto.
    rewrite VarMap.get_update2 in H14; auto.
    rewrite DEX_Registers.get_update_old in H11; auto.
    rewrite DEX_Registers.get_update_old in H12; auto.
    apply VarMap.in_dom_get_some in H7; rewrite VarMap.get_update2 in H7; auto.
    apply VarMap.get_some_in_dom in H7.
    apply VarMap.in_dom_get_some in H10; rewrite VarMap.get_update2 in H10; auto.
    apply VarMap.get_some_in_dom in H10.
(*     rewrite VarMap.domain_inv in H7; auto. rewrite VarMap.domain_inv in H10; auto. *)
    apply H6 with (k:=k0) (k':=k') (v:=v0) (v':=v') in H7; auto.
  (* DEX_Ineg *)
  subst. inversion H2.
  apply H10 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H6; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H21.
    rewrite VarMap.get_update1 in H22.
    rewrite DEX_Registers.get_update_new in H19.
    rewrite DEX_Registers.get_update_new in H20.
    apply some_eq in H19; apply some_eq in H20; apply some_eq in H21; apply some_eq in H22.
    apply leql_join_eq in H21; apply leql_join_eq in H22.
    apply Reg_in_monotony_left with (k'' := k1) in H6; auto.
    apply Reg_in_sym in H6.
    apply Reg_in_monotony_left with (k'' := k') in H6; auto.
    apply Reg_in_sym in H6; subst; auto.
    inversion H6. constructor 1; auto.
    constructor 2. inversion H19. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H21; auto.
    rewrite VarMap.get_update2 in H22; auto.
    rewrite DEX_Registers.get_update_old in H19; auto.
    rewrite DEX_Registers.get_update_old in H20; auto.
    apply VarMap.in_dom_get_some in H11; rewrite VarMap.get_update2 in H11; auto.
    apply VarMap.get_some_in_dom in H11.
    apply VarMap.in_dom_get_some in H18; rewrite VarMap.get_update2 in H18; auto.
    apply VarMap.get_some_in_dom in H18.
(*     rewrite VarMap.domain_inv in H11; auto; rewrite VarMap.domain_inv in H18; auto. *)
    apply H10 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H11; auto.
  (* DEX_Inot *)
  subst. inversion H2.
  apply H10 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H6; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H21.
    rewrite VarMap.get_update1 in H22.
    rewrite DEX_Registers.get_update_new in H19.
    rewrite DEX_Registers.get_update_new in H20.
    apply some_eq in H19; apply some_eq in H20; apply some_eq in H21; apply some_eq in H22.
    apply leql_join_eq in H21; apply leql_join_eq in H22.
    apply Reg_in_monotony_left with (k'' := k1) in H6; auto.
    apply Reg_in_sym in H6.
    apply Reg_in_monotony_left with (k'' := k') in H6; auto.
    apply Reg_in_sym in H6; subst; auto.
    inversion H6. constructor 1; auto.
    constructor 2. inversion H19. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H21; auto.
    rewrite VarMap.get_update2 in H22; auto.
    rewrite DEX_Registers.get_update_old in H19; auto.
    rewrite DEX_Registers.get_update_old in H20; auto.
    apply VarMap.in_dom_get_some in H11; rewrite VarMap.get_update2 in H11; auto.
    apply VarMap.get_some_in_dom in H11.
    apply VarMap.in_dom_get_some in H18; rewrite VarMap.get_update2 in H18; auto.
    apply VarMap.get_some_in_dom in H18.
(*     rewrite VarMap.domain_inv in H11; auto; rewrite VarMap.domain_inv in H18; auto. *)
    apply H10 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H11; auto.
  (* DEX I2b *)
  subst. inversion H2.
  apply H10 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H6; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H21.
    rewrite VarMap.get_update1 in H22.
    rewrite DEX_Registers.get_update_new in H19.
    rewrite DEX_Registers.get_update_new in H20.
    apply some_eq in H19; apply some_eq in H20; apply some_eq in H21; apply some_eq in H22.
    apply leql_join_eq in H21; apply leql_join_eq in H22.
    apply Reg_in_monotony_left with (k'' := k1) in H6; auto.
    apply Reg_in_sym in H6.
    apply Reg_in_monotony_left with (k'' := k') in H6; auto.
    apply Reg_in_sym in H6; subst; auto.
    inversion H6. constructor 1; auto.
    constructor 2. inversion H19. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H21; auto.
    rewrite VarMap.get_update2 in H22; auto.
    rewrite DEX_Registers.get_update_old in H19; auto.
    rewrite DEX_Registers.get_update_old in H20; auto.
(*     rewrite VarMap.domain_inv in H11; auto; rewrite VarMap.domain_inv in H18; auto. *)
    apply VarMap.in_dom_get_some in H11; rewrite VarMap.get_update2 in H11; auto.
    apply VarMap.get_some_in_dom in H11.
    apply VarMap.in_dom_get_some in H18; rewrite VarMap.get_update2 in H18; auto.
    apply VarMap.get_some_in_dom in H18.
    apply H10 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H11; auto.
  (* DEX_I2s *)
  subst. inversion H2.
  apply H10 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H6; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H21.
    rewrite VarMap.get_update1 in H22.
    rewrite DEX_Registers.get_update_new in H19.
    rewrite DEX_Registers.get_update_new in H20.
    apply some_eq in H19; apply some_eq in H20; apply some_eq in H21; apply some_eq in H22.
    apply leql_join_eq in H21; apply leql_join_eq in H22.
    apply Reg_in_monotony_left with (k'' := k1) in H6; auto.
    apply Reg_in_sym in H6.
    apply Reg_in_monotony_left with (k'' := k') in H6; auto.
    apply Reg_in_sym in H6; subst; auto.
    inversion H6. constructor 1; auto.
    constructor 2. inversion H19. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H21; auto.
    rewrite VarMap.get_update2 in H22; auto.
    rewrite DEX_Registers.get_update_old in H19; auto.
    rewrite DEX_Registers.get_update_old in H20; auto.
(*     rewrite VarMap.domain_inv in H11; auto; rewrite VarMap.domain_inv in H18; auto. *)
    apply VarMap.in_dom_get_some in H11; rewrite VarMap.get_update2 in H11; auto.
    apply VarMap.get_some_in_dom in H11.
    apply VarMap.in_dom_get_some in H18; rewrite VarMap.get_update2 in H18; auto.
    apply VarMap.get_some_in_dom in H18.
    apply H10 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H11; auto.
  (* DEX_IBinop *)
  subst. inversion H2.
  apply H14 with (v:=(Num (I i1))) (v':=(Num (I i0))) (k:=k1) (k':=k0) in H7; auto.
  apply H14 with (v:=(Num (I i2))) (v':=(Num (I i3))) (k:=k2) (k':=k3) in H8; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H29.
    rewrite VarMap.get_update1 in H30.
    rewrite DEX_Registers.get_update_new in H27.
    rewrite DEX_Registers.get_update_new in H28.
    apply some_eq in H27; apply some_eq in H28; apply some_eq in H29; apply some_eq in H30.
    assert (forall (k k1 k2 k3: L.t) , k3 = L.join k (L.join k1 k2) -> L.leql k k3 /\ L.leql k1 k3) as Hjoin.
      clear. intros. split. apply leql_join_eq with (k1:=L.join k1 k2); auto.
      subst. apply L.leql_trans with (l1:=k1) (l2:=L.join k1 k2) (l3:=L.join k (L.join k1 k2)).
      apply L.join_left. apply L.join_right.
    apply Hjoin in H29; apply Hjoin in H30.
    inversion H29; inversion H30.
    subst. 
    apply Reg_in_monotony_left with (k'' := k) in H7; auto.
    apply Reg_in_sym in H7.
    apply Reg_in_monotony_left with (k'' := k') in H7; auto.
    apply Reg_in_sym in H7.
    apply Reg_in_monotony_left with (k'' := k) in H8; auto.
    apply Reg_in_sym in H8.
    apply Reg_in_monotony_left with (k'' := k') in H8; auto.
    apply Reg_in_sym in H8.
    (* When any of the register is H *)
    inversion H7; inversion H8; try (constructor 1; auto; fail).
    (* When all the registers are L, they have to have the same value *)
    subst.
    constructor 2.
    inversion H27; inversion H38; constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H29; auto.
    rewrite VarMap.get_update2 in H30; auto.
    rewrite DEX_Registers.get_update_old in H27; auto.
    rewrite DEX_Registers.get_update_old in H28; auto.
(*     rewrite VarMap.domain_inv in H15; auto; rewrite VarMap.domain_inv in H26; auto. *)
    apply VarMap.in_dom_get_some in H15; rewrite VarMap.get_update2 in H15; auto.
    apply VarMap.get_some_in_dom in H15.
    apply VarMap.in_dom_get_some in H26; rewrite VarMap.get_update2 in H26; auto.
    apply VarMap.get_some_in_dom in H26.
    apply H14 with (k:=k) (k':=k') (v:=v) (v':=v') in H15; auto.
  (* DEX_IBinopConst *)
subst. inversion H2.
  apply H10 with (v:=(Num (I i))) (v':=(Num (I i0))) (k:=k) (k':=k0) in H6; auto.
  constructor.
  rewrite VarMap.domain_inv; auto; rewrite VarMap.domain_inv; auto.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H21.
    rewrite VarMap.get_update1 in H22.
    rewrite DEX_Registers.get_update_new in H19.
    rewrite DEX_Registers.get_update_new in H20.
    apply some_eq in H19; apply some_eq in H20; apply some_eq in H21; apply some_eq in H22.
    apply leql_join_eq in H21; apply leql_join_eq in H22.
    apply Reg_in_monotony_left with (k'' := k1) in H6; auto.
    apply Reg_in_sym in H6.
    apply Reg_in_monotony_left with (k'' := k') in H6; auto.
    apply Reg_in_sym in H6; subst; auto.
    inversion H6. constructor 1; auto.
    constructor 2. inversion H19. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H21; auto.
    rewrite VarMap.get_update2 in H22; auto.
    rewrite DEX_Registers.get_update_old in H19; auto.
    rewrite DEX_Registers.get_update_old in H20; auto.
    apply VarMap.in_dom_get_some in H11; rewrite VarMap.get_update2 in H11; auto.
    apply VarMap.get_some_in_dom in H11.
    apply VarMap.in_dom_get_some in H18; rewrite VarMap.get_update2 in H18; auto.
    apply VarMap.get_some_in_dom in H18.
(*     rewrite VarMap.domain_inv in H11; auto; rewrite VarMap.domain_inv in H18; auto. *)
    apply H10 with (k:=k1) (k':=k') (v:=v0) (v':=v') in H11; auto.
Qed.


End p.


