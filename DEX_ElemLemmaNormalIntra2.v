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
  apply H1 with (v:=val) (v':=val0) (k:=k0) (k':=k1) in H5; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
(*     clear H1 H7 H0 H10 H12. *)
    subst.
    rewrite VarMap.get_update1 in H11.
    rewrite VarMap.get_update1 in H13.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H8.
    apply some_eq in H6; apply some_eq in H8; apply some_eq in H11; apply some_eq in H13.
    apply leql_join_eq in H11.
    apply leql_join_eq in H13.
    apply Reg_in_monotony_left with (k'' := k2) in H5; auto.
    apply Reg_in_sym in H5.
    apply Reg_in_monotony_left with (k'' := k') in H5; auto.
    apply Reg_in_sym in H5; subst; trivial.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H11; auto.
    rewrite VarMap.get_update2 in H13; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H8; auto.
    apply H1 with (k:=k2) (k':=k') (v:=v) (v':=v') in H6; auto.
  (* DEX_Const *)
  subst.
  inversion H2.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H6.
    rewrite VarMap.get_update1 in H7.
    rewrite DEX_Registers.get_update_new in H4.
    rewrite DEX_Registers.get_update_new in H5.
    apply some_eq in H4; apply some_eq in H5; apply some_eq in H6; apply some_eq in H7.
    subst; apply Reg_in_refl.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H6; auto.
    rewrite VarMap.get_update2 in H7; auto.
    rewrite DEX_Registers.get_update_old in H4; auto.
    rewrite DEX_Registers.get_update_old in H5; auto.
    apply H1 with (k:=k0) (k':=k') (v:=v0) (v':=v') in H4; auto.
  (* DEX_Ineg *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H4; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H10.
    rewrite VarMap.get_update1 in H11.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H7.
    apply some_eq in H6; apply some_eq in H7; apply some_eq in H10; apply some_eq in H11.
    apply leql_join_eq in H10; apply leql_join_eq in H11.
    apply Reg_in_monotony_left with (k'' := k1) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4; subst; auto.
    inversion H4. constructor 1; auto.
    constructor 2. inversion H6. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H10; auto.
    rewrite VarMap.get_update2 in H11; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H7; auto.
    apply H1 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H6; auto.
  (* DEX_Inot *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H4; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H10.
    rewrite VarMap.get_update1 in H11.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H7.
    apply some_eq in H6; apply some_eq in H7; apply some_eq in H10; apply some_eq in H11.
    apply leql_join_eq in H10; apply leql_join_eq in H11.
    apply Reg_in_monotony_left with (k'' := k1) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4; subst; auto.
    inversion H4. constructor 1; auto.
    constructor 2. inversion H6. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H10; auto.
    rewrite VarMap.get_update2 in H11; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H7; auto.
    apply H1 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H6; auto.
  (* DEX_I2b *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H4; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H10.
    rewrite VarMap.get_update1 in H11.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H7.
    apply some_eq in H6; apply some_eq in H7; apply some_eq in H10; apply some_eq in H11.
    apply leql_join_eq in H10; apply leql_join_eq in H11.
    apply Reg_in_monotony_left with (k'' := k1) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4; subst; auto.
    inversion H4. constructor 1; auto.
    constructor 2. inversion H6. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H10; auto.
    rewrite VarMap.get_update2 in H11; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H7; auto.
    apply H1 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H6; auto.
  (* DEX_I2s *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I v))) (v':=(Num (I v0))) (k:=k) (k':=k0) in H4; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H10.
    rewrite VarMap.get_update1 in H11.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H7.
    apply some_eq in H6; apply some_eq in H7; apply some_eq in H10; apply some_eq in H11.
    apply leql_join_eq in H10; apply leql_join_eq in H11.
    apply Reg_in_monotony_left with (k'' := k1) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4; subst; auto.
    inversion H4. constructor 1; auto.
    constructor 2. inversion H6. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H10; auto.
    rewrite VarMap.get_update2 in H11; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H7; auto.
    apply H1 with (k:=k1) (k':=k') (v:=v1) (v':=v') in H6; auto.
  (* DEX_IBinop *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I i1))) (v':=(Num (I i0))) (k:=k1) (k':=k0) in H4; auto.
  apply H1 with (v:=(Num (I i2))) (v':=(Num (I i3))) (k:=k2) (k':=k3) in H5; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H14.
    rewrite VarMap.get_update1 in H15.
    rewrite DEX_Registers.get_update_new in H8.
    rewrite DEX_Registers.get_update_new in H9.
    apply some_eq in H14; apply some_eq in H15; apply some_eq in H8; apply some_eq in H9.
    assert (forall (k k1 k2 k3: L.t) , k3 = L.join k (L.join k1 k2) -> L.leql k k3 /\ L.leql k1 k3).
      clear. intros. split. apply leql_join_eq with (k1:=L.join k1 k2); auto.
      subst. apply L.leql_trans with (l1:=k1) (l2:=L.join k1 k2) (l3:=L.join k (L.join k1 k2)).
      apply L.join_left. apply L.join_right.
    apply H16 in H14; apply H16 in H15.
    inversion H14; inversion H15; clear H14 H15 H16.
    subst. 
    apply Reg_in_monotony_left with (k'' := k) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k) in H5; auto.
    apply Reg_in_sym in H5.
    apply Reg_in_monotony_left with (k'' := k') in H5; auto.
    apply Reg_in_sym in H5.
    (* When any of the register is H *)
    inversion H4; inversion H5; try (constructor 1; auto; fail).
    (* When all the registers are L, they have to have the same value *)
    subst.
    constructor 2.
    inversion H8; inversion H21; constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H14; auto.
    rewrite VarMap.get_update2 in H15; auto.
    rewrite DEX_Registers.get_update_old in H8; auto.
    rewrite DEX_Registers.get_update_old in H9; auto.
    apply H1 with (k:=k) (k':=k') (v:=v) (v':=v') in H8; auto.
  (* DEX_IBinopConst *)
  subst. inversion H2.
  apply H1 with (v:=(Num (I i))) (v':=(Num (I i0))) (k:=k) (k':=k0) in H4; auto.
  constructor.
  intros. 
  destruct Reg_eq_dec with (x:=rn) (y:=rt).
    (* rn = rt *)
    subst.
    rewrite VarMap.get_update1 in H10.
    rewrite VarMap.get_update1 in H11.
    rewrite DEX_Registers.get_update_new in H6.
    rewrite DEX_Registers.get_update_new in H7.
    apply some_eq in H6; apply some_eq in H7; apply some_eq in H10; apply some_eq in H11.
    apply leql_join_eq in H10; apply leql_join_eq in H11.
    apply Reg_in_monotony_left with (k'' := k1) in H4; auto.
    apply Reg_in_sym in H4.
    apply Reg_in_monotony_left with (k'' := k') in H4; auto.
    apply Reg_in_sym in H4; subst; auto.
      (* If the register is nleq kobs *)
      inversion H4. constructor 1; auto.
      (* If the register is <= kobs *)      
      constructor 2. inversion H6. constructor.
    (* rn <> rt *)
    rewrite VarMap.get_update2 in H10; auto.
    rewrite VarMap.get_update2 in H11; auto.
    rewrite DEX_Registers.get_update_old in H6; auto.
    rewrite DEX_Registers.get_update_old in H7; auto.
    apply H1 with (k:=k1) (k':=k') (v:=v0) (v':=v') in H6; auto.
Qed.


End p.


