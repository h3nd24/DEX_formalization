Require Export JVM_Final.
Require Export DEX_Final.
Require Export DX_Translator.

Import DX_TRANSLATOR JVM_Dom JVM_Prog DEX_Dom DEX_Prog.
(*
Lemma silly : forall rt1 rt2 l a maxLocals lvt, 
  tsub_rec rt1 rt2 (BinNatMap.dom _ (translate_st_rt l maxLocals lvt)) = true ->
  tsub_element rt1 rt2 a = true ->
  tsub_rec rt1 rt2 (BinNatMap.dom _ (translate_st_rt (a::l) maxLocals lvt)) = true.
*)

Lemma cons_length : forall A (a:A) l, length (a :: l) = (1 + length l)%nat.
Proof. auto. Qed.

Lemma N_of_nat_succ : forall (m:nat), N.succ (N_toVar m) = N_toVar (S m).
Proof. intros; induction m; auto. Qed.

Lemma N_eq_nat : forall (m n:nat), (m + n - 1)%nat = 
    N.to_nat (N_toVar m + N_toVar n - 1).
Proof.
    intros. destruct n.
    rewrite plus_0_r. rewrite N.add_0_r.
    destruct m; auto. 
    rewrite <- N_of_nat_succ; rewrite <- N.pred_sub; rewrite N.pred_succ.
    simpl; rewrite <- minus_n_O; rewrite nat_of_N_bij1; auto.
    
    rewrite NPeano.Nat.add_succ_r.
    rewrite <- N_of_nat_succ. rewrite N.add_succ_r.
    rewrite <- N.pred_sub; rewrite N.pred_succ.
    rewrite <- pred_of_minus. replace (pred (S (m + n)))%nat with (m + n)%nat; auto.
    induction m. simpl; rewrite nat_of_N_bij1; auto.
    rewrite NPeano.Nat.add_succ_l.
    rewrite <- N_of_nat_succ; rewrite N.add_succ_l.
    assert (forall (n:N), S (N.to_nat n) = N.to_nat (N.succ n)); auto.
      intros. induction n0; auto.
      simpl. 
      replace (Pos.to_nat p) with (Pos.iter_op plus p 1%nat); auto.
      replace (Pos.to_nat (Pos.succ p)) with (Pos.iter_op plus (Pos.succ p) 1%nat); auto.
      induction p; auto.
      rewrite Pos.iter_op_succ. rewrite NPeano.Nat.add_succ_l. 
      assert (forall (m n:nat), m = n -> S m = S n); auto.
      intros; rewrite plus_assoc; auto.
    rewrite <- H. auto.
Qed.

Lemma le_Nle : forall (m n : nat), (m <= n)%nat -> (N.of_nat m <= N.of_nat n)%N.
Proof.
  intro m. induction m; intros. simpl. apply N.le_0_l.
  inversion H. unfold N.of_nat. destruct (m); apply N.le_refl.
  subst. repeat (rewrite <- N_of_nat_succ). apply -> N.succ_le_mono. 
  apply IHm; auto. apply le_S_n in H; auto.
Qed.

Lemma N_nat_distr_plus : forall (m n:nat), N.of_nat (m + n)%nat = 
    (N.of_nat m + N.of_nat n)%N.
Proof.
   intros.
   generalize dependent n; induction m; auto.
   intros. 
   rewrite NPeano.Nat.add_succ_l.
   rewrite <- N_of_nat_succ. rewrite <- N_of_nat_succ; rewrite N.add_succ_l.
   assert (forall (m n:N), m = n -> N.succ m = N.succ n); auto.
   clear.
   intro m; induction m. destruct n; auto. 
   intros. rewrite H; auto.
   intro n; induction n. intros. rewrite H; auto.
   generalize dependent p0; induction p; 
   destruct p0; intros; try (auto; rewrite H; auto).
Qed.

Lemma N_nat_distr_minus : forall (m n:nat), (n <= m)%nat -> 
    N.of_nat (m - n)%nat = (N.of_nat m - N.of_nat n)%N.
Proof.
   intros.
   generalize dependent n; induction m; auto.
   intros. inversion H; auto.
   rewrite minus_diag. repeat (rewrite <- N_of_nat_succ).
   rewrite N.sub_succ_r. rewrite N.sub_succ_l. rewrite N.pred_succ; auto.
   rewrite <- IHm; auto. rewrite minus_diag; auto. 
   destruct m; unfold N_toVar; unfold N.of_nat; apply N.le_refl.
   (* case when n <= m *)
   subst.
   rewrite NPeano.Nat.sub_succ_l; auto.
   repeat (rewrite <- N_of_nat_succ). 
   rewrite N.sub_succ_l; auto. 
   assert (forall (m n:N), m = n -> N.succ m = N.succ n); auto.
   clear.
   intro m; induction m. destruct n; auto. 
   intros. rewrite H; auto.
   intro n; induction n. intros. rewrite H; auto.
   generalize dependent p0; induction p; 
   destruct p0; intros; try (auto; rewrite H; auto).
   apply le_Nle; auto.
Qed.

Lemma N_nat_distr : forall (m n:nat), N.of_nat (m + n - 1)%nat = 
    (N.of_nat m + N.of_nat n - 1)%N.
Proof.
   intros. destruct n.
   rewrite plus_0_r. rewrite N.add_0_r.
   destruct m; auto. 
   rewrite <- N_of_nat_succ.
   rewrite <- N.pred_sub; rewrite N.pred_succ.
   rewrite <- pred_of_minus. replace (pred (S m))%nat with (m)%nat; auto.
   rewrite NPeano.Nat.add_succ_r. 
   rewrite <- N_of_nat_succ; rewrite N.add_succ_r.
   rewrite <- N.pred_sub; rewrite N.pred_succ.
   rewrite <- pred_of_minus. replace (pred (S (m + n)))%nat with (m + n)%nat; auto.
   apply N_nat_distr_plus.
Qed.

Lemma silly_1 : forall l n maxLocals lvt, (n < length l)%nat -> 
  nth_error l n = BinNatMap.get _ (translate_st_rt l maxLocals lvt) 
    (N_of_nat (length l - n + maxLocals - 1)).
Proof. intro l. unfold translate_st_rt. 
  induction l; intros. 
  (* Base case where the list is empty *)
  inversion H. 
  (* Induction case where the list is of the form a :: l *)
  subst. replace (translate_st_rt_rec (a :: l) maxLocals (base_rt maxLocals lvt)) 
  with 
  (BinNatMap.update _ (translate_st_rt_rec (l) maxLocals (base_rt maxLocals lvt)) 
    (N_toVar (length (a::l)) + N_toVar maxLocals - 1)%N a); auto.
  (*apply le_S_gt in H1.*)
  destruct n.
    (* n = 0 *)
    rewrite <- minus_n_O. 
    unfold BinNatMap.update. rewrite N_nat_distr. 
    rewrite BinNatMap.get_modify1; auto.
    (* n = S n *)
    replace (nth_error (a :: l) (S n)) with (nth_error (l) (n)); auto.
    assert (forall n m, N.of_nat n = N.of_nat m -> n = m); auto.
      intro n0. induction n0. destruct m; auto. intros. inversion H0. 
      destruct m; intros. inversion H0.  
      rewrite <- N_of_nat_succ in H0. rewrite <- N_of_nat_succ in H0.
      apply N.succ_inj in H0.
      apply eq_S. apply IHn0; auto. 
    replace (N.of_nat (length (a :: l) - S n + maxLocals - 1))%nat with
      (N.of_nat (length l - n + maxLocals - 1)%nat).
    unfold BinNatMap.update; rewrite BinNatMap.get_modify2; auto.
    apply IHl; auto.
    rewrite cons_length in H; simpl in H. apply lt_S_n in H; auto.
    unfold not. intros.
    rewrite cons_length in H1. replace (1 + length l)%nat with (S (length l)) in H1; auto. 
    rewrite <- N_nat_distr in H1. rewrite NPeano.Nat.add_succ_l in H1.
    replace (pred (S (length l + maxLocals)))%nat with (length l + maxLocals)%nat in H1; auto.
    simpl in H1; rewrite <- minus_n_O in H1. 
    
    apply H0 in H1. 
    assert (forall (m n p:nat), (n < m)%nat -> (m - n + p - 1 = m + p)%nat -> False). 
    intro m; induction m. intros n0 p H3.
    inversion H3. 
    intros. inversion H2. 
    (* n0 = m *)
    subst. 
    rewrite <- minus_Sn_m in H3; auto.
    rewrite minus_diag in H3. simpl in H3. rewrite <- minus_n_O in H3. 
    rewrite <- NPeano.Nat.add_succ_l in H3. rewrite plus_comm in H3.
    apply plus_minus in H3. rewrite minus_diag in H3. inversion H3.
    (* n0 < m *)
    subst. (*apply le_S_gt in H5.*)
    rewrite <- minus_Sn_m in H3. 
    repeat (rewrite NPeano.Nat.add_succ_l in H3).
    rewrite <- minus_Sn_m in H3. 
    assert (forall n m, S n = S m -> n = m); auto. apply H4 in H3.
    generalize H3. apply IHm; auto. omega. omega. 
    apply H2 in H1; auto. rewrite cons_length in H. simpl in H. apply lt_S_n in H; auto.
    
    assert (forall n m, n = m -> N.of_nat n = N.of_nat m); auto.
Qed.

Lemma tsub_st_incl : forall a b l1 l2, tsub_st (a::l1) (b::l2) = true ->
  tsub_st l1 l2 = true.
Proof.
  intros. replace (tsub_st (a::l1) (b::l2)) with (leql'_test a b && tsub_st l1 l2) in H.
  apply andb_true_iff in H. inversion H. auto.
  auto.
Qed.

Lemma tsub_st_eq_length : forall l1 l2, tsub_st l1 l2 = true ->
  length l1 = length l2.
Proof.
  intros l1; induction l1; intros; destruct l2. 
  auto. inversion H. inversion H.
  assert (length (a::l1) = (1 + length l1)%nat); auto.
  assert (length (t::l2) = (1 + length l2)%nat); auto.
  simpl. assert (forall m n, m = n -> S m = S n). auto.
  apply H2. apply IHl1. apply tsub_st_incl with (a:=a) (b:=t).
  auto.
Qed. 

Lemma silly_2 : forall l1 l2, tsub_st l1 l2 = true -> 
  forall n, (n < length l1)%nat -> (n < length l2)%nat -> 
    forall k1 k2, nth_error l1 (length l1 - n - 1) = Some k1 -> 
      nth_error l2 (length l2 - n - 1) = Some k2 -> 
      leql'_test k1 k2 = true.
Proof.
  intro l1. induction l1; auto. intros; inversion H2.
  intros. destruct l2. inversion H3.
  inversion H0. rewrite H5 in H2. 
  inversion H1. rewrite H6 in H3.  
  (* case when length l1 = length l2 = n *)
  rewrite cons_length in H2.
  rewrite <- NPeano.Nat.add_sub_assoc in H2; auto. rewrite minus_diag in H2; simpl in H2.
  rewrite cons_length in H3.
  rewrite <- NPeano.Nat.add_sub_assoc in H3; auto. rewrite minus_diag in H3; simpl in H3.
  replace (tsub_st (a::l1) (t::l2)) with (leql'_test a t && tsub_st l1 l2) in H; auto.
  apply andb_true_iff in H; inversion H; inversion H2; inversion H3; subst; auto. 
  
  (* case when length l1 <> length l2 *)
  subst. apply tsub_st_eq_length in H. 
  assert (length (a::l1) = (1 + length l1)%nat); auto.
  assert (length (t::l2) = (1 + length l2)%nat); auto.
  rewrite H4 in H. rewrite H5 in H. simpl in H.
  assert (forall m n, S m = S n -> m = n). auto. 
  apply H7 in H. apply le_S_gt in H6. 
  rewrite H in H6. apply gt_irrefl in H6. inversion H6. 

  (* case when n < length l1,  n = length l2 *)
  inversion H1. rewrite H7 in H3.
  subst. apply tsub_st_eq_length in H. 
  assert (length (a::l1) = (1 + length l1)%nat); auto.
  assert (length (t::l2) = (1 + length l2)%nat); auto.
  rewrite H4 in H. rewrite H6 in H. simpl in H.
  assert (forall m n, S m = S n -> m = n). auto. 
  apply H7 in H. apply le_S_gt in H5. 
  rewrite H in H5. apply gt_irrefl in H5. inversion H5. 

  (* case when n < length l1, n < length l2 *)
  subst.
  replace (nth_error (a :: l1) (length (a :: l1) - n - 1))
  with (nth_error (l1) (length l1 - n - 1)) in H2. 
  replace (nth_error (t :: l2) (length (t :: l2) - n - 1))
  with (nth_error (l2) (length l2 - n - 1)) in H3.
  apply IHl1 with (l2 := l2) (n := n); auto.
  apply tsub_st_incl with (a:=a) (b:=t); auto.

  apply le_S_gt in H5; rewrite cons_length. 
  replace (1 + length l2 - n - 1)%nat with (S (length l2 - n - 1)%nat); auto.
  omega.
  apply le_S_gt in H7; rewrite cons_length. 
  replace (1 + length l1 - n - 1)%nat with (S (length l1 - n - 1)%nat); auto.
  omega.
Qed.

Lemma silly_3 : forall l (i:N) maxLocals lvt, 
  ((nat_of_N i) < maxLocals)%nat ->
  BinNatMap.get _ (translate_st_rt l maxLocals lvt) i = 
  BinNatMap.get _ (base_rt (maxLocals) (lvt)) i.
Proof. unfold translate_st_rt.
  intro l; induction l. 
  auto. intros. 
  replace (translate_st_rt_rec (a :: l) maxLocals (base_rt maxLocals lvt)) 
  with 
  (BinNatMap.update _ (translate_st_rt_rec (l) maxLocals (base_rt maxLocals lvt)) 
    (N_toVar (length (a::l)) + N_toVar maxLocals - 1)%N a); auto.
  unfold BinNatMap.update. rewrite BinNatMap.get_modify2. auto.
  rewrite cons_length. replace (1+length l)%nat with (S (length l)); auto.
  rewrite N.add_comm. 
  unfold not. intros. rewrite H0 in H.
  replace (N.to_nat (N_toVar maxLocals + N_toVar (S (length l)) - 1))
  with (maxLocals + S (length l) - 1)%nat in H; auto.
  rewrite plus_comm in H. rewrite NPeano.Nat.add_succ_l in H.
  simpl in H. rewrite <- minus_n_O in H. 
  apply NPeano.Nat.lt_add_lt_sub_r in H; auto.
  rewrite minus_diag in H. inversion H.
  clear. auto. 
  assert (forall (m n:nat), (m + S n - 1)%nat = 
    N.to_nat (N_toVar m + N_toVar (S n) - 1)); auto.
    (* Proving assertion *)
    assert (forall m, N.succ (N_toVar m) = N_toVar (S m)).
      intros; induction m; auto.
    intros.
    rewrite <- H.
    rewrite N.add_comm. rewrite N.add_succ_l.
    rewrite <- N.pred_sub; rewrite N.pred_succ.
    rewrite plus_comm. rewrite NPeano.Nat.add_succ_l.
    rewrite <- pred_of_minus. rewrite <- pred_Sn.
    induction n. rewrite plus_0_l; rewrite N.add_0_l; rewrite nat_of_N_bij1; auto.
    rewrite NPeano.Nat.add_succ_l.
    rewrite <- H. rewrite N.add_succ_l.
    replace (N.to_nat (N.succ (N_toVar n + N_toVar m))) with 
      (S (N.to_nat (N_toVar n + N_toVar m))); auto.
    assert (forall (n:N), S (N.to_nat n) = N.to_nat (N.succ n)); auto.
      intros. induction n0; auto.
      simpl. 
      replace (Pos.to_nat p) with (Pos.iter_op plus p 1%nat); auto.
      replace (Pos.to_nat (Pos.succ p)) with (Pos.iter_op plus (Pos.succ p) 1%nat); auto.
      induction p; auto.
      rewrite Pos.iter_op_succ. rewrite NPeano.Nat.add_succ_l. 
      assert (forall (m n:nat), m = n -> S m = S n); auto.
      intros; rewrite plus_assoc; auto.
   Qed.
(*
Lemma reg_le_dec : forall (reg:N) (maxLocals:nat), 
  {((nat_of_N reg) < maxLocals)%nat} + {((nat_of_N reg) >= maxLocals)%nat}
  (*+ {((nat_of_N reg) = maxLocals)%nat}*).
Proof.
  intros reg. induction (nat_of_N reg). intro maxLocals. induction maxLocals. 
  auto. left. apply lt_0_Sn. intro maxLocals. induction maxLocals. 
  right. apply ltgtge_Sn_O. destruct IHn with (maxLocals:= maxLocals).
  left. apply le_n_S. apply l.
  right. apply gt_n_S. apply g.
Qed.
*)

Lemma le_minus_minus : forall (m n:nat), (n <= m)%nat ->
  (m - (m - n))%nat = n.
Proof.
  intro m. induction m. intros; inversion H; auto.
  intros. inversion H.  rewrite minus_diag. auto.
  subst. rewrite NPeano.Nat.sub_succ_l with (n:=n) (m:=m).
  simpl. apply IHm; auto. auto.
Qed.

Lemma le_minus' : forall (m n p:nat), (m <= p)%nat -> ((m - n) <= p)%nat.
Proof.
  intros m n p; generalize dependent m; generalize dependent n; induction p.
  intros; inversion H; auto. 
  intros. inversion H. apply le_minus. subst.
  apply le_S. apply IHp. auto.
Qed.

Lemma minus_distr : forall (m n p:nat), (n <= m)%nat ->
  (p <= n)%nat -> 
  (m - (n - p))%nat = (m - n + p)%nat.
Proof.
  intro m; induction m. (*; intro n; induction n; intro p; induction p.*)
  intros. inversion H. subst. inversion H0. auto.
  intros. destruct (eq_nat_dec) with (n:=n) (m:=S m).
  (* case where a = b *)
  subst. rewrite le_minus_minus; auto. rewrite minus_diag. auto.
  inversion H; try (contradiction; fail). subst.
  rewrite NPeano.Nat.sub_succ_l with (m:=m) (n:=n); auto.
  rewrite NPeano.Nat.add_succ_l.
  rewrite NPeano.Nat.sub_succ_l; auto.
  apply le_minus'. auto.
Qed.
  
Lemma lt_plus_r_lt_minus_l : forall m n p, (p <= m)%nat ->
    (m < n + p)%nat -> (m - p < n)%nat.
  Proof.
    intro m; induction m; intro n; induction n; intro p; induction p.
    auto.
    intros. inversion H. 
    intros. apply lt_0_Sn.
    intros. inversion H.
    intros. inversion H0.
    intros. simpl. apply IHm. apply le_S_n. auto. simpl. simpl in H0.
    apply lt_S_n. auto. 
    intros. simpl. rewrite plus_0_r in H0. auto.
    intros. simpl. apply IHm. apply le_S_n. auto.
    rewrite <- plus_n_Sm in H0. apply lt_S_n in H0. auto.
  Qed.

Lemma lt_minus_l_lt_plus_r : forall m n p, (p <= m)%nat ->
    (m -p < n)%nat -> (m < n + p)%nat.
  Proof.
    intro m; induction m; intro n; induction n; intro p; induction p.
    auto.
    intros. inversion H. 
    intros. apply lt_0_Sn.
    intros. inversion H.
    intros. inversion H0.
    intros. inversion H0. 
    intros. rewrite plus_0_r. simpl in H0. auto.
    intros. simpl. apply lt_n_S. 
    inversion H. omega. subst.
    apply IHm; auto.
    rewrite <- minus_Sn_m in H0; auto. apply lt_S_n in H0. auto. 
  Qed.

Lemma lt_plus_l_lt_minus_r : forall m n p, (p <= n)%nat ->
    (m + p < n)%nat -> (m < n - p)%nat.
  Proof.
    intros m; induction m. (*intro n; induction n; intro p; induction p.*)
    intros. inversion H. 
    simpl. subst. simpl. simpl in H0. apply lt_irrefl in H0. inversion H0.
    subst. simpl in H0. rewrite <- minus_Sn_m; auto. apply lt_O_Sn. 
    intros.
    inversion H. subst. 
    Lemma lt_irrefl' : forall m n, ~(m + n < m)%nat.
    Proof.
      intro m. induction m. unfold not. intros. simpl in H. inversion H.
      unfold not. intros. simpl in H. apply lt_S_n in H. apply IHm in H. inversion H.
    Qed. 
    rewrite plus_comm in H0. apply lt_irrefl' in H0. inversion H0.
    subst. 
    rewrite <- minus_Sn_m; auto. apply lt_n_S. apply IHm; auto.
    simpl in H0. apply lt_S_n in H0. auto.
Qed. 

Lemma silly_4 : forall l1 l2 maxLocals lvt, 
  tsub_st l1 l2 = true -> 
  (forall (i:N) k1 k2, 
    ((nat_of_N i) < ((length l1) + maxLocals))%nat -> 
    ((nat_of_N i) < ((length l2) + maxLocals))%nat -> 
    BinNatMap.get _ (translate_st_rt l1 maxLocals lvt) i = Some k1 ->
    BinNatMap.get _ (translate_st_rt l2 maxLocals lvt) i = Some k2 ->
    leql'_test k1 k2 = true).
Proof.
  intros. destruct le_lt_dec with (m:=(nat_of_N i)) (n:=maxLocals). 
  (* Case when i >= maxLocals *)
  apply silly_2 with (l1:=l1) (l2:=l2) (n:=((nat_of_N i) - maxLocals)%nat).
  auto. 
  apply lt_plus_r_lt_minus_l; auto.
  apply lt_plus_r_lt_minus_l; auto.
  (* l1@f(i) = map (l1)@i *)
  rewrite silly_1 with (maxLocals:=maxLocals) (lvt:=lvt). rewrite <- H2. 
  (*replace (N.of_nat (N.to_nat i - maxLocals + maxLocals)) with (i). auto.*)
  replace (N.of_nat (length l1 - (length l1 - (N.to_nat i - maxLocals) - 1) + maxLocals - 1)) with (i). auto.
  rewrite minus_distr; auto. rewrite minus_distr; auto.
  rewrite minus_diag. simpl. rewrite plus_comm. 
  rewrite plus_comm with (n:=(N.to_nat i - maxLocals)%nat) (m := (1)%nat). 
  simpl. rewrite <- plus_n_Sm. simpl. rewrite <- minus_n_O.
  
  (* *) 
  rewrite <- le_plus_minus; auto. rewrite nat_of_N_bij2; auto.
  (* *)  

  (* *)
  inversion l. rewrite minus_diag. apply le_O_n.
  apply lt_plus_r_lt_minus_l in H0; auto.
  rewrite <- H4 in H0. omega.
  (* *)

  subst.
  apply le_minus. 
  apply lt_le_S.
  apply lt_plus_l_lt_minus_r; auto. 
  apply NPeano.Nat.lt_le_incl; auto.
  apply lt_plus_r_lt_minus_l; auto. 
  simpl. apply lt_plus_r_lt_minus_l; auto.
  apply lt_plus_r_lt_minus_l; auto.
  apply lt_le_S.
  apply lt_plus_l_lt_minus_r; auto. 
  apply NPeano.Nat.lt_le_incl; auto.
  apply lt_plus_r_lt_minus_l; auto. simpl. 
  apply lt_plus_r_lt_minus_l; auto.
  inversion l. rewrite minus_diag. rewrite <- minus_n_O.
  replace (length l1 + 1)%nat with (S (length l1)); auto. 
  rewrite NPeano.Nat.add_1_r; auto.
  subst.
  apply lt_trans with (p:=(length l1 + 1)%nat) (m:=length l1); auto.
  apply lt_minus.
  rewrite H4. apply NPeano.Nat.lt_le_incl. apply lt_plus_r_lt_minus_l; auto.
  apply lt_plus_l_lt_minus_r; auto. simpl.
  apply le_lt_n_Sm; auto. 
  replace (length l1 + 1)%nat with (S (length l1)); auto. 
  rewrite NPeano.Nat.add_1_r; auto.
  (* l2@f(i) = map (l2)@i *)
  rewrite silly_1 with (maxLocals:=maxLocals) (lvt:=lvt).  rewrite <- H3. 
  replace (N.of_nat (length l2 - (length l2 - (N.to_nat i - maxLocals) - 1) + maxLocals - 1)) with (i); auto.
  rewrite minus_distr; auto. rewrite minus_distr; auto.
  rewrite minus_diag. simpl. rewrite plus_comm. 
  rewrite plus_comm with (n:=(N.to_nat i - maxLocals)%nat) (m := (1)%nat). 
  simpl. rewrite <- plus_n_Sm. simpl. rewrite <- minus_n_O.
  rewrite <- le_plus_minus. symmetry. apply nat_of_N_bij2. auto.
  (* *)
  inversion l. rewrite minus_diag. apply le_O_n.
  apply lt_plus_r_lt_minus_l in H0; auto.
  rewrite <- H4 in H0. omega.
  (* *)
  apply le_minus. 
  apply lt_le_S.
  apply lt_plus_l_lt_minus_r; auto. 
  apply NPeano.Nat.lt_le_incl; auto.
  apply lt_plus_r_lt_minus_l; auto. 
  simpl. apply lt_plus_r_lt_minus_l; auto.
  apply lt_plus_r_lt_minus_l; auto.
  apply lt_le_S.
  apply lt_plus_l_lt_minus_r; auto. 
  apply NPeano.Nat.lt_le_incl; auto.
  apply lt_plus_r_lt_minus_l; auto. simpl. 
  apply lt_plus_r_lt_minus_l; auto.
  inversion l. rewrite minus_diag. rewrite <- minus_n_O.
  replace (length l2 + 1)%nat with (S (length l2)); auto. 
  rewrite NPeano.Nat.add_1_r; auto.
  subst.
  apply lt_trans with (p:=(length l2 + 1)%nat) (m:=length l2); auto.
  apply lt_minus.
  rewrite H4. apply NPeano.Nat.lt_le_incl. apply lt_plus_r_lt_minus_l; auto.
  apply lt_plus_l_lt_minus_r; auto. simpl.
  apply le_lt_n_Sm; auto. 
  replace (length l2 + 1)%nat with (S (length l2)); auto. 
  rewrite NPeano.Nat.add_1_r; auto.
  (* Case when i < maxLocals *)
  rewrite silly_3 in H2; auto. rewrite silly_3 in H3; auto. 
  rewrite H2 in H3. inversion H3. destruct k2. destruct k; auto.
  unfold leql'_test. apply andb_true_intro; split. destruct k; auto.
  assert (eql'_test k2 k2 = true). clear H3. clear H5.
  induction k2. unfold eql'_test. destruct k0; auto.
  unfold eql'_test.
  apply andb_true_intro; split; auto. destruct k0; auto. auto.
Qed.
(*
Lemma silly_5 : forall m a (v:L.t'), ~ In a (BinNatMap.dom _ m) ->
  (1 + length (BinNatMap.dom _ m))%nat = 
  length (BinNatMap.dom _ (BinNatMap.update _ m a v)).
Proof.
  intros. unfold BinNatMap.dom.
  repeat (rewrite <- BinNatMap_Base.fold_prop).

Lemma RT_length : forall l maxLocals lvt,
  (length (BinNatMap.dom L.t' (translate_st_rt l maxLocals lvt))) = (length l + maxLocals)%nat.
Proof.
  intro l; induction l.
  (* base case where l = nil *) 
  simpl. intros.
  replace (translate_st_rt nil maxLocals lvt) with (base_rt maxLocals lvt); auto. 
  generalize dependent lvt.
  induction maxLocals; auto.
  intros.
  replace (length (BinNatMap.dom L.t' (base_rt (S maxLocals) lvt)))
    with (1 + length (BinNatMap.dom L.t' (base_rt maxLocals lvt)) )%nat; auto.
  unfold base_rt.
  replace (base_rt_rec (S maxLocals) lvt (VarMap.empty L.t')) with
    (VarMap.update _ (base_rt_rec maxLocals lvt (VarMap.empty L.t')) 
    (N_toVar (maxLocals)) (lvt (N_toVar (maxLocals)))); auto. 
  unfold BinNatMap.dom. unfold BinNatMap_Base.fold.
  (* induction case where l = a :: l *)
  intros. 
  replace (translate_st_rt nil (S maxLocals) lvt) with (base_rt (S maxLocals) lvt); auto.
  simpl.
  auto.*)

Lemma tsub_st_implies_tsub_rt : forall (*Si Sj *) S i (j:JVM_PC) maxLocals lvt,
  (*S i = Si -> S j = Sj -> *)
  tsub_st (S i) (S j) = true -> 
  tsub_rt (translate_st_rt (S i) maxLocals lvt) 
    (translate_st_rt (S j) maxLocals lvt) = true.
Proof.
  intros.
  assert (forall (i0:N) k1 k2, 
    ((nat_of_N i0) < ((length (S i)) + maxLocals))%nat -> 
    ((nat_of_N i0) < ((length (S j)) + maxLocals))%nat -> 
    BinNatMap.get _ (translate_st_rt (S i) maxLocals lvt) i0 = Some k1 ->
    BinNatMap.get _ (translate_st_rt (S j) maxLocals lvt) i0 = Some k2 ->
    leql'_test k1 k2 = true). 
  apply silly_4 with (l1:=S i) (l2:=S j) (maxLocals:=maxLocals) (lvt:=lvt); auto.
(*
/\ (a < length (Si) + maxLocals)%nat
      /\ (a < length (Sj) + maxLocals)%nat)
*)
(*
  Lemma N2nat_0_N0 : forall n, (N.to_nat n = 0)%nat -> n = N0.
  Proof. intros. replace (0%nat) with (N.to_nat N0) in H; auto. 
    apply Nnat.N2Nat.inj in H. auto. Qed.

  Lemma N2nat_neq_0 : forall n, N.to_nat n <> 0%nat -> n <> N0.
  Proof. unfold not. intros. 
    assert (forall n, n = N0 -> (N.to_nat n = 0)%nat); auto.
    intros. replace (0%nat) with (N.to_nat N0); auto. 
    apply Nnat.N2Nat.inj_iff; auto.
  Qed.
*)
  Lemma dom_inv1 : forall m a k (v:L.t'), (a <> k) ->
    In (k) (BinNatMap.dom _ (BinNatMap.update _ m a v)) -> 
    In (k) (BinNatMap.dom _ m).
  Proof.
    intros. 
    apply BinNatMap.get_some_in_dom.
    apply BinNatMap.in_dom_get_some in H0.
    unfold BinNatMap.update in H0.
    rewrite BinNatMap.get_modify2 in H0. auto. auto.
  Qed.
  
  Lemma dom_inv2 : forall m a k (v:L.t'), (a = k) ->
    In (k) (BinNatMap.dom _ (BinNatMap.update _ m a v)).
  Proof.
    intros. rewrite H; clear H.
    apply BinNatMap.get_some_in_dom.
    unfold BinNatMap.update; rewrite BinNatMap.get_modify1. unfold not; intros; inversion H.
  Qed.

  Lemma silly_sub_2 : forall (Si:TypeStack) a maxLocals lvt, In (N.of_nat a) 
    (BinNatMap.dom _ (translate_st_rt Si maxLocals lvt)) -> 
    (a < length Si + maxLocals)%nat.
  Proof.
    unfold translate_st_rt.
    intro Si; induction Si; auto.
    (* base case *)
    simpl.
    intros a maxLocals; generalize dependent a; induction maxLocals; intros; simpl in H.
    inversion H. 
    destruct eq_nat_dec with (a) (maxLocals). 
    rewrite e; auto. apply lt_S.
    apply IHmaxLocals with (lvt:=lvt). 
    unfold base_rt; unfold base_rt in H.
    replace (base_rt_rec (S maxLocals) lvt (VarMap.empty L.t')) with 
     (VarMap.update _ (base_rt_rec maxLocals lvt (VarMap.empty L.t'))
      (N_toVar maxLocals) (lvt (N_toVar maxLocals))) in H; auto.
    apply dom_inv1 in H. auto. unfold not in n; unfold not.
    intros; apply n; apply Nnat.Nat2N.inj; auto.
    
    (* induction case *)
    intros.
    replace (translate_st_rt_rec (a :: Si) maxLocals (base_rt maxLocals lvt)) with
      (VarMap.update _ (translate_st_rt_rec Si maxLocals (base_rt maxLocals lvt)) 
       (N_toVar (length (a::Si)) + N_toVar maxLocals - 1)%N a) in H; auto.
    (* Case when a0 = length (a::Si) + maxLocals - 1 *)
    destruct eq_nat_dec with (n:=a0) (m:=(length (a::Si) + maxLocals - 1)%nat). 
    rewrite e. apply lt_plus_r_lt_minus_l. 
    rewrite cons_length. rewrite NPeano.Nat.add_succ_l.
    apply le_n_S; apply le_0_n. 
    rewrite NPeano.Nat.add_succ_r; rewrite plus_0_r; omega. 
    
    (* Case when a0 <> length (a::Si) + maxLocals -1 *)
    apply dom_inv1 in H; auto.
    rewrite cons_length. rewrite NPeano.Nat.add_succ_l.
    apply lt_S. apply IHSi with (lvt:=lvt); auto.
    auto. 
    rewrite <- N_nat_distr_plus.
    replace (1%N) with (N.of_nat (1)%nat); auto.
    rewrite <- Nnat.Nat2N.inj_sub.
    unfold not. intros.
    apply Nnat.Nat2N.inj in H0. unfold not in n. apply n. symmetry; apply H0.
  Qed.    

  Lemma silly_sub_1 : forall l Si Sj maxLocals lvt, 
    (forall a, In (N.of_nat a) l ->
      tsub_element (translate_st_rt (Si) maxLocals lvt) 
      (translate_st_rt (Sj) maxLocals lvt) (N.of_nat a) = true) -> 
    tsub_rec (translate_st_rt (Si) maxLocals lvt)
       (translate_st_rt (Sj) maxLocals lvt) (l) = true.
  Proof.
    intro l. induction l; auto.
    intros.
    set (rt1 := translate_st_rt Si maxLocals lvt).
    set (rt2 := translate_st_rt Sj maxLocals lvt). 
    replace (tsub_rec rt1 rt2 (a :: l) = true)
      with (tsub_element rt1 rt2 (a) && tsub_rec rt1 rt2 (l) = true); auto.
      apply andb_true_intro; split.
      rewrite <- nat_of_N_bij2 with (n:=a). apply H with (a0:=(N.to_nat a)). 
      rewrite nat_of_N_bij2. apply in_eq.
      apply IHl; auto.
      intros. apply H; auto.
      (*inversion H0. split; auto.*)
      apply in_cons; auto.
  Qed.

  Lemma silly_sub_3 : forall Si Sj, tsub_st Si Sj = true -> 
    (length Si = length Sj)%nat.
  Proof. 
    intro Si; induction Si; intros. 
    destruct Sj; inversion H. simpl. auto.
    destruct Sj; inversion H. repeat (rewrite cons_length).
    simpl. assert (forall m n, m = n -> S m = S n); auto.
    apply H0. apply IHSi. 
    apply tsub_st_incl in H; auto.
  Qed.  

  Lemma silly_sub_4 : forall Si Sj a maxLocals lvt, In (N.of_nat a) 
    (BinNatMap.dom _ (translate_st_rt Sj maxLocals lvt)) -> 
    tsub_st Si Sj = true ->
    (a < length Si + maxLocals)%nat.
  Proof.
    intros. (*split.*) apply silly_sub_2 in H.
    rewrite silly_sub_3 with (Sj := Sj); auto.
    (*apply silly_sub_2 with (lvt:=lvt); auto.*)
  Qed.
    
  unfold tsub_rt.
  set (rt1 := translate_st_rt (S i) maxLocals lvt).
  set (rt2 := translate_st_rt (S j) maxLocals lvt).
  apply silly_sub_1.
  intros.  
  (*inversion H1; clear H1. inversion H3; clear H3. *)
  unfold tsub_element. 
  destruct (BinNatMap.get L.t' (translate_st_rt (S i) maxLocals lvt) (N.of_nat a)) eqn:Hk1;
  destruct (BinNatMap.get L.t' (translate_st_rt (S j) maxLocals lvt) (N.of_nat a)) eqn:Hk2; auto.
  apply H0 with (i0:=N.of_nat a); try (rewrite nat_of_N_bij1); try (apply silly_sub_4); auto.
  apply silly_sub_4 with (Sj := S j) (lvt:=lvt); auto.
  apply silly_sub_2 with (lvt:=lvt); auto. 
  
  Lemma silly_sub_5 : forall l1 l2 a maxLocals lvt, length l1 = length l2 ->
    In a (BinNatMap.dom L.t' (translate_st_rt l2 maxLocals lvt)) -> 
      In a (BinNatMap.dom L.t' (translate_st_rt l1 maxLocals lvt)).
  Proof.
    intro l1; induction l1.
    destruct l2. auto.  
    intros; inversion H. destruct l2. intros; inversion H.
    intros.
    repeat (rewrite cons_length in H). simpl in H. 
    assert (forall x y, S x = S y -> x = y); auto.
    apply H1 in H; clear H1.
    replace (translate_st_rt (a::l1) maxLocals lvt) with
      (VarMap.update _ (translate_st_rt l1 maxLocals lvt) 
       (N_toVar (length (a::l1)) + N_toVar maxLocals - 1)%N a); auto.

    destruct N.eq_dec with (n:=a0) (m:=(N_toVar (1 + length l1)%nat + N_toVar maxLocals - 1)%N); auto.
    Lemma in_dom_eq : forall A a (v:A) m, In a (BinNatMap.dom _ (BinNatMap.update _ m a v)).
    Proof.
      intros.
      apply BinNatMap.get_some_in_dom.
      rewrite BinNatMap.get_update1.
      unfold not. intros. inversion H.
    Qed.
    rewrite e. apply in_dom_eq. 
    apply BinNatMap.get_some_in_dom. 
    rewrite BinNatMap.get_update2; auto. 
    apply BinNatMap.in_dom_get_some.
    apply IHl1 with (l2:=l2); auto.
    apply BinNatMap.in_dom_get_some in H0. 
    replace (translate_st_rt (t::l2) maxLocals lvt) with
      (VarMap.update _ (translate_st_rt l2 maxLocals lvt) 
       (N_toVar (length (t::l2)) + N_toVar maxLocals - 1)%N t) in H0; auto.
    rewrite BinNatMap.get_update2 in H0; auto. 
    apply BinNatMap.get_some_in_dom in H0.
    auto. 
    rewrite cons_length. rewrite <- H; auto.
  Qed.
  apply silly_sub_5 with (l1:=(S i)) (l2:=(S j)) in H1 .
  apply BinNatMap.in_dom_get_some in H1. unfold not in H1. apply H1 in Hk1.
  inversion Hk1.
  apply silly_sub_3; auto.
Qed.

Fixpoint create_insnList_rec (bm:JVM_BytecodeMethod) 
 (ls:list (JVM_PC*(JVM_Instruction*(option JVM_PC*list JVM_ClassName))))
 (l:list (JVM_PC*(option JVM_PC*JVM_Instruction))) 
 : list (JVM_PC*(option JVM_PC*JVM_Instruction)) :=
   match ls with
     | nil => l
     | (pc, (ins,(pc',_))) :: ts => create_insnList_rec (bm) (ts) ((pc,(pc',ins))::l)
   end.

Definition create_insnList (bm:JVM_BytecodeMethod) : list (JVM_PC * (option JVM_PC*JVM_Instruction)) :=
  let pc := JVM_BYTECODEMETHOD.firstAddress bm in
      create_insnList_rec (bm) 
  (MapPC.elements _ (JVM_BYTECODEMETHOD.instr bm)) (nil)
.

Definition translate_se (jvm_se:JVM_PC -> L.t) (translate_pc':(N*N)->JVM_PC) 
  : (N*N) -> L.t :=
  fun address => jvm_se (translate_pc' address).

Definition pc_jvm_int : (MapN.t (list (N*N))) -> JVM_PC -> list (N*N) :=
  (fun map source => match MapN.get _ map source with
                | None => nil
                | Some v => v
              end).

Definition create_int_jvm_map (map:MapN.t (list (N*N))) : MapAddress.t JVM_PC :=
  MapN.fold _ _ 
    (fun key l m => fold_left 
       (fun m' address => MapAddress.update _ m' address key) l m) 
    map (MapAddress.empty JVM_PC).

Definition pc_int_jvm : (MapAddress.t JVM_PC) -> (N*N) -> JVM_PC :=
  (fun map source => match MapAddress.get _ map source with
                | None => (0)%N
                | Some v => v
              end).

Definition static_sign (source:JVM_sign) : DEX_sign :=
  make_DEX_sign (source.(JVM_lvt)) (source.(JVM_resType)) (source.(JVM_heapEffect)).

Definition virtual_sign (source:L.t -> JVM_sign) : L.t -> DEX_sign :=
  (fun k =>
    make_DEX_sign (fun reg => L.Simple L.Low) (Some (L.Simple L.Low)) (L.Low)
  ).

Fixpoint create_locR (max_locals:nat) : list DEX_Reg :=
  match max_locals with
    | O => nil
    | S n => (N_toReg n) :: create_locR (n)
  end.

Definition translate_region (pc_trans:JVM_PC->list (N*N)) : CheckCdr.M.t (MapN.t bool) 
  -> CheckCdr_int.M.t (MapAddress.t bool) :=
  fun sourceMap => CheckCdr.M.fold _ _ 
    (fun key subM newM => 
       CheckCdr_int.M.update _ newM (last (pc_trans (fst key)) (0,0)%N , snd key) 
       (MapN.fold _ _
       (fun subKey b newSubM => 
          fold_left (fun m' key =>
            MapAddress.update _ m' key b)
          (pc_trans subKey) newSubM)
       subM (MapAddress.empty bool))
    )
  sourceMap (CheckCdr_int.M.empty (MapAddress.t bool)).

Fixpoint append_instruction_blocks 
  (m:MapAddress.t (DEX_Instruction * (option (N*N) * list DEX_ClassName)))
  (l:list DEX_Instruction) (address_list:list (N*N))
  : MapAddress.t (DEX_Instruction * (option (N*N) * list DEX_ClassName)) :=
  match l, address_list with 
    | nil, nil => m
    | h :: nil, h' :: nil => MapAddress.update _ m h' (h, (None, nil))
    | h :: t, h' :: t' => let newM := MapAddress.update _ m h' (h, (Some (hd (0,0)%N t'), nil)) in  
                          append_instruction_blocks (newM) (t) (t')
    | _, _ => m (* an impossible case, if the proof ever reach here probably something goes wrong *)
  end.

(* ignore return block for now *)
Definition codes_to_map (compiled_codes:(BlockMap*Block)) (trans_jvm_int:JVM_PC -> list (N*N))
  : codes_int:=
  MapPC.fold _ _ 
    (fun key block newM =>
       append_instruction_blocks newM (BLOCK.dex_instructions block) (trans_jvm_int key)
    )
  (fst compiled_codes) 
  (MapAddress.empty (DEX_Instruction*(option (N*N)*list DEX_ClassName))).

Definition create_RT (m:MapAddress.t TypeRegisters) : (N*N) -> TypeRegisters :=
  (fun key => match MapAddress.get _ m key with
                | None => MapN.empty L.t'
                | Some rt => rt
              end). 

Lemma translation_soundness : forall p m bm insnList
  jvm_static_sign jvm_virtual_sign compiled_program type_result
  jvm_se jvm_S jvm_reg trans_jvm_int trans_int_jvm RT, 
  check p (jvm_se) (jvm_S) (jvm_reg) m = true 
  -> jvm_static_sign = JVM_static_signature p (JVM_METHOD.signature m)
  -> jvm_virtual_sign = JVM_virtual_signature p (JVM_METHOD.signature m)
  -> Some bm = JVM_METHOD.body m
  -> insnList = create_insnList (bm)
  -> (compiled_program, type_result) = translate_instructions (insnList) 
     (trace_parent_child insnList
     (start_block insnList)) 
  -> trans_int_jvm = pc_int_jvm (create_int_jvm_map (snd type_result))
  -> trans_jvm_int = pc_jvm_int (snd type_result)
  -> RT = create_RT (fst type_result)
  -> check_int (translate_se (jvm_se) (trans_int_jvm)) (RT) 
       (JVM_METHOD.isStatic m) (static_sign jvm_static_sign) 
       (virtual_sign jvm_virtual_sign) (create_locR (JVM_BYTECODEMETHOD.max_locals bm)) 
       (translate_region (trans_jvm_int) jvm_reg) (codes_to_map compiled_program trans_jvm_int)
       = true.
  Proof.

    intros. unfold check_int. unfold check in H.
    destruct (JVM_METHOD.isStatic m) eqn:method_static.
    (* The method is static *)
      unfold check_codes_int.
      apply for_all_steps_codes_true2.
      intros.
      unfold Typing_int.DEX_tcheck.
      unfold Typing_int.tsub_next. 
      destruct ins eqn:Hins.
      inversion H9.
      
      Lemma nextAddress_same : forall codes i, Step_int.nextAddress codes i 
        = Typing_int.nextAddress codes i.
      Proof.
        unfold Typing_int.nextAddress.
        unfold Step_int.nextAddress. reflexivity.
      Qed.
      rewrite <- nextAddress_same. rewrite H10.
      (*  clear H11; clear H13; clear H14; clear H10.*)
      rewrite <- H13 in H9. rewrite <- H14 in H9.
      apply Step_int.DEX_nop in H9.
      unfold Step_int.for_all_steps_codes.
      unfold MapAddress.for_all.
      unfold MapAddress'.fold. unfold MapN.fold. unfold BinNatMap_Base.fold.
      destruct (codes_to_map compiled_codes trans_jvm_int) as (v,m0) eqn:Hcodes.
      destruct v eqn:Hv.
      destruct t eqn:Ht.
      destruct o eqn:Ho.
      apply andb_true_intro. split. 
      (* 1st branch *)
        destruct p0 as (ins, next0) eqn:Hp0.
        unfold for_all. 
        unfold fold_right.
        unfold Step_int.get_steps.
        apply for_all_steps_m_true in H.
        
        destruct ins eqn:Hins.
        apply andb_true_intro. split. 
          
          admit. reflexivity.
        destruct (Step_int.get_steps jump_address (0%N, 0%N) ins (fst next0)).
        
        
      
      apply Step_int.for_all_steps_codes_true with (codes := codes_to_map compiled_codes trans_jvm_int)
      (jump_label := jump_address) (test :=(fun (i : Step_int.address)
     (ins : DEX_BigStep.DEX_Dom.DEX_Prog.DEX_Instruction) (_ : DEX_tag)
     (_ : option Step_int.address) =>
   Typing_int.DEX_tcheck (codes_to_map compiled_codes trans_jvm_int)
     jump_address (create_locR (JVM_BYTECODEMETHOD.max_locals bm0))
     (static_sign jvm_static_sign) (translate_se jvm_se trans_int_jvm)
     (selift_int (translate_se jvm_se trans_int_jvm)
        (translate_region trans_jvm_int jvm_reg)) RT i ins)).
  Qed.
*)
  Abort.