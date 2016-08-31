Require Export DEX_BigStepWithTypes.

Import DEX_BigStepWithTypes DEX_BigStepAnnot.DEX_BigStepAnnot 
  DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.


Lemma reduce_dec_true : forall (P:Prop) (test:{P}+{~P}),
   P -> exists h, test = left (~P) h.
Proof.
  intros.
  destruct test; contradiction || eauto.
Qed.

Lemma reduce_dec_false : forall (P:Prop) (test:{P}+{~P}),
   ~P -> exists h, test = right P h.
Proof.
  intros.
  destruct test; contradiction || eauto.
Qed.
(* Opaque Heap.update. *)

Ltac reduce_leql_dec :=
  match goal with
   [ id : ~ L.leql ?x ?y |- context[L.leql_dec ?x ?y] ] => 
      let h := fresh "h" in
      let Heq := fresh "Heq" in 
        (destruct (reduce_dec_false _ (L.leql_dec x y) id) as [h Heq];
          simpl in Heq;
         rewrite Heq; clear h Heq)
  |[ id : L.leql ?x ?y |- context[L.leql_dec ?x ?y] ] => 
      let h := fresh "h" in
      let Heq := fresh "Heq" in 
        (destruct (reduce_dec_true _ (L.leql_dec x y) id) as [h Heq];
          simpl in Heq;
         rewrite Heq; clear h Heq)
  end.

Ltac reduce_leql_dec_strong :=
  match goal with
   [ id : ~ L.leql ?x ?y |- context[L.leql_dec ?x ?y] ] => 
      let h := fresh "h" in
      let Heq := fresh "Heq" in 
        (destruct (reduce_dec_false _ (L.leql_dec x y) id) as [h Heq];
         rewrite Heq; clear h Heq)
  |[ id : L.leql ?x ?y |- context[L.leql_dec ?x ?y] ] => 
      let h := fresh "h" in
      let Heq := fresh "Heq" in 
        (destruct (reduce_dec_true _ (L.leql_dec x y) id) as [h Heq];
         rewrite Heq; clear h Heq)
  |[ |- context[L.leql_dec ?x ?y] ] => 
      let id := fresh in (
      try (assert (id:L.leql x y); 
           [simpl in *; eauto with lattice;fail
           |let h := fresh "h" in
            let Heq := fresh "Heq" in 
            (destruct (reduce_dec_true _ (L.leql_dec x y) id) as [h Heq];
             rewrite Heq; clear h Heq)]);
      try (assert (id:~L.leql x y); 
           [simpl in *; eauto with lattice;fail
           |let h := fresh "h" in
            let Heq := fresh "Heq" in 
            (destruct (reduce_dec_false _ (L.leql_dec x y) id) as [h Heq];
             rewrite Heq; clear h Heq)]))
  end.

(*   Implicit Arguments os_in_tl. *)
(*
Ltac os_in_tail_this H :=
  let Sin := fresh "Sin" in (
    assert (Sin:=os_in_tl H);
    try os_in_tail_this Sin
  ).

Ltac os_in_tail :=
  match goal with
  [ id : os_in _ _ _ (_::_) (_::_) (_::_) (_::_) |- _ ] => os_in_tail_this id
  end.

Ltac case_os_in H :=
   let T1 := fresh "T" in
   let T2 := fresh "T" in
   let T3 := fresh "T" in (
     elim os_in_cons_cases2 with (1:=H); 
      [intros (T1,(T2,T3)); inversion_mine T2|intros (T1,T2)]).

Ltac os_app :=
  try match goal with
  [ id : os_in ?kobs ?b1 ?b2 (?a1 ++ ?s1) (?a2 ++ ?s2) (?st1 ++ ?stt1) (?st2 ++ ?stt2) |- _ ] =>
    let H := fresh "SinApp" in (
    assert (H:os_in kobs b1 b2 s1 s2 stt1 stt2); 
     [apply os_in_app1 with a1 a2 st1 st2; auto; congruence
     |idtac])
  end.
*)
Lemma inv_st_in : forall kobs pc0 pc1 r0 r1 rt0 rt1,
 st_in kobs rt1 rt0 (pc1, r1) (pc0, r0) ->
   Regs_in kobs r1 r0 rt1 rt0.
Proof.
  intros.
  inversion_clear H; intuition.
Qed.
Implicit Arguments inv_st_in.

(* Hint Resolve os_in_lift os_in_elift. *)

(*Definition newb (kobs:L.t) (k:L.t) (b:FFun.t Location) (loc:Location) : FFun.t Location :=
    if L.leql_dec k kobs then (FFun.extends b loc) 
    else b.*)
(*
Lemma ExceptionStep_typeof : forall kobs p m sgn i s st b1 h loc k b2 cn,
  BigStepWithTypes.ExceptionStep kobs p m sgn i s st b1 (h,loc) k b2 cn ->
  Heap.typeof h loc = Some (Heap.LocationObject cn).
Proof.
  intros.
  inversion_clear H; auto.
  eapply Heap.new_typeof; eauto.
Qed.
Implicit Arguments ExceptionStep_typeof.

Lemma CaughtException_same1 : forall p m pc h1 h2 loc1 loc2 pc',
 @CaughtException p m (pc, h1, loc1) pc' ->
 Heap.typeof h1 loc1 = Heap.typeof h2 loc2 ->
 CaughtException p m (pc, h2, loc2) pc'.
Proof.
  intros.
  inversion_clear H.
  constructor 1 with bm e; auto; congruence.
Qed.

Lemma lookup_handlers_same2 : forall p ex pc pc1 pc2 e,
 lookup_handlers p ex pc e pc1 ->
 lookup_handlers p ex pc e pc2 -> pc1 = pc2.
Proof.
  induction 1; intros.
  inversion_clear H0 in H; intuition.
  inversion_clear H1; intuition.
Qed.

Lemma CaughtException_same2 : forall p m pc pc1 pc2 h loc,
 @CaughtException p m (pc, h, loc) pc1 ->
 CaughtException p m (pc, h, loc) pc2 -> pc1 = pc2.
Proof.
  intros.
  inversion_clear H in H0.
  inversion_clear H0.
  DiscrimateEq.
  eapply lookup_handlers_same2; eauto.
Qed.

Lemma CaughtException_same3 : forall p m pc h1 h2 loc1 loc2 pc1 pc2,
 @CaughtException  p m (pc, h1, loc1) pc1 ->
 Heap.typeof h1 loc1 = Heap.typeof h2 loc2 ->
 CaughtException p m (pc, h2, loc2) pc2 -> pc1 = pc2.
Proof.
  intros.
  apply CaughtException_same2 with p m pc h2 loc2; auto.
  apply CaughtException_same1 with (1:=H); assumption.
Qed.

  Hint Resolve os_in_lift_high_os.

Lemma rewrite_elift : forall e m pc k st,
  In e (throwableAt m pc) ->
  elift m pc k st = lift k st.
Proof.
  unfold elift; intros.
  destruct (throwableAt m pc); simpl; auto.
  elim H.
Qed.

Ltac try_rewrite_elift :=
  try match goal with
   [ id : In ?e (throwableAt ?m ?pc) |- context[elift ?m ?pc ?k ?st] ] => 
      rewrite (rewrite_elift e m pc k st id)
  end.

Lemma elift_or : forall m pc,
  (forall k st, elift m pc k st = lift k st) \/ 
  (forall k st, elift m pc k st = st).
Proof.
  unfold elift; intros.
  destruct (throwableAt m pc); auto.
Qed.

Ltac elift_case :=
  try match goal with
   [ |- context[elift ?m ?pc ?k ?st] ] => 
   (let h := fresh in
     destruct (elift_or m pc) as [h|h];
       repeat rewrite h; clear h)
  end.
*)