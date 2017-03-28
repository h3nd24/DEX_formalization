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

Lemma inv_st_in : forall kobs ft pc0 pc1 r0 r1 b0 b1 rt0 rt1 h0 h1,
 st_in kobs ft b1 b0 rt1 rt0 (pc1, h1, r1) (pc0, h0, r0) ->
   Regs_in kobs b1 b0 r1 r0 rt1 rt0.
Proof.
  intros.
  inversion_clear H; intuition.
Qed.
Implicit Arguments inv_st_in.