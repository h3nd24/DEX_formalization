Require Export DEX_ElemLemmas.


Import DEX_BigStepWithTypes.DEX_BigStepWithTypes DEX_Dom DEX_Prog.

(*   Opaque BigStep.Dom.Heap.update. *)

Section p. 
Variable kobs: L.t.
Variable p : DEX_ExtendedProgram.

(*
Lemma high_exec_normal : 
 forall se reg m sgn pc i h1 s1 l1 st1 b1 st2 b2 s2 h2 pc2 l2,
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1 st1 ->
   DEX_BigStepWithTypes.NormalStep kobs p se reg m sgn i 
     (pc,(h1,s1,l1)) st1 b1 (pc2,(h2,s2,l2)) st2 b2 ->
   b1 = b2.
Proof.
  intros.
  destruct i; simpl in H2; inversion_mine H2;
  repeat match goal with
      [ id : high_st _ (_::_) (_::_) |- _ ] => inversion_mine id
  end; 
  unfold BigStepWithTypes.newb; try reduce_leql_dec; 
    try reflexivity.
Qed.
*)

(* Step consistent *)
(*
Lemma indist1_intra_normal : 
 forall se reg m sgn pc1 pc pc2' i r1 rt1 r1' rt1' r2' rt2',
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
(*    high_st kobs s1' st1' -> *)
   NormalStep (*kobs p*) se reg m sgn i (pc,r1') rt1' (pc2',r2') rt2' ->

   st_in kobs (*sgn.(DEX_lvt)*) rt1 rt1' (pc1,r1) (pc,r1') ->

   st_in kobs  (*sgn.(DEX_lvt)*) rt1 rt2' (pc1,r1) (pc2',r2').
Proof.
  intros.
  apply inv_st_in in H2.  
(*   destruct (inv_st_in H2) as [Rin]. ; clear H2. *)
(*   assert (HH1:=os_in_high_high _ _ _ _ _ _ _ (os_in_sym _ _ _ _ _ _ _ Sin) H1).
  destruct i; simpl in H2; inversion_clear H2 in H H0 H1 HH1 Hin Sin Lin; *)
  destruct i; simpl in H1; apply Build_st_in; 
    try (inversion_clear H1 in H H0 H2; intuition; fail). 
  inversion_clear H1 in H H0 H2.
  (* Move *)
  clear H3. 
  
  repeat match goal with
      [ id : high_st _ (_::_) (_::_) |- _ ] => inversion_mine id
  end; 
  unfold newb; try reduce_leql_dec; 
  (constructor;
  [ (* localvar *)
    try assumption
  | (* operand stack *)
    constructor 1; repeat constructor; try assumption;
    try (apply lift_os_high; auto);
    try (apply elift_os_high; auto);
    simpl in *; eauto with lattice
(*  | (* heap *)
    try assumption]).
  (* Ibinop *)
  destruct op; assumption || (apply elift_os_high; auto).
  (* Iinc *)
  apply localvar_in_upd_high_right; eauto with lattice.
  (* New *)
  eapply ffun_extends_hp_in_new_right; eauto.
  (* Newarray *)
  eapply ffun_extends_hp_in_newarray_right; eauto.
  (* Putfield *)
  eapply hp_in_putfield_high_update_right; eauto with lattice. 
  (* Vastore *)
  eapply hp_in_arraystore_high_update_right with (mpc:=mpc); eauto with lattice.*)
  (* Vstore *)
  apply localvar_in_upd_high_right; eauto with lattice.
Qed.

(*
Lemma indist1_return_intra_normal : 
 forall se reg m sgn pc pc2' i h1 h2' v1 b1 
                   h1' s1' l1' st1' b1' b2' s2' st2' l2',
   instructionAt m pc = Some i ->
   ~ L.leql (se pc) kobs ->
   high_st kobs s1' st1' ->
   NormalStep kobs p se reg m sgn i 
     (pc,(h1',s1',l1')) st1' b1' (pc2',(h2',s2',l2')) st2' b2' ->

   indist_intra_return kobs p sgn (pc,(h1',s1',l1')) st1' b1' h1 v1 b1 ->

   indist_intra_return kobs p sgn (pc2',(h2',s2',l2')) st2' b2' h1 v1 b1.
Proof.
  intros.
  inversion_mine H3.
  destruct i; simpl in H2; inversion_mine H2;
  repeat match goal with
      [ id : high_st _ (_::_) (_::_) |- _ ] => inversion_mine id
  end; 
  unfold newb; try reduce_leql_dec; 
  (constructor;
  [ try assumption
  | try assumption
  | repeat constructor; try assumption;
    try (apply lift_os_high; auto);
    try (apply elift_os_high; auto);
    simpl in *; eauto with lattice
  ]).
  (* Ibinop *)
  destruct op; assumption || (apply elift_os_high; auto).
  (* New *)
  apply hp_in_sym.
  eapply ffun_extends_hp_in_new_right; eauto.
  apply hp_in_sym; auto.
  (* Newarray *)
  apply hp_in_sym.
  eapply ffun_extends_hp_in_newarray_right; eauto.
  apply hp_in_sym; auto.
  (* Putfield *)
  apply hp_in_sym.
  eapply hp_in_putfield_high_update_right; eauto with lattice.
  apply hp_in_sym; auto.
  (* Vastore *)
  apply hp_in_sym.
  eapply hp_in_arraystore_high_update_right with (mpc:=mpc); eauto with lattice.
  apply hp_in_sym; auto.
Qed.

End p.
*)


(* 
*** Local Variables: ***
*** coq-prog-name: "~/Soft/src/coq-8.2pl1/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../Library" "-I" "../Library/Map") ***
*** End: ***
 *)