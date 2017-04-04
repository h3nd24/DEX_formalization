(*** Framework.v: Abstract framework where we prove non interference from unwindings lemmas *)
Require Export Wf_nat.
Require Export Omega.
Require Export Max.
Require Export Level.
Require Export cdr.
Require Export Axioms.
Require Export Tactics.
Require Import Setoid.

 Import L.

Section A.
Variable observable : L.t.

Variable PC : Set.
Variable Method : Type.
Variable Kind: Set.
Variable step : Method -> PC -> option PC -> Prop.
Variable PM : Method -> Prop.
Variable cdr : forall m, PM m -> CDR (step m).
Implicit Arguments region.

Variable Reg : Set.

Variable Sign : Set.

Record SignedMethod : Type := SM {unSign:Method; sign:Sign}.
Coercion unSign :  SignedMethod >-> Method.

Variable istate rstate : Type.
Variable exec : Method -> istate -> istate+rstate -> Prop.

Variable pc : istate -> PC.

Notation "m |- p1 => p2" := (step m p1 (Some p2)) (at level 30). 
Notation "m |- p1 => " := (step m p1 None) (at level 30).
Variable exec_step_some : forall m s s',
  PM m -> exec m (* kd *) s (inl _ s')-> m |- (pc s) => (pc s').
Variable exec_step_none : forall m s s',
  PM m -> exec m (* kd *) s (inr _ s')-> m |- (pc s) =>.

Variable registertypes : Type.
Variable pbij : Type.

Variable texec : forall m, PM m ->
      Sign -> (PC->L.t) -> PC ->
      registertypes -> option registertypes -> Prop.
Variable high_reg : registertypes -> Reg -> Prop.
Variable indist_reg_val : istate -> istate -> pbij -> pbij -> Reg -> Prop.
Variable same_reg_val : istate -> istate -> Reg -> Prop.
Variable same_reg_val_indist2 : forall s1 s2 s1' s2' b1 b2 r,
  indist_reg_val s1 s2 b1 b2 r ->
  same_reg_val s1 s1' r -> same_reg_val s2 s2' r ->
  indist_reg_val s1' s2' b1 b2 r.
Variable same_reg_val_indist1 : forall s1 s2 s1' b1 b2 r,
  indist_reg_val s1 s2 b1 b2 r ->
  same_reg_val s1 s1' r -> 
  indist_reg_val s1' s2 b1 b2 r.
(* Variable indist_reg_val_trans : forall s1 s2 s3 b1 b2 b3 r, 
  indist_reg_val s1 s2 b1 b2 r -> indist_reg_val s2 s3 b2 b3 r -> indist_reg_val s1 s3 b1 b3 r. *)
Variable indist_reg_val_sym : forall s1 s2 b1 b2 r, 
  indist_reg_val s1 s2 b1 b2 r -> indist_reg_val s2 s1 b2 b1 r.
Inductive indist_reg : registertypes -> registertypes -> istate -> istate -> pbij -> pbij -> Reg -> Prop :=
  | high_indist_reg : forall rt1 rt2 s1 s2 b1 b2 r,
      high_reg rt1 r -> high_reg rt2 r -> indist_reg rt1 rt2 s1 s2 b1 b2 r
  | low_indist_reg : forall rt1 rt2 s1 s2 b1 b2 r, indist_reg_val s1 s2 b1 b2 r -> 
      indist_reg rt1 rt2 s1 s2 b1 b2 r.
Inductive indist_regs : registertypes -> registertypes -> istate -> istate -> pbij -> pbij -> Prop :=
  | indist_all_regs : forall rt1 rt2 s1 s2 b1 b2, (forall r, indist_reg rt1 rt2 s1 s2 b1 b2 r) -> indist_regs rt1 rt2 s1 s2 b1 b2.
Variable indist : Sign -> registertypes -> registertypes -> pbij -> pbij -> istate -> istate -> Prop.
Variable indist_heap : istate -> istate -> pbij -> pbij -> Prop.
Variable indist_heap_sym : forall s1 s2 b1 b2,
  indist_heap s1 s2 b1 b2 -> indist_heap s2 s1 b2 b1.
Variable indist_from_regs_heap : forall sgn rt1 rt2 s1 s2 b1 b2 , 
  indist_regs rt1 rt2 s1 s2 b1 b2 -> indist_heap s1 s2 b1 b2 ->
  indist sgn rt1 rt2 b1 b2 s1 s2.
Variable indist_reg_from_indist : forall sgn rt1 rt2 s1 s2 b1 b2 ,
  indist sgn rt1 rt2 b1 b2 s1 s2 -> 
  forall r, 
    (high_reg rt1 r -> high_reg rt2 r -> indist_reg rt1 rt2 s1 s2 b1 b2 r) /\ 
    ((~high_reg rt1 r /\ ~high_reg rt2 r) \/
      (high_reg rt1 r /\ ~high_reg rt2 r) \/
      (~high_reg rt1 r /\ high_reg rt2 r) ->
    indist_reg_val s1 s2 b1 b2 r).
Variable indist_heap_from_indist : forall sgn rt1 rt2 s1 s2 b1 b2,
  indist sgn rt1 rt2 b1 b2 s1 s2 ->
  indist_heap s1 s2 b1 b2.

Variable rindist : Sign -> pbij -> pbij -> rstate -> rstate -> Prop.
Variable indist_sym : forall m rt1 rt2 s1 s2 b1 b2,
 indist m rt1 rt2 b1 b2 s1 s2 -> indist m rt2 rt1 b2 b1 s2 s1.
Variable rindist_sym : forall m s1 s2 b1 b2,
 rindist m b1 b2 s1 s2 -> rindist m b2 b1 s2 s1.

Variable high_result : Sign -> rstate -> Prop.

Variable rt0 : Method-> Sign -> registertypes.
Variable init_pc : Method -> PC -> Prop.

Inductive evalsto (m:Method) : nat -> istate -> rstate -> Prop :=
  | evalsto_res : forall (* k *) s res,
      exec m (* k *) s (inr _ res) -> evalsto m 1 s res
  | evalsto_intra : forall (* k *) n s1 s2 res,
     exec m (* k *) s1 (inl _ s2) -> 
     evalsto m n s2 res ->
     evalsto m (S n) s1 res.

Variable border : pbij -> pbij -> Prop.
Variable border_refl : forall b, border b b.
Variable border_trans : forall b1 b2 b3, 
  border b1 b2 ->
  border b2 b3 ->
  border b1 b3.

Variable P : SignedMethod -> Prop.

Variable PM_P : forall m, P m -> PM m.

Definition ni :=
  forall m p p' sgn s s' r r' b b',
  P (SM m sgn) ->
(*   rt0 m sgn rt -> *)
  indist sgn (rt0 m sgn) (rt0 m sgn) b b' s s' ->
  pc s = pc s' ->
  init_pc m (pc s) ->
  init_pc m (pc s') ->
  evalsto m p s r ->
  evalsto m p' s' r' ->
  exists br, exists br',
  border b br /\
  border b' br' /\
  rindist sgn br br' r r'.
  
  
(* seems weird to have same rt *)
Variable indist2_intra : forall m sgn se rt ut ut' s s' u u' b b',
  forall H0:P (SM m sgn), 
  indist sgn rt rt b b' s s' ->
  pc s = pc s' ->
  exec m s (inl _ u) ->
  exec m s' (inl _ u') ->
  texec m (PM_P _ H0) sgn se (pc s) rt (Some ut) ->
  texec m (PM_P _ H0) sgn se (pc s) rt (Some ut') ->
    exists bu, exists bu',
    border b bu /\
    border b' bu' /\
    indist sgn ut ut' bu bu' u u'.

Variable indist2_return : forall m sgn se rt s s' u u' b b',
  forall H0:P (SM m sgn),
  indist sgn rt rt b b' s s' ->
  pc s = pc s' ->
  exec m s (inr _ u) -> 
  exec m s' (inr _ u')-> 
  texec m (PM_P _ H0) sgn se (pc s) rt None ->
  texec m (PM_P _ H0) sgn se (pc s) rt None ->
    exists bu, exists bu',
    border b bu /\
    border b' bu' /\
    rindist sgn bu bu' u u'.

(* high branching *)
Variable soap2_basic_intra : forall m sgn se rt ut ut' s s' u u' b b',
  forall (h:P (SM m sgn)),
  indist sgn rt rt b b' s s' -> 
  pc s = pc s' ->
  exec m s (inl _ u) -> 
  exec m s' (inl _ u') -> 
  texec m (PM_P _ h) sgn se (pc s) rt (Some ut) ->
  texec m (PM_P _ h) sgn se (pc s) rt (Some ut') ->
  pc u <> pc u' -> 
    (forall j:PC, (region (cdr m (PM_P _ h)) (pc s) j) -> ~ leql (se j) observable).

Variable sub : registertypes -> registertypes -> Prop.
Variable sub_simple : forall sgn rt rt' rt0 s s0 b b0,
  indist sgn rt0 rt b0 b s0 s ->
  sub rt rt' ->
  indist sgn rt0 rt' b0 b s0 s.

Inductive typed_exec (m:Method) (H:PM m) (sgn:Sign) (se:PC->L.t) (RT:PC->registertypes) 
: istate -> istate + rstate -> Prop :=
  typed_exec_def1 : forall s1 s2 rt',
   exec m s1 (inl _ s2) ->
   sub rt' (RT (pc s2)) ->
   texec m H sgn se (pc s1) (RT (pc s1)) (Some rt') ->
   typed_exec m H sgn se RT s1 (inl _ s2)
| big_exec_def2 : forall s1 s2,
   exec m s1 (inr _ s2) ->
   texec m H sgn se (pc s1) (RT (pc s1)) None ->
   typed_exec m H sgn se RT s1 (inr _ s2).

Inductive tevalsto (m:Method) (H:PM m) (sgn:Sign) (se:PC->L.t) (RT:PC->registertypes) : nat -> istate -> rstate -> Prop :=
  | tevalsto_res : forall s res,
      typed_exec m H sgn se RT s (inr _ res) -> tevalsto m H sgn se RT 1 s res
  | tevalsto_intra : forall n s1 s2 res,
     typed_exec m H sgn se RT s1 (inl _ s2) -> 
     tevalsto m H sgn se RT n s2 res ->
     tevalsto m H sgn se RT (S n) s1 res.

(* Hendra additional *)
Variable tevalsto_high_result' : forall m sgn (H:PM m) se s RT res,
  ~L.leql (se m sgn (pc s)) observable ->
  exec m s (inr res) ->
  texec m H sgn (se m sgn) (pc s) (RT m sgn (pc s)) None -> high_result sgn res.

Variable tevalsto_diff_high_result : forall se RT m sgn s s' p res res' (H:PM m),
  pc s = pc s' -> 1 < p ->
  tevalsto m H sgn (se m sgn) (RT m sgn) 1 s res -> tevalsto m H sgn (se m sgn) (RT m sgn) p s' res' -> 
  high_result sgn res /\ high_result sgn res'.

Variable high_result_indist : forall sgn res res0 b b0,
  high_result sgn res -> high_result sgn res0 -> rindist sgn b b0 res res0.

Variable eq_map : registertypes -> registertypes -> Prop.
Variable eq_map_refl : reflexive registertypes eq_map.
Variable eq_map_sym : symmetric registertypes eq_map.
Variable eq_map_trans : transitive registertypes eq_map.
Theorem map_setoid: Setoid_Theory registertypes eq_map.
 split.
 exact eq_map_refl.
 exact eq_map_sym.
 exact eq_map_trans.
Qed.
Add Setoid registertypes eq_map map_setoid as eq_map_rel.

Variable indist_morphism_proof : forall (y : Sign) (x y0 : registertypes),
eq_map x y0 ->
forall (x0 y1 : registertypes),
eq_map x0 y1 -> forall (b2 b3 : pbij) (y2 y3 : istate), 
  indist y x x0 b2 b3 y2 y3 <-> indist y y0 y1 b2 b3 y2 y3.
Add Morphism indist : indist_morphism. Proof. exact indist_morphism_proof. Qed.

Definition Typable (m:Method) (H:PM m) (sgn:Sign) (se:Method->Sign->PC->L.t) (RT:Method->Sign->PC->registertypes) : Prop :=
  (forall i, init_pc m i -> eq_map (RT m sgn i) (rt0 m sgn)) /\ 
  (forall i,
     m |- i => ->
     texec m H sgn (se m sgn) i (RT m sgn i) None) /\
  (forall i j,
    m |- i =>j ->
    exists rt,
      texec m H sgn (se m sgn) i (RT m sgn i) (Some rt) 
      /\ sub rt (RT m sgn j)).

Definition TypableProg se S := 
  forall m sgn (H:P (SM m sgn)), Typable m (PM_P _ H) sgn se S.

Lemma typable_evalsto : forall se RT m sgn n s r
  (H:PM m),
  Typable m H sgn se RT ->
  evalsto m n s r -> 
  tevalsto m H sgn (se m sgn) (RT m sgn) n s r.
Proof.
  intros until r; intros HP H.
  destruct H as [_ [H0 H1]].
  induction 1.
  (* ret *)
  constructor 1; auto.
  constructor; auto.
  apply H0; auto.
  eapply exec_step_none; eauto.
  (* next *)
  constructor 2 with s2; auto.  
  elim H1 with (pc s1) (pc s2).
  intros st (HT,Hs).
  constructor 1 with st; auto.
  eapply exec_step_some; eauto.  
Qed.

Lemma tevalsto_evalsto : forall se RT m sgn p s r
  (h:PM m),
  tevalsto m h sgn (se m sgn) (RT m sgn) p s r ->
  evalsto m p s r.
Proof.
  induction 1.
  inversion H. 
  constructor 1; auto.
  inversion H.
  constructor 2 with s2; auto. 
Qed.

Lemma tevalsto_high_result : forall m sgn (H:PM m) se RT s res,
  ~L.leql (se m sgn (pc s)) observable ->
  tevalsto m H sgn (se m sgn) (RT m sgn) 1 s res -> high_result sgn res.
Proof.
  intros.
  apply tevalsto_high_result' with (m:=m) (H:=H) (sgn:=sgn) (se:=se) (s:=s) (RT:=RT); auto.
  apply tevalsto_evalsto in H1. inversion H1; auto. inversion H4.
  inversion H1; auto. inversion H2; auto. inversion H4.
Qed.

Implicit Arguments tevalsto_evalsto.

Hint Resolve PM_P.

Section TypableProg.
Variable se : Method -> Sign -> PC -> L.t.
Variable RT : Method -> Sign -> PC -> registertypes.
Variable T : TypableProg se RT.

Definition high_region m (h:PM m) sgn (i:PC) := 
  forall j:PC, region (cdr m h) i j ->
    ~ leql (se m sgn j) observable.

Hint Immediate indist_sym rindist_sym.
Hint Resolve exec_step_some exec_step_none.

Lemma final_bighighstep_aux : forall m sgn i p s res (H: P (SM m sgn)),
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s res ->
  region (cdr m (PM_P _ H)) i (pc s) ->
  (forall jun, ~junc (cdr m (PM_P _ H)) i jun) ->
  high_region m (PM_P _ H) sgn i ->
  high_result sgn res.
Proof.
  intros.
  induction H0.
  apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se) (RT:=RT) (s:=s); auto.
    constructor 1; auto.
  apply IHtevalsto; auto.
  inversion H0.
    eapply exec_step_some with (1:=PM_P _ H) in H6; eauto.
    elim (soap2 (cdr m (PM_P _ H))) with i (pc s1) (pc s2); auto.
    intros. unfold not in H2. apply H2 in H10. contradiction.
Qed.

Lemma final_bighighstep : forall m sgn p i s0 s res res0 b b0 
  (H:P (SM m sgn)),
  pc s = pc s0 ->
  evalsto m p s res-> 
  evalsto m 1 s0 res0 ->
  region (cdr m (PM_P _ H)) i (pc s)-> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s0)) b b0 s s0 ->
  high_region m (PM_P _ H) sgn i ->
    rindist sgn b b0 res res0.
Proof.
  intros.
  inversion H2; try (inversion H8).
  destruct (T m sgn H). inversion_mine H11.
  apply high_result_indist.
  (* high result res *)
    apply final_bighighstep_aux with (m:=m) (i:=i) (p:=p) (s:=s) (H:=H); auto.
    apply typable_evalsto; auto.
    intros.
    apply soap3 with (j:=pc s0).
    rewrite <- H0; auto.
    apply exec_step_none with (1:=PM_P _ H) in H6.
    unfold result; eauto.
  (* high result res0 *)
    apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se) (RT:=RT) (s:=s0).
        rewrite <- H0; auto.
      apply typable_evalsto; auto.
Qed.

Lemma my_double_ind:forall P:(nat->nat->Prop),
   (forall n m:nat, (forall p q:nat, lt p n -> lt q m -> P p q) -> P n m) -> 
   forall p q:nat, P p q.
Proof.
  intros P0 H.
  apply lt_wf_double_ind.
  intros.
  apply H.
  intros.
  apply H0.
  assumption.
Qed.

Lemma execution_reach_junction_or_return_1 : forall m sgn ns i s res (H: P (SM m sgn)),
  region (cdr m (PM_P _ H)) i (pc s) ->
  evalsto m ns s res ->
  (exists u, exists ps,
    evalsto m ps u res /\ ps < ns /\
    junc (cdr m (PM_P _ H)) i (pc u))
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) i jun).
Proof.
  intros m sgn ns.
  pattern ns. apply lt_wf_ind.
  clear ns; intros ns Hind; intros.  
  inversion H1; auto.
  right.
  apply exec_step_none with (1:=PM_P _ H) in H2.
  intros; apply soap3 with (k:=jun) in H0; auto.
  elim (soap2 (cdr m (PM_P _ H))) with i (pc s) (pc s2); auto.
  intros.
  elim Hind with (m0:=n) (i:=i) (s:=s2) (res:=res) (H:=H); auto; try omega.
  intros [U [ps [sH1 [sH2 sH3]]]].
  left. exists U. exists ps. repeat (split; auto).
  intros.
  left. exists s2. exists n. repeat (split; auto).
  apply exec_step_some with (1:=PM_P _ H) in H2; auto.
Qed.

Lemma execution_reach_junction_or_return_2 : forall m sgn ns ns' i s s' res res' (H: P (SM m sgn)),
  region (cdr m (PM_P _ H)) i (pc s) ->
  region (cdr m (PM_P _ H)) i (pc s') ->
  evalsto m ns s res ->
  evalsto m ns' s' res' ->
  (exists u, exists u', exists ps, exists ps',
    evalsto m ps u res /\ ps < ns /\
    evalsto m ps' u' res' /\ ps' < ns' /\
    junc (cdr m (PM_P _ H)) i (pc u) /\ junc (cdr m (PM_P _ H)) i (pc u'))
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) i jun).
Proof.
    intros.
  apply execution_reach_junction_or_return_1 with (sgn:=sgn) (i:=i) (H:=H) in H2; auto.
  apply execution_reach_junction_or_return_1 with (sgn:=sgn) (i:=i) (H:=H) in H3; auto.
  inversion H2; inversion H3; auto.
  left.
  inversion H4; inversion H6; inversion H5; inversion H8.
  exists x; exists x1; exists x0; exists x2; auto.
  Cleanexand.
  repeat (split; auto).
Qed. 

Lemma execution_reach_junction_or_return : forall m sgn ns ns' s s' u u' res res' (H: P (SM m sgn)),
  pc s = pc s' ->  
  exec m s (inl u) -> exec m s' (inl u') -> 
  pc u <> pc u' -> 
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  (exists v, exists v', exists ps, exists ps', 
    evalsto m ps v res /\ ps <= ns /\
    evalsto m ps' v' res' /\ ps' <= ns' /\
    junc (cdr m (PM_P _ H)) (pc s) (pc v) /\ junc (cdr m (PM_P _ H)) (pc s') (pc v'))
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) (pc s) jun /\ forall jun, ~junc (cdr m (PM_P _ H)) (pc s') jun).
Proof.
  intros.
  apply exec_step_some with (1:=PM_P _ H) in H1; apply exec_step_some with (1:=PM_P _ H) in H2; auto.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc u) (pc u'); try (rewrite H0; auto; fail); auto; intros.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc u') (pc u); try (rewrite H0; auto; fail); auto; intros.
  (* both are in the region *)
  apply execution_reach_junction_or_return_2 with (ns:=ns) (ns':=ns') (s:=u) (s':=u') (res:=res) (res':=res') in H6; auto.
  inversion H6.
  left. 
  Cleanexand.
  exists x; exists x0; exists x1; exists x2. repeat (split; auto). 
  omega. omega.
  rewrite H0 in H13; auto. 
  right. split; auto. rewrite H0 in H8; auto.
  (* one is in the region *)
  apply execution_reach_junction_or_return_1 with (ns:=ns') (s:=u') (res:=res') in H6; auto.
  inversion H6; Cleanexand.
  left.
  exists u; exists x; exists ns; exists x0; repeat (split; auto).
  omega. rewrite H0 in H10; auto.
  right. split; auto. rewrite H0 in H8; auto.
  (* *)
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc u') (pc u); try (rewrite H0; auto; fail); auto; intros.
  (* one is in the region *)
  apply execution_reach_junction_or_return_1 with (ns:=ns) (s:=u) (res:=res) in H7; auto.
  inversion H7; Cleanexand.
  left.
  exists x; exists u'; exists x0; exists ns'; repeat (split; auto).
  omega. rewrite H0 in H6; auto.
  right. split; auto. rewrite H0 in H8; auto.
  (* both are junction point *)
  left. 
  exists u; exists u'; exists ns; exists ns'; repeat (split;auto).
  rewrite H0 in H6; auto.
Qed.

Inductive path (m:Method) (i:istate) : istate -> Type :=
  | path_base : forall j, exec m i (inl j) -> path m i j 
  | path_step : forall j k, path m k j -> exec m i (inl k) -> path m i j.

Inductive path_prop (m:Method) (i j:istate) (p:path m i j) : Prop := path_prop_cons : path_prop m i j p.

Inductive path_in_region (m:Method) (cdr: CDR (step m)) (s:PC) (i j:istate) : (path m i j) -> Prop :=
  | path_in_reg_base : forall (Hexec:exec m i (inl j)), region cdr s (pc i) -> 
      path_in_region m cdr s i j (path_base m i j Hexec)
  | path_in_reg_ind : forall k (Hexec:exec m i (inl k)) (p:path m k j), region cdr s (pc i) ->
      path_in_region m cdr s k j p -> path_in_region m cdr s i j (path_step m i j k p Hexec).

Lemma evalsto_path : forall m sgn n s i res (H: P (SM m sgn)),
  region (cdr m (PM_P _ H)) s (pc i) ->
  evalsto m n i res ->
  (exists j p, junc (cdr m (PM_P _ H)) s (pc j) /\ path_prop m i j p /\
    path_in_region m (cdr m (PM_P _ H)) s i j p /\
    (exists n', evalsto m n' j res /\ n' < n)) 
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) s jun).
Proof.
  intros m sgn n. pattern n. apply lt_wf_ind.
  clear n. intros n IH.
  intros s i res H Hreg Hevalsto.
  inversion Hevalsto.
  (* the case where i is immediately a return point *)
  apply exec_step_none with (1:=PM_P _ H) in H0.
  right. intros. apply soap3 with (j:=pc i); auto.
  (* inductive case *)
  elim soap2 with PC (step m) (cdr m (PM_P _ H)) s (pc i) (pc s2); intros; auto.
  (* path stays in region *)
  elim IH with (H:=H) (s:=s) (m0:=n0) (i:=s2) (res:=res); simpl; intros; auto.
  Cleanexand.
  left. 
  exists x. exists (path_step m i x s2 x0 H0).
  repeat (split; auto).
  constructor 2; auto.
  exists x1. split; auto.
  omega.

  (* path is the junction *) 
  left. exists s2. exists (path_base m i s2 H0).
  repeat (split; auto).
  constructor 1; auto. 

  (* final case *)
  exists n0; repeat (split; auto).
  apply exec_step_some with (1:=PM_P _ H); auto.
Qed.
  
Variable changed : forall (m:Method) (i j:istate), path m i j -> Reg -> Prop.
Variable changed_high : forall m sgn s i j r (H:P (SM m sgn)) (Hpath: path m i j), 
  (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) observable) ->
  path_in_region m (cdr m (PM_P _ H)) s i j Hpath ->
  region (cdr m (PM_P _ H)) s (pc i) ->
  junc (cdr m (PM_P _ H)) s (pc j) ->
  changed m i j Hpath r -> 
    high_reg (RT m sgn (pc j)) r.
Variable not_changed_same : forall m sgn i j (Hpath: path m i j) r,
  (*(forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) observable) ->
  path_in_region m (cdr m (PM_P _ H)) s i j Hpath -> *)
  ~changed m i j Hpath r -> 
  (same_reg_val i j r) /\ 
    (high_reg (RT m sgn (pc i)) r -> high_reg (RT m sgn (pc j)) r). 
Variable high_reg_dec : forall rt r, high_reg rt r \/ ~high_reg rt r.
Variable changed_dec : forall m i j r (p:path m i j),
  changed m i j (p) r \/ ~changed m i j (p) r. 

Variable high_path_heap_indist : forall m sgn s i i' b b' j (H:P (SM m sgn)) (Hpath: path m i j), 
  (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) observable) ->
  path_in_region m (cdr m (PM_P _ H)) s i j Hpath ->
  region (cdr m (PM_P _ H)) s (pc i) ->
  junc (cdr m (PM_P _ H)) s (pc j) ->
  indist_heap i i' b b' ->
    indist_heap j i' b b'.

Lemma high_path_heap_indist2 : forall m sgn s i i' b b' j j' (H:P (SM m sgn)) 
    (Hpath: path m i j) (Hpath': path m i' j'), 
  (forall k:PC, region (cdr m (PM_P _ H)) s k -> ~ L.leql (se m sgn k) observable) ->
  path_in_region m (cdr m (PM_P _ H)) s i j Hpath ->
  path_in_region m (cdr m (PM_P _ H)) s i' j' Hpath' ->
  region (cdr m (PM_P _ H)) s (pc i) ->
  region (cdr m (PM_P _ H)) s (pc i') ->
  junc (cdr m (PM_P _ H)) s (pc j) ->
  junc (cdr m (PM_P _ H)) s (pc j') ->
  indist_heap i i' b b' ->
    indist_heap j j' b b'.
Proof.
  intros m sgn s i i' b b' j j' H Hpath Hpath' HHighReg HRegPath HRegPath'
    Hreg Hreg' Hjun Hjun' Hindist.
  apply high_path_heap_indist with (m:=m) (sgn:=sgn) (j:=j) (H:=H) (Hpath:=Hpath) (s:=s) in Hindist; auto.
  apply indist_heap_sym in Hindist.
  apply high_path_heap_indist with (m:=m) (sgn:=sgn) (j:=j') (H:=H) (Hpath:=Hpath') (s:=s) in Hindist; auto.
Qed.

Lemma junction_indist : forall m sgn ns ns' s s' u u' b b' bu bu' res res' i (H: P (SM m sgn)),
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) b b' s s' ->
  exec m s (inl u) -> exec m s' (inl u') ->
  region (cdr m (PM_P _ H)) i (pc u) ->
  region (cdr m (PM_P _ H)) i (pc u') ->
  high_region m (PM_P _ H) sgn i ->
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) bu bu' u u' ->
  (exists v, exists v', exists ps, exists ps', 
    evalsto m ps v res /\ ps <= ns /\
    evalsto m ps' v' res' /\ ps' <= ns' /\
    junc (cdr m (PM_P _ H)) i (pc v) /\ 
    junc (cdr m (PM_P _ H)) i (pc v') /\
    indist sgn (RT m sgn (pc v)) (RT m sgn (pc v')) bu bu' v v')
  \/ (high_result sgn res /\ high_result sgn res'). 
Proof.
  intros.
  elim evalsto_path with (1:=H3) (2:=H6); 
  elim evalsto_path with (1:=H4) (2:=H7); intros.
  left. destruct H10 as [v H10]; destruct H10 as [path H10]; destruct H9 as [v' H9]; destruct H9 as [path' H9].
    exists v; exists v'.
    Cleanexand.
    exists x; exists x0. 
    repeat (split; auto).
    omega. omega.
    apply indist_from_regs_heap. constructor 1.
    intros.
    elim changed_dec with (m:=m) (i:=u) (j:=v) (p:=path) (r:=r);
    elim changed_dec with (m:=m) (i:=u') (j:=v') (p:=path') (r:=r); intros; auto.
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H19; 
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H20; auto.
    constructor; auto.
    constructor 1; auto. 
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H20; auto.
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H20; auto.
    elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
      (j1:=pc v) (j2:=pc v'); auto.
    constructor 1; auto.
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H19; auto.
    elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
      (j1:=pc v') (j2:=pc v); auto.
    apply changed_high with (m:=m) (sgn:=sgn) (s:=i) (H:=H) in H19; auto.
    (* both are not changed *)
    apply not_changed_same with (m:=m) (sgn:=sgn) (i:=u') (j:=v') in H19; auto.
(*     apply not_changed_same with (m:=m) (sgn:=sgn) (i:=u') (j:=v') (s:=i) (b:=bu') (H:=H)in H19; auto.  *)
    apply not_changed_same with (m:=m) (sgn:=sgn) (i:=u) (j:=v) in H20; auto.
(*     apply not_changed_same with (m:=m) (sgn:=sgn) (i:=u) (j:=v) (s:=i) (b:=bu) (H:=H)in H20; auto. *)
    inversion H19; inversion H20.
    destruct high_reg_dec with (rt:=RT m sgn (pc u)) (r:=r);
    destruct high_reg_dec with (rt:=RT m sgn (pc u')) (r:=r).
    specialize H22 with (1:=H26); specialize H24 with (1:=H25).
    constructor 1; auto.
    specialize H24 with (1:=H25).
    constructor 1; auto.
    elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
      (j1:=pc v) (j2:=pc v'); auto.
    specialize H22 with (1:=H26).
    elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
      (j1:=pc v') (j2:=pc v); auto.
    constructor 1; auto.
    constructor 2. apply same_reg_val_indist2 with (s1:=u) (s2:=u'); auto.
    apply indist_reg_from_indist with (r:=r) in H8.
    destruct H8 as [HindistReg HindistRegVal]. apply HindistRegVal; auto.
    (*apply indist_reg_val_sym; auto.
    apply indist_reg_val_trans with (s2:=u') (b2:=bu'); auto.
    apply indist_reg_from_indist with (r:=r) in H8.
    Cleanexand.
    apply H29; auto.*)
    (* heap indist *)
    apply high_path_heap_indist2 with (m:=m) (sgn:=sgn) (i:=u) (i':=u') (H:=H)
      (Hpath:=path) (Hpath':=path') (s:=i); auto.
    apply indist_heap_from_indist in H8; auto.
  (* one of them doesn't have a junction point *)
  Cleanexand. specialize H9 with (pc x). contradiction.
  Cleanexand. specialize H10 with (pc x). contradiction.
  (* both are junction points *)
  right.
  split.
  apply typable_evalsto with (1:=T m sgn H) (se:=se) (RT:=RT) in H6. 
  apply final_bighighstep_aux with (m:=m) (sgn:=sgn) (H:=H) 
    (s:=u) (i:=i) (p:=ns); auto.
  (* the other high result *)
  apply typable_evalsto with (1:=T m sgn H) (se:=se) (RT:=RT) in H7. 
  apply final_bighighstep_aux with (m:=m) (sgn:=sgn) (H:=H) 
    (s:=u') (i:=i) (p:=ns'); auto.
Qed.

Lemma junction_indist_2 : forall m sgn ns ns' s s' u u' b b' bu bu' res res' i (H: P (SM m sgn)),
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) b b' s s' ->
  exec m s (inl u) -> exec m s' (inl u') ->
  region (cdr m (PM_P _ H)) i (pc u) ->
  junc (cdr m (PM_P _ H)) i (pc u') ->
  high_region m (PM_P _ H) sgn i ->
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) bu bu' u u' ->
  (exists v, exists ps, 
    evalsto m ps v res /\ ps <= ns /\
    junc (cdr m (PM_P _ H)) i (pc v) /\ 
    indist sgn (RT m sgn (pc v)) (RT m sgn (pc u')) bu bu' v u').
Proof. 
  intros.
  elim evalsto_path with (1:=H3) (2:=H6); intros.
  destruct H9 as [v [Hpath H9]].
  exists v.
  Cleanexand.
  exists x. repeat (split; auto).
  omega.
  apply indist_from_regs_heap. constructor.
  intro r.
  elim changed_dec with (m:=m) (i:=u) (j:=v) (r:=r) (p:=Hpath); intros; auto.
  constructor 1.
  apply changed_high with (m:=m) (sgn:=sgn) (H:=H) (s:=i) in H14; auto.
  apply changed_high with (m:=m) (sgn:=sgn) (H:=H) (s:=i) in H14; auto.
  elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
      (j1:=pc v) (j2:=pc u'); auto.
  (* dealing with the value when it is not changed *)
  apply not_changed_same with (m:=m) (sgn:=sgn) (i:=u) (j:=v) in H14; auto.
  Cleanexand.
  destruct high_reg_dec with (rt:=RT m sgn (pc u)) (r:=r);
  destruct high_reg_dec with (rt:=RT m sgn (pc u')) (r:=r).
  specialize H15 with (1:=H16).
  constructor 1; auto.
  constructor 1; auto.
  elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
    (j1:=pc v) (j2:=pc u'); auto.
  constructor 1; auto.
  elim junc_func with (PC:=PC) (step:=step m) (c:=cdr m (PM_P _ H)) (i:=i) 
    (j1:=pc u') (j2:=pc v); auto.
  constructor 2; auto.
  apply same_reg_val_indist1 with (s1:=u); auto.
  apply indist_reg_from_indist with (r:=r) in H8.
  destruct H8 as [HindistReg HindistRegVal]. apply HindistRegVal; auto.
  (* heap indist *)
  apply high_path_heap_indist with (m:=m) (sgn:=sgn) (i:=u) (i':=u') (H:=H)
      (Hpath:=Hpath) (s:=i); auto.
  apply indist_heap_from_indist in H8; auto.
 (* apply indist_reg_val_sym; auto.  
  apply indist_reg_val_trans with (s2:=u) (b2:=bu).*)
  (*apply indist_reg_from_indist with (r:=r) in H8.
  Cleanexand. apply indist_reg_val_sym. apply H18; auto.
  apply H14; auto.*)
  specialize H9 with (pc u'); contradiction.
Qed. 

Definition tni :=
  forall m sgn p p' s s' b b' r r' (H:P (SM m sgn)),
  pc s = pc s' ->
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s)) b b' s s' ->
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s r -> 
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p' s' r' -> 
  exists br, exists br', border b br /\ border b' br' /\
  rindist sgn br br' r r'.

Lemma tni_ni : tni -> ni.
Proof.
  unfold tni, ni; intros.
  destruct (T _ _ H0) as [T1 [T2 T3]].
  apply H with m p p' s s' H0; auto.
  rewrite T1; auto.
  apply typable_evalsto; auto.
  apply typable_evalsto; auto.
Qed.

Variable branch_indist : forall m sgn s s' u u' b b' (H:P (SM m sgn)), 
  pc s = pc s' ->
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) b b' s s' ->
  exec m s (inl u) ->
  exec m s' (inl u') ->
  pc u <> pc u' ->
  exists bu, exists bu',
    border b bu /\ border b' bu' /\
    indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) b b' u u'.

Lemma ni_ind : tni.
Proof.
  intros m sgn.
  intros ns ns'. pattern ns, ns'. apply my_double_ind.
  clear ns ns'; intros ns ns' Hind.
  intros s s' b b' r r' H Hpc Hindist Htevalsto Htevalsto'.
  set (HM:=PM_P _ H).
  inversion Htevalsto; inversion Htevalsto'.
  (* *)
  inversion H0; inversion H4.
  subst. 
  rewrite <- Hpc in H15.
  eapply indist2_return with (1:=Hindist) (5:=H11) (6:=H15); auto. 
  
  (* *)
  subst.
  apply tevalsto_diff_high_result with (s:=s) (res:=r) in Htevalsto'; auto.
  inversion Htevalsto'. 
  exists b. exists b'; split; auto.
(*   apply high_result_indist; auto.  *)
  destruct n; auto. inversion H5. omega. 
  (* *)
  subst.
  apply tevalsto_diff_high_result with (s:=s') (res:=r') in Htevalsto; auto.
  inversion Htevalsto.
  exists b. exists b'; split; auto.
(*   apply high_result_indist; auto. *)
  destruct n; auto. inversion H1. omega.
  (* *)
  inversion H0; inversion H5; subst.
  elim eq_excluded_middle with PC (pc s2) (pc s3); intros.
  (* pc s = pc s' *)
  rewrite <- Hpc in H19.
  assert (H11':=H11). 
  elim indist2_intra with (1:=Hindist) (2:=Hpc) (4:=H16) (5:=H14) (6:=H19) (3:=H11); 
    try (auto); try (rewrite <- Hpc; auto; fail).
  intros bu [bu' [V1 [V2 V3]]].
  elim Hind with (q:=n0) (p:=n) (s:=s2) (s':=s3) (r:=r) (r':=r') (H:=H) (b:=bu) (b':=bu'); 
    auto; try omega.
  intros br [br' [W1 [W2 W3]]].
  exists br; exists br'; repeat (split); auto.
  eapply border_trans; eauto.
  eapply border_trans; eauto. 
  apply sub_simple with (rt:=rt'0); auto. apply indist_sym.
  apply sub_simple with (rt:=rt'); auto.
  (* apply indist2_intra with (1:=Hindist) (2:=Hpc) (4:=H16) (5:=H14) (6:=H19) in H11; 
    try (auto); try (rewrite <- Hpc; auto; fail).
  apply Hind with (q:=n0) (p:=n) (s:=s2) (s':=s3) (r:=r) (r':=r') (H:=H); auto; try omega. 
  apply sub_simple with (rt:=rt'0).  
  apply indist_sym. inversion H11. inversion H3. 
  inversion H4. inversion H8.
  apply sub_simple with (rt:=rt'); auto.
  apply indist_sym; auto. *)
  
  rewrite H2; auto. 

  (* pc s <> pc s' *)
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s2) (pc s3); try (rewrite Hpc; auto; fail); auto; intros.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s3) (pc s2); try (rewrite Hpc; auto; fail); auto; intros.
  (* both are still in the region *)
  elim junction_indist with (m:=m) (sgn:=sgn) (ns:=n) (ns':=n0) (s:=s) (s':=s')
    (u:=s2) (u':=s3) (res:=r) (res':=r') (i:=pc s) (H:=H) (b:=b) (b':=b') (bu:=b) (bu':=b'); auto.
  intros. Cleanexand.
  assert (pc x = pc x0) as Hpcx. apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=x1) (q:=x2) (s:=x) (s':=x0) (r:=r) (r':=r') (H:=H); auto; try omega.
  rewrite <- Hpcx in H18; auto.
  apply typable_evalsto; auto.  
  apply typable_evalsto; auto.
  intros. 
  inversion H7. exists b. exists b'; split; auto. 
(*   apply high_result_indist; auto. *)
  rewrite <- Hpc; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H) (b:=b) (b':=b'); auto.
    rewrite Hpc; auto.
    unfold high_region. auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  elim branch_indist with (s:=s) (s':=s') (m:=m) (sgn:=sgn) (u:=s2) (u':=s3) (b:=b) (b':=b'); auto.
  intros b2 [b3 [Hborder1 [Hborder2 Hindist']]]; auto. rewrite <- Hpc; auto.
(*   apply branch_indist with (s:=s) (s':=s'); auto. rewrite <- Hpc; auto. *)
  (* one region one junction *)
  elim junction_indist_2 with (m:=m) (sgn:=sgn) (ns:=n0) (ns':=n) (s:=s') (s':=s)
    (u:=s3) (u':=s2) (res:=r') (res':=r) (i:=pc s) (H:=H) (b:=b') (b':=b) (bu:=b') (bu':=b); auto. 
  intros. Cleanexand.
  assert (pc x = pc s2) as Hpcx. apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=n) (q:=x0) (s:=s2) (s':=x) (r:=r) (r':=r') (H:=H); auto; try omega.
  apply indist_sym; rewrite Hpcx in H10; auto.
  apply typable_evalsto; auto.  
  apply indist_sym; rewrite <- Hpc; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H) (b:=b) (b':=b'); auto.
    rewrite Hpc; auto.
    unfold high_region; auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  elim branch_indist with (s:=s') (s':=s) (m:=m) (sgn:=sgn) (u:=s3) (u':=s2) (b:=b') (b':=b); auto.
  intros b3 [b2 [Hborder1 [Hborder2 Hindist']]]; auto. rewrite <- Hpc; auto.
  (* apply branch_indist with (s:=s') (s':=s); auto.
  apply indist_sym. rewrite <- Hpc; auto. *)
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s3) (pc s2); try (rewrite H0; auto; fail); auto; intros.
  (* one junction one region *)
  elim junction_indist_2 with (m:=m) (sgn:=sgn) (ns:=n) (ns':=n0) (s:=s) (s':=s')
    (u:=s2) (u':=s3) (res:=r) (res':=r') (i:=pc s) (H:=H) (b:=b) (b':=b') (bu:=b) (bu':=b'); auto.
  intros. Cleanexand.
  assert (pc x = pc s3) as Hpcx. apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=x0) (q:=n0) (s:=x) (s':=s3) (r:=r) (r':=r') (H:=H); auto; try omega.
  rewrite <- Hpcx in H10; auto.
  apply typable_evalsto; auto.  
  rewrite <- Hpc; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H) (b:=b) (b':=b'); auto.
    rewrite Hpc; auto.
    unfold high_region; auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  elim branch_indist with (s:=s) (s':=s') (m:=m) (sgn:=sgn) (u:=s2) (u':=s3) (b:=b) (b':=b'); auto.
  intros bu [bu' [Hborder1 [Hborder2 Hindist']]]; auto.
  rewrite <- Hpc; auto.
  (* apply branch_indist with (s:=s) (s':=s'); auto.
  rewrite <- Hpc; auto. *)
  (* both are junctions *)
  apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s) (j1:=pc s2) in H3; auto.
  contradiction.
  apply exec_step_some with (1:=PM_P _ H) in H16. rewrite Hpc; auto.
Qed.

Theorem safe_ni : forall m sgn p p' s s' b b' r r',
  P (SM m sgn) ->
  init_pc m (pc s) ->
  init_pc m (pc s') ->
  indist sgn (rt0 m sgn) (rt0 m sgn) b b' s s' ->
  pc s = pc s' ->
  evalsto m p s r -> 
  evalsto m p' s' r' -> 
  exists br, exists br',
    border b br /\
    border b' br' /\
    rindist sgn br br' r r'.
Proof.
  intros.
  apply (@ni_ind m sgn p p' s s' b b' r r' H); auto.
  destruct (T _ _ H) as [T1 _]. rewrite T1; auto.
  apply typable_evalsto; auto.
  apply typable_evalsto; auto.
Qed.

End TypableProg.
End A.