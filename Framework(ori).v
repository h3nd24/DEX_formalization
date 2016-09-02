(*** Framework.v: Abstract framework where we prove non interference from unwindings lemmas *)
Require Export Wf_nat.
Require Export Omega.
Require Export Max.
Require Export Level.
Require Export cdr.
Require Export Axioms.
Require Export Tactics.

 Import L.

Section A.
Variable observable : L.t.

Variable PC : Set.
Variable Method : Type.
Variable Kind: Set.
Variable step : Method -> PC -> Kind -> option PC -> Prop.
Variable PM : Method -> Prop.
Variable cdr : forall m, PM m -> CDR (step m).
Implicit Arguments region.

Variable Sign : Set.

Record SignedMethod : Type := SM {unSign:Method; sign:Sign}.
Coercion unSign :  SignedMethod >-> Method.

Variable istate rstate : Type.
Variable exec : Method -> (* nat -> *) Kind -> istate -> istate+rstate -> Prop.

Variable pc : istate -> PC.

Notation "m |- p1 =>( k ) p2" := (step m p1 k (Some p2)) (at level 30). 
Notation "m |- p1 =>( k ) " := (step m p1 k None) (at level 30).
Variable exec_step_some : forall m kd s s',
  PM m -> exec m kd s (inl _ s')-> m |- (pc s) =>(kd) (pc s').
Variable exec_step_none : forall m kd s s',
  PM m -> exec m kd s (inr _ s')-> m |- (pc s) =>(kd).

Variable typeregisters : Set.
(* Variable pbij : Set. *)
Variable texec : forall m, PM m ->
      Sign -> (PC->L.t) -> PC -> Kind ->  
      typeregisters -> option typeregisters -> Prop.
(*
Variable bexec :
      Method -> Sign -> (PC->L.t) -> PC -> Kind ->  
      istate -> stacktype -> pbij -> pbij -> Prop.
*)

Variable indist : Sign -> typeregisters -> typeregisters -> istate -> istate -> Prop.
(* Variable irindist : Sign -> typeregisters -> istate -> rstate -> Prop. *)
Variable rindist : Sign -> rstate -> rstate -> Prop.
Variable indist_trans :forall m rt1 rt2 rt3 s1 s2 s3,
 indist m rt1 rt2 s1 s2 -> 
 indist m rt2 rt3 s2 s3 -> 
 indist m rt1 rt3 s1 s3.
Variable indist_sym : forall m rt1 rt2 s1 s2,
 indist m rt1 rt2 s1 s2 -> indist m rt2 rt1 s2 s1.
Variable rindist_sym : forall m s1 s2,
 rindist m s1 s2 -> rindist m s2 s1.

(* Variable indist_irindist_trans : forall m rt rt' s s' res res',
  indist m rt rt' s s' ->
  irindist m rt s res ->
  irindist m rt' s' res' ->
  rindist m res res'. *)

Variable compat : Sign -> istate -> typeregisters -> Prop.
Variable compat_res : Sign -> rstate -> Prop.

Variable high_result : Sign -> rstate -> Prop.

Variable rt0 : typeregisters.
(* Variable init : Method -> istate -> Prop. *)
Variable init_pc : Method -> PC -> Prop.
(* Variable init_init_pc : forall m s, init m s -> init_pc m (pc s). *)

(*
   Variable compat_init : forall m sgn s,
  init m s -> compat sgn s s0.
*)

(* Variable high_opstack : stacktype -> istate -> Prop. *)

(* Hendra 22082016 - focusin on DEX I
Variable side_effect : Sign -> istate -> istate+rstate -> Prop.

Variable side_effect_trans : forall m s1 s2 s3,
  side_effect m s1 (inl _ s2) ->
  side_effect m s2 s3 ->
  side_effect m s1 s3.


Inductive evalsto (m:Method) : nat -> nat -> istate -> rstate -> Prop :=
  | evalsto_res : forall n k s res,
      exec m n k s (inr _ res) -> evalsto m n 1 s res
  | evalsto_intra : forall k n n1 n2 s1 s2 res,
     exec m n1 k s1 (inl _ s2) -> 
     evalsto m n2 n s2 res ->
     evalsto m (S (n1+n2)) (S n) s1 res.
*)

Inductive evalsto (m:Method) : nat -> istate -> rstate -> Prop :=
  | evalsto_res : forall k s res,
      exec m k s (inr _ res) -> evalsto m 1 s res
  | evalsto_intra : forall k n s1 s2 res,
     exec m k s1 (inl _ s2) -> 
     evalsto m n s2 res ->
     evalsto m (S n) s1 res.

Variable P : SignedMethod -> Prop.

Variable PM_P : forall m, P m -> PM m.

Definition cmp :=
  forall m p sign s r ,
  P (SM m sign) ->
  init_pc m (pc s) -> 
  compat sign s rt0 ->
  evalsto m p s r ->
  compat_res sign r.


Variable compat_exec_intra : forall sgn m se kd s s' rt rt', 
(*   (forall k, k<n -> cmp k) -> *)
  forall H0:P (SM m sgn),
  exec m kd s (inl _ s') ->
  texec m (PM_P _ H0) sgn se (pc s) kd rt (Some rt') ->
  compat sgn s rt ->
  compat sgn s' rt'.

Variable compat_exec_return : forall sgn m se kd s r rt, 
(*   (forall k, k<n -> cmp k) -> *)
  forall H0:P (SM m sgn),
  exec m kd s (inr _ r) ->
  texec m (PM_P _ H0) sgn se (pc s) kd rt None ->
  compat sgn s rt ->
  compat_res sgn r.
(*
Definition ses N  :=
  forall m sign s r n p,
  P (SM m sign) ->
  init_pc m (pc s) -> 
  compat sign s s0 ->
  evalsto m n p s r -> n <= N ->
  side_effect sign s (inr _ r).

Variable side_effect_exec_intra : forall m sgn se n kd s1 s2 st1 st2,
  (forall k, k<n -> ses k) ->
  forall H0:P (SM m sgn),
  exec m n kd s1 (inl _ s2) -> 
  texec m (PM_P _ H0) sgn se (pc s1) kd st1 (Some st2) ->
  compat sgn s1 st1 ->
  side_effect sgn s1 (inl _ s2).

Variable side_effect_exec_return : forall m sgn se n kd s st r,
  (forall k, k<n -> ses k) ->
  forall H0:P (SM m sgn),
  exec m n kd s (inr _ r) -> 
  texec m (PM_P _ H0) sgn se (pc s) kd st None ->
  compat sgn s st ->
  side_effect sgn s (inr _ r).

Variable border : pbij -> pbij -> Prop.
Variable border_refl : forall b, border b b.
Variable border_trans : forall b1 b2 b3, 
  border b1 b2 ->
  border b2 b3 ->
  border b1 b3.


Definition ni N :=
  forall m sgn p p' n n' b b' s s' r r',
  P (SM m sgn) ->
  indist sgn s0 s0 b b' s s' ->
  pc s = pc s' ->
  init_pc m (pc s) ->
  init_pc m (pc s') ->
  evalsto m n p s r -> n <= N ->
  evalsto m n' p' s' r' -> n' <= N ->
  compat sgn s s0 ->
  compat sgn s' s0 ->
  exists br, exists br',
  border b br /\
  border b' br' /\
  rindist sgn br br' r r'.
*)

Definition ni :=
  forall m p p' sgn s s' r r',
  P (SM m sgn) ->
  indist sgn rt0 rt0 s s' ->
  pc s = pc s' ->
  init_pc m (pc s) ->
  init_pc m (pc s') ->
  evalsto m p s r ->
  evalsto m p' s' r' ->
  compat sgn s rt0 ->
  compat sgn s' rt0 ->
  rindist sgn r r'.
  
  
(* seems weird to have same rt *)
Variable indist2_intra : forall m sgn se rt ut ut' s s' u u' kd kd',
(*   (forall k, k<N -> ni k) -> *)
(*   ni ->  *)
  forall H0:P (SM m sgn), 
  indist sgn rt rt s s' ->
  pc s = pc s' ->
  exec m kd s (inl _ u) ->
  exec m kd' s' (inl _ u') ->
  texec m (PM_P _ H0) sgn se (pc s) kd rt (Some ut) ->
  texec m (PM_P _ H0) sgn se (pc s) kd' rt (Some ut') ->
  compat sgn s rt ->
  compat sgn s' rt ->
    indist sgn ut ut' u u'.

Variable indist2_return : forall m sgn se rt s s' u u' kd kd',
(*   (forall k, k<N -> ni k) -> *)
  forall H0:P (SM m sgn),
  indist sgn rt rt s s' ->
  pc s = pc s' ->
  exec m kd s (inr _ u) -> 
  exec m kd' s' (inr _ u')-> 
  texec m (PM_P _ H0) sgn se (pc s) kd rt None ->
  texec m (PM_P _ H0) sgn se (pc s) kd' rt None ->
  compat sgn s rt ->
  compat sgn s' rt ->
    rindist sgn u u'.

(* Variable indist2_intra_return : forall m sgn se rt ut s s' u u' kd kd',
(*   (forall k, k<N -> ni k) -> *)
  forall H0:P (SM m sgn),
  indist sgn rt rt s s' ->
  pc s = pc s' ->
  exec m kd s (inl _ u) -> 
  exec m kd' s' (inr _ u')-> 
  texec m (PM_P _ H0) sgn se (pc s) kd rt (Some ut) ->
  texec m (PM_P _ H0) sgn se (pc s) kd' rt None ->
  compat sgn s rt ->
  compat sgn s' rt ->
    irindist sgn ut u u'.
 *)
(*
   Variable bexec_high_se : forall m sgn se i kd s st b b',
   ~ leql (se i) observable ->
   bexec m sgn se i kd s st b b' -> b=b'.
*)

(*
Variable indist1_intra : forall m sgn se b bu st ut ut' s u u' n kd
  (H:P (SM m sgn)),
  ~ leql (se (pc u)) observable ->
  high_opstack ut u ->
  indist sgn st ut b bu s u ->
  exec m n kd u (inl _ u') ->
  texec m (PM_P _ H) sgn se (pc u) kd ut (Some ut') ->
  compat sgn u ut ->
  indist sgn st ut' b bu s u'.

Variable indist1_intra_return : forall m sgn se st ut b bu s u u' n kd
  (H:P (SM m sgn)),
  ~ leql (se (pc u)) observable ->
  high_opstack ut u ->
  indist sgn st ut b bu s u ->
  exec m n kd u (inr _ u') ->
  texec m (PM_P _ H) sgn se (pc u) kd ut None ->
  compat sgn u ut ->
  irindist sgn st b bu s u'.

Variable indist1_return_intra : forall m sgn se ut ut' b bu s u u' n kd
  (H:P (SM m sgn)),
  ~ leql (se (pc u)) observable ->
  high_opstack ut u ->
  irindist sgn ut bu b u s ->
  exec m n kd u (inl _ u') ->
  texec m (PM_P _ H) sgn se (pc u) kd ut (Some ut') ->
  compat sgn u ut ->
  irindist sgn ut' bu b u' s.

Variable indist1_return : forall m sgn se ut s u u' kd
  (H:P (SM m sgn)),
  ~ leql (se (pc u)) observable ->
(*   high_opstack ut u -> *)
  irindist sgn ut u s ->
  exec m kd u (inr _ u') ->
  texec m (PM_P _ H) sgn se (pc u) kd ut None ->
  compat sgn u ut ->
  rindist sgn u' s.

Variable opstack1: forall m sgn se st st' n k s s'
  (H:P (SM m sgn)),
  ~ leql (se (pc s)) observable ->
  high_opstack st s ->
  exec m n k s (inl _ s') -> 
  texec m (PM_P _ H) sgn se (pc s) k st (Some st') ->
  compat sgn s st ->
  high_opstack st' s'.
*)

(* high branching *)
Variable soap2_basic_intra : forall m sgn se rt ut ut' s s' u u' kd kd',
(*   (forall k, k<N -> ni k) -> *)
  forall (h:P (SM m sgn)),
  indist sgn rt rt s s' -> 
  pc s = pc s' ->
  exec m kd s (inl _ u) -> 
  exec m kd' s' (inl _ u') -> 
  texec m (PM_P _ h) sgn se (pc s) kd rt (Some ut) ->
  texec m (PM_P _ h) sgn se (pc s) kd' rt (Some ut') ->
  compat sgn s rt ->
  compat sgn s' rt ->
  pc u <> pc u' -> 
(*   high_opstack ut u /\ *)
  (forall j:PC, (region (cdr m (PM_P _ h)) (pc s) kd j) -> ~ leql (se j) observable).

Variable soap2_basic_return : forall m sgn se rt ut s s' u u' kd kd',
(*   (forall k, k<N -> ni k) -> *)
  forall (h:P (SM m sgn)),
  indist sgn rt rt s s' -> 
  pc s = pc s' ->
  exec m kd s (inl _ u) -> 
  exec m kd' s' (inr _ u') -> 
  texec m (PM_P _ h) sgn se (pc s) kd rt (Some ut) ->
  texec m (PM_P _ h) sgn se (pc s) kd' rt None ->
  compat sgn s rt ->
  compat sgn s' rt ->
(*   high_opstack ut u /\ *)
  (forall j:PC, region (cdr m (PM_P _ h)) (pc s) kd j -> ~ leql (se j) observable)
     /\  
  (forall j:PC, region (cdr m (PM_P _ h)) (pc s) kd' j -> ~ leql (se j) observable).

Variable sub : typeregisters -> typeregisters -> Prop.
(* Variable sub_high_opstack : forall st1 st2 s,
  high_opstack st1 s -> sub st1 st2 -> high_opstack st2 s. *)
(* Variable sub_double : forall sgn st1 st2 st s1 s2 b1 b2,
  indist sgn st1 st2 b1 b2 s1 s2 ->
  sub st1 st -> sub st2 st ->
  indist sgn st st b1 b2 s1 s2. *)
Variable sub_simple : forall sgn rt rt' rt0 s s0,
  indist sgn rt0 rt s0 s ->
  sub rt rt' -> (* high_opstack st s -> *)
  indist sgn rt0 rt' s0 s.
(* Variable indist_high_opstack : forall sgn st1 st2 st1' st2' b1 b2 s1 s2,
  indist sgn st1 st2 b1 b2 s1 s2 ->
  high_opstack st1' s1 ->
  high_opstack st2' s2 ->
  indist sgn st1' st2' b1 b2 s1 s2. *)
(* Variable sub_irindist : forall sgn rt rt' s1 s2,
  irindist sgn rt s1 s2 -> sub rt rt' ->
  irindist sgn rt' s1 s2. *)
Variable sub_compat : forall sgn s rt1 rt2,
  sub rt1 rt2 ->
  compat sgn s rt1 ->
  compat sgn s rt2.

Inductive typed_exec (m:Method) (H:PM m) (sgn:Sign) (se:PC->L.t) (RT:PC->typeregisters) 
: (* nat -> *) Kind -> istate -> istate + rstate -> Prop :=
  typed_exec_def1 : forall kd s1 s2 rt',
   exec m kd s1 (inl _ s2) ->
   sub rt' (RT (pc s2)) ->
   texec m H sgn se (pc s1) kd (RT (pc s1)) (Some rt') ->
   typed_exec m H sgn se RT kd s1 (inl _ s2)
| big_exec_def2 : forall kd s1 s2,
   exec m kd s1 (inr _ s2) ->
   texec m H sgn se (pc s1) kd (RT (pc s1)) None ->
   typed_exec m H sgn se RT kd s1 (inr _ s2).

Inductive tevalsto (m:Method) (H:PM m) (sgn:Sign) (se:PC->L.t) (RT:PC->typeregisters) : nat -> (* nat -> *) istate -> rstate -> Prop :=
  | tevalsto_res : forall k s res,
      typed_exec m H sgn se RT k s (inr _ res) -> tevalsto m H sgn se RT 1 s res
  | tevalsto_intra : forall k n s1 s2 res,
     typed_exec m H sgn se RT k s1 (inl _ s2) -> 
     tevalsto m H sgn se RT n s2 res ->
     tevalsto m H sgn se RT (S n) s1 res.

(* Hendra additional *)
Variable tevalsto_high_result : forall m (H:PM m) sgn se RT s res,
  ~L.leql (se (pc s)) observable ->
  tevalsto m H sgn se RT 1 s res -> high_result sgn res.

Variable step_diff_region : forall m i j kd kd' (H0:PM m), 
  step m i kd (Some j) -> step m i kd' None -> region (cdr m H0) i kd j.

Variable step_diff_region_intra : forall m i j k kd kd' (H0:PM m), 
  step m i kd (Some j) -> step m i kd' (Some k) -> 
  j <> k -> region (cdr m H0) i kd j /\ region (cdr m H0) i kd' k.

Variable tevalsto_diff_high_result : forall m sgn se RT s s' p res res' (H:PM m),
  pc s = pc s' -> 1 < p ->
  tevalsto m H sgn se RT 1 s res -> tevalsto m H sgn se RT p s' res' -> 
  high_result sgn res /\ high_result sgn res'.

Variable high_result_indist : forall sgn res res0,
  high_result sgn res -> high_result sgn res0 -> rindist sgn res res0.

Variable high_result_implies_high_result : forall m sgn p p' s s' res res' (H: P (SM m sgn)),
  evalsto m p s res ->
  evalsto m p' s' res' ->
  high_result sgn res -> high_result sgn res'.
(* *)

Definition Typable (m:Method) (H:PM m) (sgn:Sign) (se:Method->Sign->PC->L.t) (RT:Method->Sign->PC->typeregisters) : Prop :=
  (forall i, init_pc m i -> RT m sgn i = rt0) /\
  (forall i kd,
     m |- i =>(kd) ->
     texec m H sgn (se m sgn) i kd (RT m sgn i) None) /\
  (forall i j kd,
    m |- i =>(kd) j ->
    exists rt,
      texec m H sgn (se m sgn) i kd (RT m sgn i) (Some rt) 
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
  destruct H as [_ [H H0]].
  induction 1.
  (* ret *)
  constructor 1 with k; auto.
  constructor; auto.
  apply H; auto.
  eapply exec_step_none; eauto.
  (* next *)
  constructor 2 with k s2; auto.  
  elim H0 with (pc s1) (pc s2) k.
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
(*    inversion_mine H;  *)
  constructor 1 with k; auto.
(*   inversion_mine H. *)
  inversion H.
  constructor 2 with k s2; auto. 
Qed.

Implicit Arguments tevalsto_evalsto.

Definition wf_eval se RT :=
  forall m sgn s r p (H:P (SM m sgn)),
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s r ->
  compat sgn s (RT m sgn (pc s)) ->
  compat_res sgn r.

Hint Resolve PM_P.

Lemma wf_eval_cmp : forall se RT,
  TypableProg se RT ->
  wf_eval se RT ->
  cmp.
Proof.
  unfold wf_eval, cmp; intros.
  apply H0 with m s p H1; auto.
  apply typable_evalsto; auto.
  destruct (H _ _ H1) as [T1 _].
  rewrite T1; auto.
Qed.
 
Lemma wf_eval_induction : forall se RT,
  TypableProg se RT -> 
  wf_eval se RT.
Proof.
  intros se RT H.
 (*  apply lt_wf_ind; auto.
  apply lt_wf_ind; clear n; intros. *)
  unfold wf_eval.
  induction 1; intros. 
  inversion H1. subst.
  apply compat_exec_return with (2:=H7) (3:=H2); auto.
  inversion H1; subst.
  apply IHtevalsto.
  apply sub_compat with (rt1:=rt'); auto.
  apply compat_exec_intra with m (se m sgn) k s1 (RT m sgn (pc s1)) H0; auto.
Qed. 

Lemma safe_cmp : forall se RT,
  TypableProg se RT -> 
  forall m sign s r p (h:P (SM m sign)),
  init_pc m (pc s) -> 
  compat sign s rt0 ->
  evalsto m p s r ->
  compat_res sign r.
Proof.
  intros.
  generalize (wf_eval_cmp se RT); unfold cmp; intros.
  eapply H3; eauto.
  apply wf_eval_induction; auto.
Qed.

Section TypableProg.
Variable se : Method -> Sign -> PC -> L.t.
Variable RT : Method -> Sign -> PC -> typeregisters.
Variable T : TypableProg se RT.

Lemma wf_prop : forall m sgn s r p,
  P (SM m sgn) ->
  evalsto m p s r -> 
  compat sgn s (RT m sgn (pc s))->
  compat_res sgn r.
Proof.
  intros.
  apply (wf_eval_induction _ _ T m sgn s r p H); auto.
  apply typable_evalsto; auto.
Qed.

Lemma wf_step_intra : forall m sgn k s1 s2,
  P (SM m sgn) ->
  compat sgn s1 (RT m sgn (pc s1)) ->
  exec m k s1 (inl _ s2) -> 
  compat sgn s2 (RT m sgn (pc s2)).
Proof.
  intros.
  destruct (T _ _ H) as [U1 [U2 U3]].
  destruct (U3 (pc s1) (pc s2) k) as [st [P1 P2]].
  eapply exec_step_some; eauto.
  apply PM_P with (1:=H).
  apply sub_compat with st; auto.
  apply compat_exec_intra with m (se m sgn) k s1 (RT m sgn (pc s1)) H; auto.
  (* intros; apply wf_eval_cmp with se S; auto.
  apply wf_eval_induction; auto. *)
Qed.

(*
Definition tses N  :=
  forall m sgn s r (h:P (SM m sgn)),
  tevalsto m (PM_P _ h) sgn (se m sgn) (RT m sgn) s r -> 
  compat sgn s (RT m sgn (pc s)) ->
  side_effect sgn s (inr _ r).

Lemma tses_ses : forall n, tses n -> ses n.
Proof.
  unfold tses, ses; intros.
  apply H with m n0 p H0; auto.
  apply typable_evalsto; auto.
  destruct (T _ _ H0) as [T1 [T2 T3]].
  rewrite T1; auto.
Qed.

Lemma ses_induction : forall n, tses n.
Proof.
  intros n.
  apply lt_wf_ind; clear n; intros.
  unfold tses.
  induction 1; intros.
  inversion_mine H0.
  apply side_effect_exec_return with m (se m sgn) n0 k (S m sgn (pc s)) h; auto.
  intros; apply tses_ses; apply H; omega.
  inversion_mine H0; auto.
  apply side_effect_trans with s2.
  apply side_effect_exec_intra with m (se m sgn) n1 k (S m sgn (pc s1)) st' h; auto.
  intros; apply tses_ses; apply H; omega.
  apply IHtevalsto; auto; try omega.
  eapply wf_step_intra; eauto.
Qed.
*)

Definition high_region m (h:PM m) sgn (i:PC) (kd:Kind) := 
  forall j:PC, region (cdr m h) i kd j ->
    ~ leql (se m sgn j) observable.
(* Step consistent on junction point *)
(* Lemma bighighstep : forall m sgn i s0 s res ns kd
  (H:P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) -> 
  region (cdr m (PM_P _ H)) i kd (pc s)-> 
  indist sgn (RT m sgn (pc s0)) (RT m sgn (pc s)) s0 s ->
  evalsto m ns s res-> 
  high_region m (PM_P _ H) sgn i kd ->
(*   high_opstack (S m sgn (pc s)) s -> *)
  (exists u, exists ps,
    indist sgn (RT m sgn (pc s0)) (RT m sgn (pc u)) s0 u /\ 
    junc (cdr m (PM_P _ H)) i kd (pc u) /\ 
    evalsto m ps u res /\ lt ps ns /\
(*     high_opstack (S m sgn (pc u)) u /\  *)
    compat sgn u (RT m sgn (pc u))) 
  \/ 
  (exists u, high_result sgn res /\ region (cdr m (PM_P _ H)) i kd (pc u) /\ 
    result (step m) (pc u) /\ compat sgn u (RT m sgn (pc u)) )
  (*exists u, 
    irindist sgn (RT m sgn (pc s0)) s0 res /\ region (cdr m (PM_P _ H)) i kd (pc u) /\ 
    result (step m) (pc u) /\ compat sgn u (RT m sgn (pc u))*).
Proof.
 intros.
 induction H3.
 right.
 exists s; repeat split; auto.
 apply tevalsto_high_result with m (PM_P _ H) (se m sgn) (RT m sgn) s; auto.
 constructor 1 with k. constructor; auto.
 destruct (T _ _ H) as [U1 [U2 U3]]. apply U2; auto. apply exec_step_none with (s':=res) (1:=PM_P _ H); auto.
 exists k; eapply exec_step_none with (1:=PM_P _ H); eauto.
(*  eapply indist1_intra_return; eauto.
 destruct (T _ _ H) as [_ [T1 T2]].
 apply T1.
 eapply exec_step_none; eauto.
  apply PM_P with (1:=H).
 exists k; eapply exec_step_none; eauto.
  apply PM_P with (1:=H). *)
 (**)
 destruct (T _ _ H) as [_ [_ T2]].
 destruct (T2 (pc s1) (pc s2) k) as [rt [T1 T3]].
 eapply exec_step_some; eauto.
  apply PM_P with (1:=H).
(*  assert (high_opstack st s3).
 eapply opstack1; eauto. *) 
 elim soap2 with PC Kind (step m) (cdr m (PM_P _ H)) i (pc s1) (pc s2) k kd; intros; auto.
 elim IHevalsto; clear IHevalsto; auto.
 intros [u [ps [U1 [U2 [U3 [U4 U5]]]]]].
 left; exists u; exists ps; repeat split; auto; omega.
 eapply wf_step_intra; eauto.
 apply sub_simple with rt; auto.
 eapply indist1_intra with (3:=H2); eauto.
 eapply sub_high_opstack; eauto.
 left; exists s3; exists n2; exists n; repeat split; auto.
 apply sub_simple with st; auto.
 eapply indist1_intra with (3:=H2); eauto.
 omega.
 eapply sub_high_opstack; eauto.
 eapply wf_step_intra; eauto.
 eapply exec_step_some; eauto.
  apply PM_P with (1:=H).
Qed.  *)


Hint Immediate indist_sym rindist_sym.
Hint Resolve exec_step_some wf_step_intra exec_step_none.
(*  
Lemma bighighstep_with_junc :forall m sgn i s' s res n res' n' ns ns' kd kd' b' b
  (H:P (SM m sgn)),
  compat sgn s' (S m sgn (pc s')) -> 
  compat sgn s (S m sgn (pc s)) -> 
  junc (cdr m (PM_P _ H)) i kd' (pc s') -> 
  region (cdr m (PM_P _ H)) i kd (pc s)-> 
  indist sgn (S m sgn (pc s')) (S m sgn (pc s)) b' b s' s ->
  evalsto m n' ns' s' res' -> 
  evalsto m n ns s res-> 
  high_region m  (PM_P _ H) sgn i kd ->
  high_opstack (S m sgn (pc s)) s -> 
  high_region m (PM_P _ H) sgn i kd' ->
  high_opstack (S m sgn (pc s')) s' -> 
(exists t, exists t', exists p, exists p', exists ps, exists ps',
    indist sgn (S m sgn (pc t')) (S m sgn (pc t)) b' b t' t /\
    pc t = pc t' /\ 
    evalsto m p ps t res /\ le p n /\ le ps ns /\
    evalsto m p' ps' t' res' /\ le p' n' /\ le ps' ns' /\
    compat sgn t (S m sgn (pc t)) /\
    compat sgn t' (S m sgn (pc t'))) 
  \/ rindist sgn b b' res res'.
Proof.
  intros.
  elim bighighstep with m sgn i s' s res n ns kd b b' H; auto; intros; Cleanexand.
  left.
  elim eq_excluded_middle with Kind kd kd'; [intros; subst|intros].
  assert (pc x= pc s').
  eapply (junc_func (cdr m (PM_P _ H))); eauto.
  exists x; exists s'; exists x0; exists n'; exists x1; exists ns'; repeat split; auto.
  rewrite H18 in H11; auto.
  omega.
  elim soap4 with (1:=H12) (2:=H2); intros; auto.
  exists x; exists s'; exists x0; exists n'; exists x1; exists ns'; repeat split; auto.
  rewrite H19 in H11; auto.
  omega.
  destruct H19.
  elim bighighstep with m sgn i s s' res' n' ns' kd b' b H; auto; intros; Cleanexand.
  assert (pc x = pc x2).
  eapply (junc_func (cdr m (PM_P _ H))); eauto.
  exists x; exists x2; exists x0; exists x3; exists x1; exists x4; repeat split; auto.
  apply indist_trans with (S m sgn (pc s')) b' s'; auto.
  apply indist_trans with (S m sgn (pc s)) b s; auto.
  omega.
  omega.
  elim (soap3 (cdr m (PM_P _ H))) with i (pc x2) (pc x) kd; auto.
  elim bighighstep with m sgn i s' x res x0 x1 kd' b b' H; auto; intros; Cleanexand.
  assert (pc x2 = pc s').
  eapply (junc_func (cdr m (PM_P _ H))); eauto.
  exists x2; exists s'; exists x3; exists n'; exists x4; exists ns'; repeat split; auto.
  rewrite H27 in H20; auto.
  omega.
  omega.
  elim (soap3 (cdr m (PM_P _ H))) with i (pc x2) (pc s') kd'; auto.
  assert (T1:region (cdr m (PM_P _ H)) i kd (pc s')).
  apply (soap5 (cdr m (PM_P _ H))) with (pc x) kd'; auto.
  elim bighighstep with m sgn i s s'  res' n' ns' kd b' b H; auto;
  intros; Cleanexand.
  elim (soap3 (cdr m (PM_P _ H))) with i (pc x) (pc x0) kd; auto.
  right.
  eapply indist_irindist_trans; eauto.
Qed.
*)

Lemma final_bighighstep_aux : forall m sgn i p s res kd (H: P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) ->
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s res ->
  region (cdr m (PM_P _ H)) i kd (pc s) ->
  (forall jun, ~junc (cdr m (PM_P _ H)) i kd jun) ->
  high_region m (PM_P _ H) sgn i kd ->
  high_result sgn res.
Proof.
  intros.
  induction H1.
  apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se m sgn) (RT:=RT m sgn) (s:=s); auto.
    constructor 1 with (k:=k); auto.
  apply IHtevalsto; auto.
  inversion H1.
    apply sub_compat with (s:=s2) (rt1:=rt') (rt2:=RT m sgn (pc s2)); auto.
    apply compat_exec_intra with (m:=m) (se:=se m sgn) (kd:=k) (s:=s1) (s':=s2) 
      (rt:=RT m sgn (pc s1)) (rt':=rt') (H0:=H); auto.
  inversion H1. 
    eapply exec_step_some with (1:=PM_P _ H) in H7; eauto.
    elim (soap2 (cdr m (PM_P _ H))) with i (pc s1) (pc s2) k kd; auto.
    intros. unfold not in H3. apply H3 in H12. contradiction.
Qed.

Lemma final_bighighstep : forall m sgn p i s0 s res res0 kd (*kd'*)
  (H:P (SM m sgn)),
  pc s = pc s0 ->
  compat sgn s (RT m sgn (pc s)) -> 
  compat sgn s0 (RT m sgn (pc s)) ->
  evalsto m p s res-> 
  evalsto m 1 s0 res0 ->
  region (cdr m (PM_P _ H)) i kd (pc s)-> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s0)) s s0 ->
  high_region m (PM_P _ H) sgn i kd ->
(*   high_opstack (S m sgn (pc s)) s -> *)
(*   step m i kd' None ->  *)
  rindist sgn res res0.
Proof.
  intros.
  (* apply typable_evalsto with (1:=T m sgn H) in H3.
  apply typable_evalsto with (1:=T m sgn H) in H4. *)
  inversion H4; try (inversion H10).
  destruct (T m sgn H). inversion_clear H13.
  apply high_result_indist.
  (* high result res *)
    apply final_bighighstep_aux with (m:=m) (i:=i) (p:=p) (s:=s) (kd:=kd) (H:=H); auto.
    apply typable_evalsto; auto.
    intros.
    apply soap3 with (j:=pc s0).
(*     elim (soap3 (cdr m (PM_P _ H))) with i (pc s0) jun kd; auto.  *)
    rewrite <- H0; auto.
    apply exec_step_none with (1:=PM_P _ H) in H8.
    unfold result; eauto.
  (* high result res0 *)
    apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se m sgn) (RT:=RT m sgn) (s:=s0).
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

Lemma tni_aux : forall m sgn ns ns' s s' t t' res res' kd kd' (H: P (SM m sgn)),
  pc s = pc s' ->  
  exec m kd s (inl t) -> exec m kd' s' (inl t') -> 
  evalsto m ns t res ->
  evalsto m ns' t' res' ->
  pc t <> pc t' -> 
  (exists u, exists u', exists ps, exists ps', 
    evalsto m ps u res /\ ps < ns /\
    evalsto m ps' u' res' /\ ps' < ns' /\
    junc (cdr m (PM_P _ H)) (pc s) kd (pc u) /\ junc (cdr m (PM_P _ H)) (pc s') kd' (pc u'))
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) (pc s) kd jun)
  \/ (forall jun, ~junc (cdr m (PM_P _ H)) (pc s') kd' jun).
Proof.
  intros m sgn ns ns'.
  pattern ns, ns'. apply my_double_ind.
  clear ns ns'; intros ns ns' Hind; intros.
  assert (region (cdr m (PM_P _ H)) (pc s) kd (pc t0) /\ region (cdr m (PM_P _ H)) (pc s') kd' (pc t'0)).
    rewrite <- H0. apply step_diff_region_intra; auto. 
    apply exec_step_some with (1:=PM_P _ H); auto. 
    rewrite H0; apply exec_step_some with (1:=PM_P _ H); auto.
  inversion H6.
  inversion H3; inversion H4.
  (* *)
  right. right.
  apply exec_step_none with (1:=PM_P _ H) in H13.
  intros. apply soap3 with (k:=jun) in H8; auto.
  exists k0; auto.
  (* *)
  right. left.
  apply exec_step_none with (1:=PM_P _ H) in H9.
  intros. apply soap3 with (j:=pc t0) (k:=jun); auto. 
  exists k; auto.
  (* *)
  right. right.
  apply exec_step_none with (1:=PM_P _ H) in H14.
  intros. apply soap3 with (k:=jun) in H8; auto.
  exists k0; auto.
  (* *)
  subst. 
  elim Hind with (p:=n) (q:=n0) (s:=s) (s':=s') (t:=s2) (t':=s3) (res:=res) (res':=res') 
    (kd:=kd) (kd':=kd') (H:=H); auto.
  intros [U1 [U2 [ps [ps' [HS1 [HS2 [HS3 [HS4 [HS5 HS6]]]]]]]]].
  left. exists U1. exists U2. exists ps. exists ps'.
  repeat (split; auto). 
  
  

(* Lemma ind_step : forall m sgn i u u' res res' ns ns' kd kd' 
  (H:P (SM m sgn)),
  compat sgn u' (RT m sgn (pc u')) -> 
  compat sgn u (RT m sgn (pc u)) -> 
  indist sgn (RT m sgn (pc u)) (RT m sgn (pc u')) u u' ->
  evalsto m ns' u' res' -> 
  evalsto m ns u res -> 
  high_region m (PM_P _ H) sgn i kd ->
  high_region m (PM_P _ H) sgn i kd' ->
  m |- i =>(kd) (pc u) ->
  m |- i =>(kd') (pc u') ->
  (exists t, exists t', exists ps, exists ps',
    indist sgn (RT m sgn (pc t')) (RT m sgn (pc t)) t' t /\
    pc t = pc t' /\ 
    evalsto m ps t res /\ le ps ns /\
    evalsto m ps' t' res' /\ le ps' ns' /\
    compat sgn t (RT m sgn (pc t)) /\
    compat sgn t' (RT m sgn (pc t'))) 
  \/ rindist sgn res res'.
Proof.
  intros.
  Cleanexand.
  elim (soap1 (cdr m (PM_P _ H))) with i (pc u) kd;
  elim (soap1 (cdr m (PM_P _ H))) with i (pc u') kd'; intros; auto.
  induction H3; induction H4.
  
  right. apply high_result_indist. 
    apply tevalsto_high_result with m (PM_P _ H) (se m sgn) (RT m sgn) s0; auto.
      apply typable_evalsto; auto.
      constructor 1 with k0; auto.
    apply tevalsto_high_result with m (PM_P _ H) (se m sgn) (RT m sgn) s; auto.
      apply typable_evalsto; auto.
      constructor 1 with k; auto.
  right.
    apply IHevalsto.
    apply high_result_indist.
    apply final_bighighstep_aux with (m:=m) (i:=i) (p:=n) (s:=s2) (kd:=kd) (H:=H); auto.
    admit. apply typable_evalsto; auto.
    admit.
    apply tevalsto_high_result with m (PM_P _ H) (se m sgn) (RT m sgn) s; auto.
      apply typable_evalsto; auto.
      constructor 1 with k; auto.
  right. apply high_result_indist.
    apply tevalsto_high_result with m (PM_P _ H) (se m sgn) (RT m sgn) s; auto.
      apply typable_evalsto; auto.
      constructor 1 with k0; auto.
    admit.

  admit.

  intros [t0 [t'0 [ps [ps' [U1 [U2 [U3 [U4 [U5 [U6 [U7 U8]]]]]]]]]]].



  elim bighighstep with m sgn i u u'  res' n' ns' kd' b' b H; auto;
  intros; Cleanexand.
  elim bighighstep_with_junc with m sgn i x u res n res' x0 ns x1 kd kd' b' b H; auto;
  intros; Cleanexand.
  left; exists x2; exists x3; exists x4; exists x5; exists x6; exists x7; repeat split; auto.
  omega.
  omega.
  elim bighighstep with m sgn i u' u res n ns kd b b' H; auto;
  intros; Cleanexand.
  elim bighighstep_with_junc with (sgn:=sgn) (6:=H19) (7:=H3) (3:=H18) (4:=H11) (b:=b') (b':=b) (H:=H); auto; 
  intros; Cleanexand.
  left; exists x4; exists x3; exists x6; exists x5; exists x8; exists x7; repeat split; auto.
  omega.
  omega.
  right; apply rindist_sym; eapply indist_irindist_trans; eauto.
  eapply bighighstep_with_junc with (s:=u) (s':=u'); eauto.
  elim bighighstep_with_junc with (sgn:=sgn) (b:=b') (b':=b) (6:=H4) (7:=H3) (3:=H12) (4:=H11) (H:=H); auto; 
  intros; Cleanexand; eauto .
  left; exists x0; exists x; exists x2; exists x1; exists x4; exists x3; 
    repeat split; auto.
  elim soap4 with (1:=H11) (2:=H12); intros.
  left; exists u; exists u'; exists n; exists n'; exists ns; exists ns'; repeat split; auto.
  destruct H13.
  elim bighighstep_with_junc with (sgn:=sgn) (b:=b) (b':=b') (6:=H3) (7:=H4) (3:=H11) (4:=H13) (H:=H); auto; 
  intros; Cleanexand; auto.
  elim bighighstep_with_junc with (sgn:=sgn) (b:=b') (b':=b) (6:=H4) (7:=H3) (3:=H12) (4:=H13) (H:=H); auto; 
  intros; Cleanexand; auto.
  left; exists x0; exists x; exists x2; exists x1; exists x4; exists x3; 
    repeat split; auto.
Qed.  *)

(* Lemma final_bighighstep : forall m sgn p i s0 s res kd
  (H:P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) -> 
  evalsto m s res-> 
  region (cdr m (PM_P _ H)) i kd (pc s)-> 
  irindist sgn (RT m sgn (pc s)) s s0 ->
  high_region m (PM_P _ H) sgn i kd ->
(*   high_opstack (S m sgn (pc s)) s -> *)
  step m i kd None ->
  rindist sgn res s0.
Proof. *)

Definition tni :=
  forall m sgn p p' s s' r r' (H:P (SM m sgn)),
  pc s = pc s' ->
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s)) s s' ->
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s r -> 
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p' s' r' -> 
  compat sgn s (RT m sgn (pc s)) ->
  compat sgn s' (RT m sgn (pc s')) ->
(*   exists br, exists br', *)
(*   border b br /\ *)
(*   border b' br' /\ *)
  rindist sgn r r'.

Lemma tni_ni : tni -> ni.
Proof.
  unfold tni, ni; intros.
  destruct (T _ _ H0) as [T1 [T2 T3]].
  apply H with m p p' s s' H0; auto.
  rewrite T1; auto.
  apply typable_evalsto; auto.
  apply typable_evalsto; auto.
  rewrite T1; auto.
  rewrite T1; auto.
Qed.

Lemma ni_ind : tni.
Proof.
  intros m sgn.
  intros ns ns'. pattern ns, ns'. apply my_double_ind.
  clear ns ns'; intros ns ns' Hind; intros.
  set (HM:=PM_P _ H).
  inversion H2; inversion H3.
  (* *)
  inversion H6; inversion H10.
  subst. rewrite <- H0 in H23.
  rewrite <- H0 in H5.
  eapply indist2_return with (3:=H15) (5:=H18) (6:=H23) (7:=H4) (8:=H5); auto. 
  
  (* *)
  inversion H6; inversion H10; subst.
(*   rewrite H0 in H19. *)
  
  apply tevalsto_diff_high_result with (s:=s) (res:=r) in H3; auto.
  inversion H3; apply high_result_indist; auto.
  destruct n; auto. inversion H11. omega.
  (* *)
  inversion H6; inversion H10; subst.
  apply tevalsto_diff_high_result with (s:=s') (res:=r') in H2; auto.
  inversion H2; apply high_result_indist; auto.
  destruct n; auto. inversion H7. omega.
  (* *)
  inversion H6; inversion H11; subst.
  elim eq_excluded_middle with PC (pc s2) (pc s3); intros.
  (* pc s = pc s' *)
  rewrite H0 in H21.
  assert (H23':=H23). 
  apply indist2_intra with (4:=H17) (5:=H27) (6:=H21) in H23; try (auto); try (rewrite <- H0; auto; fail).
   apply Hind with (q:=n0) (p:=n) (s:=s2) (s':=s3) (r:=r) (r':=r') (H:=H); auto; try omega. 
  apply sub_simple with (rt:=rt'0).  
  apply indist_sym. apply sub_simple with (rt:=rt'); auto.
  rewrite H8; auto. 
  apply sub_compat with rt'; auto.
  apply compat_exec_intra with m (se m sgn) k s (RT m sgn (pc s)) H; auto.
  rewrite H0; auto.
  apply sub_compat with rt'0; auto.
  apply compat_exec_intra with m (se m sgn) k0 s' (RT m sgn (pc s')) H; auto.
  (* pc s <> pc s' *)
  rewrite <- H0 in H27.
  assert (H17':=H17). 
  assert (forall j : PC, region (cdr m (PM_P {| unSign := m; sign := sgn |} H)) (pc s) k j -> ~ leql (se m sgn j) observable).
    apply soap2_basic_intra with (4:=H23) (5:=H21) (6:=H27) (9:=H8) (h:=H); auto.
    rewrite H0; auto.
  
    rewrite H
  elim indist2_intra. with (3:=H23) (4:=H17) (5:=H27) (6:=H21); auto.
; auto.

  elim Hind with n0 n s2 s3 r r' H; auto; try omega.
  apply Hind with (p:=n) (q:=n0) (H:=H); auto.
  clear Hind.

  elim soap2_basic_return with (3:=H21) (4:=H16) (5:=H25) (6:=H19) (h:=H); auto.
  intros.
  apply 
  
  assert (region (cdr m HM) (pc s') k0 (pc s2)).
    apply exec_step_none with (1:=HM) in H16.
    apply exec_step_some with (1:=HM) in H21.
    rewrite H0 in H16.
    apply step_diff_region with (i:=pc s') (j:=pc s2) (kd:=k0) (kd':=k); auto.
  apply high_result_indist.
  (* high result r *) admit.
    (* apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se m sgn) (RT:=RT m sgn) (s:=s).
    auto. rewrite <- H0; auto.
    apply typable_evalsto; auto. *)
   
  (* high result r' *)
    apply final_bighighstep_aux with (m:=m) (i:=pc s') (p:=n) (s:=s2) (kd:=k0) (H:=H); auto.
    apply sub_compat with (s:=s2) (rt1:=rt') (rt2:=RT m sgn (pc s2)); auto.
    apply compat_exec_intra with (m:=m) (se:=se m sgn) (kd:=k0) (s:=s') (rt:=RT m sgn (pc s')) (H0:=H); auto.
    intros. apply soap3 with (j:=pc s).
    rewrite <- H0; auto.
    apply exec_step_none with (1:=PM_P _ H) in H8.
    unfold result; eauto. *)

  apply final_bighighstep_aux. with (m:=m) (p:=p) (i:=pc s') (s0:=
  rewrite H0 in H19.
  rewrite H0 in H4.
  elim soap2_basic_return with (3:=H21) (4:=H16) (5:=H25) (6:=H19) (7:=H5) (8:=H4) (h:=H); auto.
  intros.
  
 
  (* both are return value *)
    inversion_clear H2; inversion_clear H3.  
    apply indist2_return with (m:=m) (se:=se m sgn) (rt:=RT m sgn (pc s)) 
      (s:=s) (s':=s0) (kd:=k) (kd':=k0) (H0:=H); auto; try (rewrite H0; auto).
  (* one is return value and the other is not is an impossible case in DEX_I *)
  inversion_clear H2; inversion_clear H3.
  eapply exec_step_some in H2; try (apply PM_P with (1:=H); fail). 
  apply exec_step_none in H7; try (apply PM_P with (1:=H); fail). 
  rewrite H0 in H7. apply False_ind. contradiction.
  inversion H7.
  
  admit. admit.
  (* both are intra state *)

  intros N; apply lt_wf_ind; clear N.
  intros N HN.
  assert (HN': forall k1 : nat, k1 < N -> ni k1).
  intros; apply tni_ni; apply HN; omega.
  intros m sgn.
  intros ns ns'; pattern ns,ns'; apply my_double_ind.
  clear ns ns'; intros ns ns' Hind; intros.
  set (HM:=PM_P _ H).
  inversion_mine H2; inversion_mine H4.
  (**)
  inversion_mine H2; inversion_mine H8.
  rewrite <- H0 in H13.
  eapply indist2_return with (N:=N) (4:=H4) (6:=H9) (8:=H14) (9:=H13); auto. 
  rewrite H0; auto.
  (**)
  inversion_mine H2; inversion_mine H8.
  rewrite H0 in H16.
  elim soap2_basic_return with (N:=N) (4:=H10) (6:=H4) (8:=H15) (9:=H16) (b':=b) (b:=b') (h:=H); auto.
  intros.
  destruct H8 as [H8 V8].
  elim indist2_intra_return with (N:=N) (4:=H10) (6:=H4) (8:=H15) (9:=H16) (b:=b') (b':=b) (H0:=H); auto.
  intros bu' [bu [V1 [V2 V3]]].
  exists bu; exists bu'; repeat split; auto.
  assert (irindist sgn (S m sgn (pc s2)) bu' bu s2 r).
  eapply sub_irindist; eauto.
  assert (region (cdr m HM) (pc s) k (pc s2)).
  apply (soap5' (cdr m HM)) with k0; eauto.
  apply (soap1 (cdr m HM)); intros; auto.
  rewrite H0; eauto.
  apply rindist_sym.
  eapply final_bighighstep with (H:=H) (4:=H12); eauto.
  eapply tevalsto_evalsto; eauto.
  do 2 intro; eapply V8; eauto.
  rewrite <- H0; auto.
  rewrite <- H0; auto.
  omega.
  rewrite <- H0; auto.
  rewrite <- H0; auto.
  omega.
  rewrite <- H0; auto.
  (**)
  inversion_mine H2; inversion_mine H8.
  rewrite <- H0 in H14.
  elim soap2_basic_return with (N:=N) (4:=H4) (6:=H10) (8:=H16) (9:=H14) (b':=b') (b:=b) (h:=H); auto.
  intros.
  destruct H8 as [H8 V8].
  elim indist2_intra_return with (N:=N) (4:=H4) (6:=H10) (8:=H16) (9:=H14) (b:=b) (b':=b'); auto.
  intros bu' [bu [V1 [V2 V3]]].
  exists bu'; exists bu; repeat split; auto.
  assert (region (cdr m HM) (pc s') k0 (pc s2)).
  apply (soap5' (cdr m HM)) with k; auto.
  eauto.
  apply (soap1 (cdr m HM)); auto.
  rewrite <- H0; eauto.
  apply final_bighighstep with (H:=H) (3:=H12) (2:=tevalsto_evalsto se S H9); auto.
  eauto.
  apply sub_irindist with st'; auto.
  rewrite <- H0; auto.
  apply sub_high_opstack with st'; auto.
  eauto.
  omega.
  rewrite H0; auto.
  omega.
  rewrite H0; auto.
  (**)
  inversion_mine H2; inversion_mine H8.
  rewrite H0 in H18.
  elim indist2_intra with (N:=N) (b:=b') (b':=b) (4:=H11) (6:=H4) (8:=H16) (9:=H18); auto.
  intros bu' [bu [V1 [V2 V3]]].
  elim eq_excluded_middle with PC (pc s2) (pc s3); intros.
  elim Hind with n0 n n2 n4 bu bu' s2 s3 r r' H; auto; try omega.
  intros br' [br [W1 [W2 W3]]].
  exists br'; exists br; repeat split; auto.
  eapply border_trans; eauto.
  eapply border_trans; eauto.
  apply sub_double with st'0 st'; auto.
  rewrite H2; auto.
  eauto.
  eauto.
  rewrite <- H0 in H16;
  rewrite <- H0 in H18;
  elim soap2_basic_intra with (N:=N) (4:=H4) (6:=H11) (8:=H18) (9:=H16) (b:=b) (b':=b') (h:=H); auto.
  intros.
  rewrite H0 in H16;
  rewrite H0 in H18;
    elim soap2_basic_intra with (N:=N) (4:=H11) (6:=H4) (8:=H16) (9:=H18) (b:=b') (b':=b) (h:=H); auto.
  intros.
  elim ind_step with m sgn (pc s) s2 s3 r r' n2 n4 n0 n k k0 bu bu' H; auto.
  intros [v [v' [p [p' [ps [ps' [U1 [U2 [U3 [U4 [U5 [U6 [U7 [U8 [U9 U10]]]]]]]]]]]]]]].
  elim Hind with ps ps' p p' bu bu' v v' r r' H; auto; try omega.
  intros br [br' [W1 [W2 W3]]].
  exists br; exists br'; repeat split; auto.
  eapply border_trans; eauto.
  eapply border_trans; eauto.
  rewrite <- U2 in U1; auto.
  apply typable_evalsto; auto.
  apply typable_evalsto; auto.
  intros; exists bu; exists bu'; repeat split; auto.
  eauto.
  eauto.
  apply indist_high_opstack with st'0 st'; auto.
  apply sub_high_opstack with st'0; auto.
  apply sub_high_opstack with st'; auto.
  eapply tevalsto_evalsto; eauto.
  eapply tevalsto_evalsto; eauto.
  apply sub_high_opstack with st'0; auto.
  rewrite H0; auto.
  apply sub_high_opstack with st'; auto.
  eauto.
  rewrite H0; eauto.
  rewrite <- H0; auto.
  omega.
  omega.
  rewrite <- H0; auto.
  omega.
  omega.
  rewrite H0; auto.
  rewrite <- H0; auto.
  omega.
  omega.
  rewrite <- H0; auto.
Qed.
(* 
Theorem safe_ses : forall m sgn s r n p,
  P (SM m sgn) ->
  init_pc m (pc s) ->
  compat sgn s s0 ->
  evalsto m n p s r -> 
  side_effect sgn s (inr _ r).
Proof.
  intros.
  apply (@ses_induction n m sgn s r n p H); auto.
  apply typable_evalsto; auto.
  destruct (T _ _ H) as [T1 _]; rewrite T1; auto.
Qed.

Theorem safe_ni : forall m sgn p p' n n' s s' r r' b b',
  P (SM m sgn) ->
  init_pc m (pc s) ->
  init_pc m (pc s') ->
  compat sgn s s0 ->
  compat sgn s' s0 ->
  indist sgn s0 s0 b b' s s' ->
  pc s = pc s' ->
  evalsto m n p s r -> 
  evalsto m n' p' s' r' -> 
  exists br, exists br',
    border b br /\
    border b' br' /\
    rindist sgn br br' r r'.
Proof.
  intros.
  apply (@ni_ind (max n n') m sgn p p' n n' b b' s s' r r' H); auto.
  destruct (T _ _ H) as [T1 _]; rewrite T1; auto.
  apply typable_evalsto; auto.
  apply le_max_l.
  apply typable_evalsto; auto.
  apply le_max_r.
  destruct (T _ _ H) as [T1 _]; rewrite T1; auto.
  destruct (T _ _ H) as [T1 _]; rewrite T1; auto.
Qed. *)

End TypableProg.
End A.
