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
Variable step : Method -> PC -> (* Kind -> *) option PC -> Prop.
Variable PM : Method -> Prop.
Variable cdr : forall m, PM m -> CDR (step m).
Implicit Arguments region.

Variable Sign : Set.

Record SignedMethod : Type := SM {unSign:Method; sign:Sign}.
Coercion unSign :  SignedMethod >-> Method.

Variable istate rstate : Type.
Variable exec : Method -> (* nat ->  Kind ->*) istate -> istate+rstate -> Prop.

Variable pc : istate -> PC.

Notation "m |- p1 => p2" := (step m p1 (* k *) (Some p2)) (at level 30). 
Notation "m |- p1 => " := (step m p1 (* k *) None) (at level 30).
Variable exec_step_some : forall m (* kd *) s s',
  PM m -> exec m (* kd *) s (inl _ s')-> m |- (pc s) => (pc s').
Variable exec_step_none : forall m (* kd *) s s',
  PM m -> exec m (* kd *) s (inr _ s')-> m |- (pc s) =>.

Variable typeregisters : Set.
(* Variable pbij : Set. *)
Variable texec : forall m, PM m ->
      Sign -> (PC->L.t) -> PC -> (* Kind ->   *)
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
  | evalsto_res : forall (* k *) s res,
      exec m (* k *) s (inr _ res) -> evalsto m 1 s res
  | evalsto_intra : forall (* k *) n s1 s2 res,
     exec m (* k *) s1 (inl _ s2) -> 
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


Variable compat_exec_intra : forall sgn m se (* kd *) s s' rt rt', 
(*   (forall k, k<n -> cmp k) -> *)
  forall H0:P (SM m sgn),
  exec m (* kd *) s (inl _ s') ->
  texec m (PM_P _ H0) sgn se (pc s) (* kd *) rt (Some rt') ->
  compat sgn s rt ->
  compat sgn s' rt'.

Variable compat_exec_return : forall sgn m se (* kd *) s r rt, 
(*   (forall k, k<n -> cmp k) -> *)
  forall H0:P (SM m sgn),
  exec m (* kd *) s (inr _ r) ->
  texec m (PM_P _ H0) sgn se (pc s) (* kd *) rt None ->
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
Variable indist2_intra : forall m sgn se rt ut ut' s s' u u' (* kd kd' *),
(*   (forall k, k<N -> ni k) -> *)
(*   ni ->  *)
  forall H0:P (SM m sgn), 
  indist sgn rt rt s s' ->
  pc s = pc s' ->
  exec m (* kd *) s (inl _ u) ->
  exec m (* kd' *) s' (inl _ u') ->
  texec m (PM_P _ H0) sgn se (pc s) (* kd *) rt (Some ut) ->
  texec m (PM_P _ H0) sgn se (pc s) (* kd' *) rt (Some ut') ->
  compat sgn s rt ->
  compat sgn s' rt ->
    indist sgn ut ut' u u'.

Variable indist2_return : forall m sgn se rt s s' u u' (* kd kd' *),
(*   (forall k, k<N -> ni k) -> *)
  forall H0:P (SM m sgn),
  indist sgn rt rt s s' ->
  pc s = pc s' ->
  exec m (* kd *) s (inr _ u) -> 
  exec m (* kd' *) s' (inr _ u')-> 
  texec m (PM_P _ H0) sgn se (pc s) (* kd *) rt None ->
  texec m (PM_P _ H0) sgn se (pc s) (* kd' *) rt None ->
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
Variable soap2_basic_intra : forall m sgn se rt ut ut' s s' u u' (* kd kd' *),
(*   (forall k, k<N -> ni k) -> *)
  forall (h:P (SM m sgn)),
  indist sgn rt rt s s' -> 
  pc s = pc s' ->
  exec m (* kd *) s (inl _ u) -> 
  exec m (* kd' *) s' (inl _ u') -> 
  texec m (PM_P _ h) sgn se (pc s) (* kd *) rt (Some ut) ->
  texec m (PM_P _ h) sgn se (pc s) (* kd' *) rt (Some ut') ->
  compat sgn s rt ->
  compat sgn s' rt ->
  pc u <> pc u' -> 
(*   high_opstack ut u /\ *)
  (forall j:PC, (region (cdr m (PM_P _ h)) (pc s) (* kd *) j) -> ~ leql (se j) observable).

Variable soap2_basic_return : forall m sgn se rt ut s s' u u' (* kd kd' *),
(*   (forall k, k<N -> ni k) -> *)
  forall (h:P (SM m sgn)),
  indist sgn rt rt s s' -> 
  pc s = pc s' ->
  exec m (* kd *) s (inl _ u) -> 
  exec m (* kd' *) s' (inr _ u') -> 
  texec m (PM_P _ h) sgn se (pc s) (* kd *) rt (Some ut) ->
  texec m (PM_P _ h) sgn se (pc s) (* kd' *) rt None ->
  compat sgn s rt ->
  compat sgn s' rt ->
(*   high_opstack ut u /\ *)
  (forall j:PC, region (cdr m (PM_P _ h)) (pc s) (* kd *) j -> ~ leql (se j) observable)
  (*    /\  
  (forall j:PC, region (cdr m (PM_P _ h)) (pc s) (* kd' *) j -> ~ leql (se j) observable) *).

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
: (* nat ->  Kind ->*) istate -> istate + rstate -> Prop :=
  typed_exec_def1 : forall (* kd *) s1 s2 rt',
   exec m (* kd *) s1 (inl _ s2) ->
   sub rt' (RT (pc s2)) ->
   texec m H sgn se (pc s1) (* kd *) (RT (pc s1)) (Some rt') ->
   typed_exec m H sgn se RT (* kd *) s1 (inl _ s2)
| big_exec_def2 : forall (* kd *) s1 s2,
   exec m (* kd *) s1 (inr _ s2) ->
   texec m H sgn se (pc s1) (* kd *) (RT (pc s1)) None ->
   typed_exec m H sgn se RT (* kd *) s1 (inr _ s2).

Inductive tevalsto (m:Method) (H:PM m) (sgn:Sign) (se:PC->L.t) (RT:PC->typeregisters) : nat -> (* nat -> *) istate -> rstate -> Prop :=
  | tevalsto_res : forall (* k *) s res,
      typed_exec m H sgn se RT (* k *) s (inr _ res) -> tevalsto m H sgn se RT 1 s res
  | tevalsto_intra : forall (* k *) n s1 s2 res,
     typed_exec m H sgn se RT (* k *) s1 (inl _ s2) -> 
     tevalsto m H sgn se RT n s2 res ->
     tevalsto m H sgn se RT (S n) s1 res.

(* Hendra additional *)
Variable tevalsto_high_result : forall m (H:PM m) sgn se RT s res,
  ~L.leql (se (pc s)) observable ->
  tevalsto m H sgn se RT 1 s res -> high_result sgn res.

Variable tevalsto_diff_high_result : forall m sgn se RT s s' p res res' (H:PM m),
  pc s = pc s' -> 1 < p ->
  tevalsto m H sgn se RT 1 s res -> tevalsto m H sgn se RT p s' res' -> 
  high_result sgn res /\ high_result sgn res'.

(* Variable tevalsto_high_result2 : forall m (H:PM m) sgn se RT s u res,
  high_region m H sgn (pc s) ->
  region (cdr m (PM_P _ H)) (pc s)  *)

Variable high_result_indist : forall sgn res res0,
  high_result sgn res -> high_result sgn res0 -> rindist sgn res res0.

(* Variable high_result_implies_high_result : forall m sgn p p' s s' res res' (H: P (SM m sgn)),
  evalsto m p s res ->
  evalsto m p' s' res' ->
  high_result sgn res -> high_result sgn res'. *)
(* *)

Definition Typable (m:Method) (H:PM m) (sgn:Sign) (se:Method->Sign->PC->L.t) (RT:Method->Sign->PC->typeregisters) : Prop :=
  (forall i, init_pc m i -> RT m sgn i = rt0) /\
  (forall i (* kd *),
     m |- i =>(*kd*) ->
     texec m H sgn (se m sgn) i (* kd *) (RT m sgn i) None) /\
  (forall i j (* kd *),
    m |- i =>(*kd*) j ->
    exists rt,
      texec m H sgn (se m sgn) i (* kd *) (RT m sgn i) (Some rt) 
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
  constructor 1 (* with k *); auto.
  constructor; auto.
  apply H; auto.
  eapply exec_step_none; eauto.
  (* next *)
  constructor 2 with (* k *) s2; auto.  
  elim H0 with (pc s1) (pc s2) (* k *).
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
  constructor 1 (* with k *); auto.
(*   inversion_mine H. *)
  inversion H.
  constructor 2 with (* k *) s2; auto. 
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
  apply compat_exec_return with (2:=H6) (3:=H2); auto.
  inversion H1; subst.
  apply IHtevalsto.
  apply sub_compat with (rt1:=rt'); auto.
  apply compat_exec_intra with m (se m sgn) (* k  *)s1 (RT m sgn (pc s1)) H0; auto.
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

Definition high_region m (h:PM m) sgn (i:PC) (*kd:Kind*) := 
  forall j:PC, region (cdr m h) i (* kd *) j ->
    ~ leql (se m sgn j) observable.

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

Lemma wf_step_intra : forall m sgn (* k *) s1 s2,
  P (SM m sgn) ->
  compat sgn s1 (RT m sgn (pc s1)) ->
  exec m (* k *) s1 (inl _ s2) -> 
  compat sgn s2 (RT m sgn (pc s2)).
Proof.
  intros.
  destruct (T _ _ H) as [U1 [U2 U3]].
  destruct (U3 (pc s1) (pc s2) (* k *)) as [rt [P1 P2]].
  eapply exec_step_some; eauto.
  apply PM_P with (1:=H).
  apply sub_compat with rt; auto.
  apply compat_exec_intra with m (se m sgn) (* k *) s1 (RT m sgn (pc s1)) H; auto.
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

Lemma final_bighighstep_aux : forall m sgn i p s res (* kd *) (H: P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) ->
  tevalsto m (PM_P _ H) sgn (se m sgn) (RT m sgn) p s res ->
  region (cdr m (PM_P _ H)) i (* kd *) (pc s) ->
  (forall jun, ~junc (cdr m (PM_P _ H)) i (* kd *) jun) ->
  high_region m (PM_P _ H) sgn i (* kd *) ->
  high_result sgn res.
Proof.
  intros.
  induction H1.
  apply tevalsto_high_result with (m:=m) (H:=(PM_P _ H)) (se:=se m sgn) (RT:=RT m sgn) (s:=s); auto.
    constructor 1 (* with (k:=k) *); auto.
  apply IHtevalsto; auto.
  inversion H1.
    apply sub_compat with (s:=s2) (rt1:=rt') (rt2:=RT m sgn (pc s2)); auto.
    apply compat_exec_intra with (m:=m) (se:=se m sgn) (*kd:=k*) (s:=s1) (s':=s2) 
      (rt:=RT m sgn (pc s1)) (rt':=rt') (H0:=H); auto.
  inversion H1. 
    eapply exec_step_some with (1:=PM_P _ H) in H7; eauto.
    elim (soap2 (cdr m (PM_P _ H))) with i (pc s1) (pc s2) (* k  kd*); auto.
    intros. unfold not in H3. apply H3 in H11. contradiction.
Qed.

Lemma final_bighighstep : forall m sgn p i s0 s res res0 (*kd kd'*)
  (H:P (SM m sgn)),
  pc s = pc s0 ->
  compat sgn s (RT m sgn (pc s)) -> 
  compat sgn s0 (RT m sgn (pc s)) ->
  evalsto m p s res-> 
  evalsto m 1 s0 res0 ->
  region (cdr m (PM_P _ H)) i (* kd  *) (pc s)-> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s0)) s s0 ->
  high_region m (PM_P _ H) sgn i (* kd *) ->
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
    apply final_bighighstep_aux with (m:=m) (i:=i) (p:=p) (s:=s) (*kd:=kd*) (H:=H); auto.
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
 

Variable junction_indist : forall m sgn ns ns' s s' u u' res res' i (H: P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) -> compat sgn s' (RT m sgn (pc s')) -> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) s s' ->
  exec m s (inl u) -> exec m s' (inl u') ->
  region (cdr m (PM_P _ H)) i (pc u) ->
  region (cdr m (PM_P _ H)) i (pc u') ->
  high_region m (PM_P _ H) sgn i ->
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  (exists v, exists v', exists ps, exists ps', 
    evalsto m ps v res /\ ps <= ns /\
    evalsto m ps' v' res' /\ ps' <= ns' /\
    junc (cdr m (PM_P _ H)) i (pc v) /\ 
    junc (cdr m (PM_P _ H)) i (pc v') /\
    compat sgn v (RT m sgn (pc v)) /\ compat sgn v' (RT m sgn (pc v')) 
    /\ indist sgn (RT m sgn (pc v)) (RT m sgn (pc v')) v v')
  \/ (high_result sgn res /\ high_result sgn res'). 

Variable junction_indist_2 : forall m sgn ns ns' s s' u u' res res' i (H: P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) -> compat sgn s' (RT m sgn (pc s')) -> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) s s' ->
  exec m s (inl u) -> exec m s' (inl u') ->
  region (cdr m (PM_P _ H)) i (pc u) ->
  junc (cdr m (PM_P _ H)) i (pc u') ->
  high_region m (PM_P _ H) sgn i ->
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  (exists v, exists ps, 
    evalsto m ps v res /\ ps <= ns /\
    junc (cdr m (PM_P _ H)) i (pc v) /\ 
    compat sgn v (RT m sgn (pc v)) /\ 
    indist sgn (RT m sgn (pc v)) (RT m sgn (pc u')) v u').  

(* Lemma junction_indist_1_helper : forall m sgn ns s u rt v rtv res (H: P (SM m sgn)), *)
(* 
Lemma execution_indist : forall m sgn ns ns' s s' u u' res res' i (H: P (SM m sgn)),
  compat sgn s (RT m sgn (pc s)) -> compat sgn s' (RT m sgn (pc s')) -> 
  indist sgn (RT m sgn (pc s)) (RT m sgn (pc s')) s s' ->
  exec m s (inl u) -> exec m s' (inl u') ->
  region (cdr m (PM_P _ H)) i (pc u) ->
  region (cdr m (PM_P _ H)) i (pc u') ->
  high_region m (PM_P _ H) sgn i ->
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  (exists v, exists v', exists ps, exists ps', exists rtv, exists rtv', 
    evalsto m ps v res /\ ps <= ns /\
    evalsto m ps' v' res' /\ ps' <= ns' /\
    junc (cdr m (PM_P _ H)) i (pc v) /\ 
    junc (cdr m (PM_P _ H)) i (pc v') /\
    compat sgn v rtv /\ compat sgn v' rtv' /\ indist sgn rtv rtv' v v')
  \/ (high_result sgn res /\ high_result sgn res').
Proof.
  intros m sgn ns ns'.
  pattern ns, ns'; apply my_double_ind.
  clear ns ns'; intros ns ns' Hind; intros.
  apply typable_evalsto with (1:=(T m sgn) H) (se:=se) (RT:=RT) (sgn:=sgn) in H8.
  apply typable_evalsto with (1:=(T m sgn) H) (se:=se) (RT:=RT) (sgn:=sgn) in H9.
  assert (H3':=H3); assert (H4':=H4).
  apply exec_step_some with (1:=PM_P _ H) in H4.
  apply exec_step_some with (1:=PM_P _ H) in H3.
  destruct ((T m sgn) H). Cleanexand.
  apply H12 in H4; apply H12 in H3. Cleanexand.
  (* applying the compat_exec_intras to get u and u' register types *)
  assert (compat sgn u (RT m sgn (pc u))). 
    apply compat_exec_intra with (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s)) (rt':=x0) (H0:=H) in H3'; auto.
    apply sub_compat with (rt2:=RT m sgn (pc u)) (rt1:=x0); auto.
  assert (compat sgn u' (RT m sgn (pc u'))). 
    apply compat_exec_intra with (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s')) (rt':=x) (H0:=H) in H4'; auto.
    apply sub_compat with (rt2:=RT m sgn (pc u')) (rt1:=x); auto.  
  (* (* determine whether u and u' are in the region or junction points *)
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc u) (pc u'); try (rewrite H0; auto; fail); auto; intros.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc u') (pc u); try (rewrite H0; auto; fail); auto; intros. *)
  inversion_mine H8; inversion_mine H9.
  (* both are return value *)
  right. split.
  apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u); auto.
      constructor; auto.
  apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u'); auto.
      constructor; auto.
  (* one is return value one is not *)
  right. split.
  apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u); auto.
      constructor; auto.
  apply final_bighighstep_aux with (m:=m) (i:=i) (p:=S n) (s:=u') (H:=H) (res:=res') in H16; auto.
      constructor 2 with (s2:=s2); auto.
      intros.
      apply soap3 with (j:=pc u); auto. inversion H17. apply exec_step_none with (1:=PM_P _ H) in H19; auto.
  (* one is not, one is return value *)    
  right. split.
  apply final_bighighstep_aux with (m:=m) (i:=i) (p:=S n) (s:=u) (H:=H) (res:=res) in H15; auto.
      constructor 2 with (s2:=s2); auto.
      intros.
      apply soap3 with (j:=pc u'); auto. inversion H8. apply exec_step_none with (1:=PM_P _ H) in H19; auto.
  apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u'); auto.
      constructor; auto.
  (* both are not return value *)
  elim soap2 with PC (step m) (cdr m (PM_P _ H)) i (pc u) (pc s2); 
  elim soap2 with PC (step m) (cdr m (PM_P _ H)) i (pc u) (pc s0); intros; auto.
  (* both successors are in the region *)
  elim Hind with (p:=n) (q:=n0) (s:=u) (s':=u') (u:=s2) (u':=s0) (res:=res) (res':=res') (H:=H) (i:=i); auto.
  intros [v [v' [ps [ps' [rtv [rtv'[iH1 [iH2 [iH3 [iH4 [iH5 [iH6 [iH7 [iH8 iH9]]]]]]]]]]]]]].
  left. exists v; exists v'; exists ps; exists ps'; exists rtv; exists rtv'; auto.
  repeat (split; auto).
  admit.
  (* exec u v *)
  inversion H17; auto.
  inversion H8; auto.
  (* *)
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  (* one junction and one region *)
  (* apply execution_reach_junction_or_return_1 with (ns:=n) (res:=res) in H20; auto.
  inversion_mine H20.
  destruct H21 as [v [ps [iH1 [iH2 iH3]]]].
  
  apply Hind with (p:=n) (q:=n0) (s:=u) (s':=u') (u:=s2) (u':=s0) (res:=res) (res':=res') (i:=i) (H:=H) in H15.  *)
  
  elim Hind with (p:=n) (q:=n0) (s:=u) (s':=u') (u:=s2) (u':=s0) (res:=res) (res':=res') (H:=H) (i:=i); auto.
  intros [v [v' [ps [ps' [rtv [rtv'[iH1 [iH2 [iH3 [iH4 [iH5 [iH6 [iH7 [iH8 iH9]]]]]]]]]]]]]].
  assert (compat sgn s0 (RT m sgn (pc s0))). 
    inversion H8.
    apply compat_exec_intra with (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc u')) (rt':=rt') (H0:=H) in H22; auto.
    apply sub_compat with (rt2:=RT m sgn (pc s0)) (rt1:=rt'); auto.  
  left. exists v; exists s0; exists ps; exists n0; exists rtv; exists (RT m sgn (pc s0)); auto.
  repeat (split; auto).
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  admit.
  inversion H17; auto. inversion H8; auto.
  (* *)
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.

(* u and u' in the region *)
    (* both are return value, and u and u' in the region *)
    right.
    split.
      (* res is a high result *)
      assert (forall j, region (cdr m (PM_P {| unSign := m; sign := sgn |} H)) (pc s) j -> ~ leql (se m sgn j) observable).
        apply soap2_basic_intra with (m:=m) (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s)) (ut:=x) (ut':=x0) (s:=s) (s':=s') 
          (u:=u) (u':=u') (h:=H); auto.
        rewrite <- H0 in H3; auto. rewrite H0; auto. rewrite H0; auto.
      apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u); auto.
      constructor; auto.
      (* res' is a high result *)
      assert (forall j, region (cdr m (PM_P {| unSign := m; sign := sgn |} H)) (pc s') j -> ~ leql (se m sgn j) observable).
        apply soap2_basic_intra with (m:=m) (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s)) (ut:=x0) (ut':=x) (s:=s') (s':=s) 
          (u:=u') (u':=u) (h:=H); auto.
        rewrite <- H0 in H3; auto. rewrite H0; auto. rewrite <- H0; auto. rewrite H0; auto.
      rewrite H0; auto. rewrite <- H0 in H8. 
      apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u'); auto.
      constructor; auto.
    (* u is a return value, u' is not*)
    right.
    split.
    (* res is a high result *)
      assert (forall j, region (cdr m (PM_P {| unSign := m; sign := sgn |} H)) (pc s) j -> ~ leql (se m sgn j) observable).
        apply soap2_basic_intra with (m:=m) (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s)) (ut:=x) (ut':=x0) (s:=s) (s':=s') 
          (u:=u) (u':=u') (h:=H); auto.
        rewrite <- H0 in H3; auto. rewrite H0; auto. rewrite H0; auto.
      apply tevalsto_high_result with (m:=m) (H:=PM_P _ H) (se:=se m sgn) (RT:=RT m sgn) (s:=u); auto.
      constructor; auto.
    (* res' is a high result *)
      assert (forall j, region (cdr m (PM_P {| unSign := m; sign := sgn |} H)) (pc s') j -> ~ leql (se m sgn j) observable).
        apply soap2_basic_intra with (m:=m) (sgn:=sgn) (se:=se m sgn) (rt:=RT m sgn (pc s)) (ut:=x0) (ut':=x) (s:=s') (s':=s) 
          (u:=u') (u':=u) (h:=H); auto.
        rewrite <- H0 in H3; auto. rewrite H0; auto. rewrite <- H0; auto. rewrite H0; auto.
        rewrite H0; auto.
      apply final_bighighstep_aux with (m:=m) (i:=pc s) (p:=S n) (s:=u') (H:=H) (res:=res') in H15; auto.
      constructor 2 with (s2:=s2); auto.
      intros.
      apply soap3 with (j:=pc u); auto. inversion H18. apply exec_step_none with (1:=PM_P _ H) in H21; auto.
      rewrite H0; auto.
    (* u is not, and u' is return value. adjust from previous one. *)
    admit.
    (* u and u' are not return value *)
    elim Hind with (p:=n) (q:=n0) (u:=s2) (u':=s0) (res:=res) (res':=res') (H:=H); auto.
    
  (* both are in region, but both are return value *)
  elim (soap3 (cdr m (PM_P _ H))) with (i:=pc s) (j:=pc u) (k:=pc v'); auto. *)

(* 
Lemma junction_indist_1 : forall m sgn s s' rt rt' u u' ns ns' k 
    ps ps' v v' rtv rtv' res res' (H: P (SM m sgn)),
  ((ns - ps) + (ns' - ps') <= k) ->
  pc s = pc s' ->  
  exec m s (inl u) -> exec m s' (inl u') -> 
  compat sgn s rt -> compat sgn s' rt' -> 
  indist sgn rt rt' s s' ->
  region (cdr m (PM_P _ H)) (pc s) (pc u) ->
  region (cdr m (PM_P _ H)) (pc s') (pc u') -> 
  evalsto m ns u res ->
  evalsto m ns' u' res' ->
  junc (cdr m (PM_P _ H)) (pc s) (pc v) -> 
  junc (cdr m (PM_P _ H)) (pc s') (pc v') ->
  compat sgn v rtv -> 
  compat sgn v' rtv' -> 
  evalsto m ps v res -> ps < ns ->
  evalsto m ps' v' res' -> ps' < ns' ->
  indist sgn rtv rtv' v v'.
Proof.
  intros m sgn s s' rt rt' u u' ns ns' k.
  pattern k. apply lt_wf_ind.
  clear k; intros k Hind; intros.
  (* (* base case *)
  assert (ns = ps /\ ns' = ps').
    apply Nat.le_0_r in H0.
    assert (forall (a b:nat), (a + b)%nat = 0 -> a = 0 /\ b = 0). intros; omega. 
    apply H19 in H0. inversion H0.
    assert (forall (a b:nat), (a - b) = 0 -> a = b). intros; omega.
    split; auto.
  Cleanexand. apply False_ind; omega. *)
  (* induction case *)
  intros.
(*   assert (forall n, n < n -> False). intros; omega.  *)
(*   assert (forall n, S n < 1 -> False). intros; omega. *)
  inversion_mine H9; inversion_mine H10.
(*   inversion H9; inversion H10; subst. *)
  apply exec_step_none with (1:=PM_P _ H) in H19.
  elim (soap3 (cdr m (PM_P _ H))) with (i:=pc s) (j:=pc u) (k:=pc v); auto.
  apply exec_step_none with (1:=PM_P _ H) in H19.
  elim (soap3 (cdr m (PM_P _ H))) with (i:=pc s) (j:=pc u) (k:=pc v); auto.
  apply exec_step_none with (1:=PM_P _ H) in H9.
  elim (soap3 (cdr m (PM_P _ H))) with (i:=pc s) (j:=pc u') (k:=pc v'); auto.
    rewrite H1; auto. rewrite H1; auto.
  apply Hind with (m0:=((S n - ps) + (n0 - ps'))%nat) (H:=H) (res:=res) (res':=res')
    (ps:=ps) (ps':=ps'); auto. omega. 
  admit. auto.
  admit.
  admit. admit.
   *)

(* Lemma junction_indist : forall m sgn ns ns' s s' u u' rt rt' res res' (H: P (SM m sgn)),
  pc s = pc s' ->
  exec m s (inl u) -> exec m s' (inl u') -> 
  compat sgn s rt -> compat sgn s' rt' -> 
  indist sgn rt rt' s s' ->
  pc u <> pc u' -> 
  evalsto m ns u res -> evalsto m ns' u' res' ->
  (exists v, exists v', exists rtv, exists rtv', exists ps, exists ps', 
    evalsto m ps v res /\ ps <= ns /\
    evalsto m ps' v' res' /\ ps' <= ns' /\
    compat sgn v rtv /\ compat sgn v' rtv' /\
    indist sgn rtv rtv' v v')
  \/ (high_result sgn res /\ high_result sgn res').
Proof. 
  intros m sgn.
  intros ns ns'. pattern ns, ns'. apply my_double_ind.
  clear ns ns'; intros ns ns' Hind; intros.
  inversion H7; inversion H8; subst.
  (* both are return value *)
  right. split; auto. *)
  

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
  subst. rewrite <- H0 in H21.
  rewrite <- H0 in H5.
  eapply indist2_return with (3:=H15) (5:=H17) (6:=H21) (7:=H4) (8:=H5); auto. 
  
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
  rewrite H0 in H20.
  assert (H22':=H22). 
  apply indist2_intra with (4:=H17) (5:=H25) (6:=H20) in H22; try (auto); try (rewrite <- H0; auto; fail).
   apply Hind with (q:=n0) (p:=n) (s:=s2) (s':=s3) (r:=r) (r':=r') (H:=H); auto; try omega. 
  apply sub_simple with (rt:=rt'0).  
  apply indist_sym. apply sub_simple with (rt:=rt'); auto.
  rewrite H8; auto. 
  apply sub_compat with rt'; auto.
  apply compat_exec_intra with m (se m sgn) s (RT m sgn (pc s)) H; auto.
  rewrite H0; auto.
  apply sub_compat with rt'0; auto.
  apply compat_exec_intra with m (se m sgn) s' (RT m sgn (pc s')) H; auto.
  (* pc s <> pc s' *)
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s2) (pc s3); try (rewrite H0; auto; fail); auto; intros.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s3) (pc s2); try (rewrite H0; auto; fail); auto; intros.
  (* both are still in the region *)
  elim junction_indist with (m:=m) (sgn:=sgn) (ns:=n) (ns':=n0) (s:=s) (s':=s')
    (u:=s2) (u':=s3) (res:=r) (res':=r') (i:=pc s) (H:=H); auto.
  intros. Cleanexand.
  assert (pc x = pc x0). apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=x1) (q:=x2) (s:=x) (s':=x0) (r:=r) (r':=r') (H:=H); auto; try omega.
  rewrite <- H28 in H27; auto.
  apply typable_evalsto; auto.  
  apply typable_evalsto; auto.
  intros. inversion H13; apply high_result_indist; auto.
  rewrite <- H0; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H); auto.
    rewrite H0; auto.
    rewrite H0; auto.
  auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  (* one region one junction *)
  elim junction_indist_2 with (m:=m) (sgn:=sgn) (ns:=n0) (ns':=n) (s:=s') (s':=s)
    (u:=s3) (u':=s2) (res:=r') (res':=r) (i:=pc s) (H:=H); auto.
  intros. Cleanexand.
  assert (pc x = pc s2). apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=n) (q:=x0) (s:=s2) (s':=x) (r:=r) (r':=r') (H:=H); auto; try omega.
  apply indist_sym; rewrite H21 in H19; auto.
  apply typable_evalsto; auto.  
  apply compat_exec_intra with (m:=m) (se:=se m sgn) (s':=s2) (rt':=rt') (H0:=H) in H4; auto.
  apply sub_compat with (rt1:=rt'); auto.
  apply indist_sym; rewrite <- H0; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H); auto.
    rewrite H0; auto.
    rewrite H0; auto.
  auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  elim (soap1 (cdr m (PM_P _ H))) with (pc s) (pc s3) (pc s2); try (rewrite H0; auto; fail); auto; intros.
  (* one junction one region *)
  elim junction_indist_2 with (m:=m) (sgn:=sgn) (ns:=n) (ns':=n0) (s:=s) (s':=s')
    (u:=s2) (u':=s3) (res:=r) (res':=r') (i:=pc s) (H:=H); auto.
  intros. Cleanexand.
  assert (pc x = pc s3). apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s); auto.
  apply Hind with (p:=x0) (q:=n0) (s:=x) (s':=s3) (r:=r) (r':=r') (H:=H); auto; try omega.
  rewrite <- H21 in H19; auto.
  apply typable_evalsto; auto.  
  apply compat_exec_intra with (m:=m) (se:=se m sgn) (s':=s3) (rt':=rt'0) (H0:=H) in H5; auto.
  apply sub_compat with (rt1:=rt'0); auto.
  rewrite <- H0; auto.
  assert ((forall j:PC, (region (cdr m (PM_P _ H)) (pc s) j) -> ~ leql (se m sgn j) observable)).
    intros. apply soap2_basic_intra with (m:=m) (sgn:=sgn) (rt:=RT m sgn (pc s)) 
      (ut:=rt') (ut':=rt'0) (s:=s) (s':=s') (u:=s2) (u':=s3) (h:=H); auto.
    rewrite H0; auto.
    rewrite H0; auto.
  auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  apply tevalsto_evalsto with (se:=se) (RT:=RT) (sgn:=sgn) (h:=PM_P _ H); auto.
  (* both are junctions *)
  apply junc_func with (step:=step m) (c:=cdr m (PM_P _ H)) (i:=pc s) (j1:=pc s2) in H9; auto.
  contradiction.
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
