(** * Level.v: Security levels *)
(* Hendra : Added mechanism for registers typing. *)
Require Export Lib.

(** Security levels form a finite upper semilattice *)
Module Type LEVEL.
  
  Parameter t : Set.

  Parameter leql : t -> t -> Prop.
  Parameter leql_refl : forall l, leql l l.
  Parameter leql_trans : forall l1 l2 l3,
    leql l1 l2 -> leql l2 l3 -> leql l1 l3.
  Parameter eq_t : t -> t -> bool.
  Parameter eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.    
  Parameter leql_t : t -> t -> bool.
  Parameter leql_t_spec : forall x y, if leql_t x y then leql x y else ~ leql x y.    
  Parameter eq_dec : forall l l':t, {l=l'}+{~l=l'}.
  Parameter leql_dec : forall l l':t, {leql l l'}+{~leql l l'}.

  Parameter join : t -> t -> t.
  Parameter join_left : forall l l', leql l (join l l').
  Parameter join_right : forall l l', leql l' (join l l').
  Parameter join_least : forall l1 l2 l,
    leql l1 l -> leql l2 l -> leql (join l1 l2) l.

  Parameter bot : t.

  Parameter all : list t.
  Parameter all_in_all : forall k, In k all.

  (** Levels are lifted to array type *)
  Inductive t' : Set :=
  | Simple (k:t)
  | Array (k:t) (k_elem:t').

  Definition head (k:t') : t :=
    match k with
      Simple k => k
      | Array k _ => k
    end. 

  Definition elem (k:t') : option t' :=
    match k with
      Simple k => None
      | Array _ k => Some k
    end. 

  Coercion head : t' >-> t.
(*  Coercion Simple : t >-> t'. *)

  Definition join' (k1:t) (k2:t') : t' :=
    match k2 with
      Simple k => Simple (join k1 k)
      | Array k ke => Array (join k1 k) ke
    end.

  (** Subtyping between extended secrity types *)
  Inductive leql' : t' -> t' -> Prop :=
  | leql_simpl : forall k1 k2, 
    leql k1 k2 -> leql' (Simple k1) (Simple k2)
  | leal_array : forall k1 k2 ke,
    leql k1 k2 -> leql' (Array k1 ke) (Array k2 ke)
  (*| leql_simpl_array : forall k1 k2 ke, (* Hendra Addition *)
    leql k1 k2 -> leql' (Simple k1) (Array k2 ke)*).

End LEVEL.

(** We instanciate the notion of security level with a simple Low-High lattice *)
Module HighLow <: LEVEL.
  
  Inductive _t : Set := High | Low.
  Definition t : Set := _t.

  Definition leql (x y:t) : Prop := x=Low \/ x=y.
  
  Lemma leql_refl : forall l, leql l l.
  Proof.
    destruct l; unfold leql; simpl; auto.
  Qed.

  Lemma leql_trans : forall l1 l2 l3,
    leql l1 l2 -> leql l2 l3 -> leql l1 l3.
  Proof.
    unfold leql; destruct l1; intros; auto.
    right.
    destruct H; try discriminate.
    destruct H0; subst; try discriminate; auto.
  Qed.

  Definition eq_t (x y:t) : bool :=
    match x,y with
      | High,High => true
      | Low,Low => true
      | _,_ => false
    end.
  Lemma eq_t_spec : forall x y, if eq_t x y then x = y else x <> y.
  Proof.
    destruct x; destruct y; simpl; reflexivity || discriminate.
  Qed.    

  Definition leql_t (x y:t) : bool :=
    match x,y with
      | _,High => true
      | Low,_ => true
      | _,_ => false
    end.
  Lemma leql_t_spec : forall x y, if leql_t x y then leql x y else ~ leql x y.
  Proof.
    destruct x; destruct y; simpl; unfold leql; auto.
    intros [H'|H']; discriminate.
  Qed.    
  
  Lemma eq_dec : forall l l':t, {l=l'}+{~l=l'}.
  Proof (P_dec eq_t_spec).
  Lemma leql_dec : forall l l':t, {leql l l'}+{~leql l l'}.
  Proof (P_dec leql_t_spec).

  Definition join (x y:t) : t :=
    match x with
      | Low => y
      | High => High
    end.

  Lemma join_left : forall l l', leql l (join l l').
  Proof.
    destruct l; destruct l'; simpl; unfold leql; auto.
  Qed.

  Lemma join_right : forall l l', leql l' (join l l').
  Proof.
    destruct l; destruct l'; simpl; unfold leql; auto.
  Qed.

  Lemma join_least : forall l1 l2 l,
    leql l1 l -> leql l2 l -> leql (join l1 l2) l.
  Proof.
    destruct l1; destruct l2; simpl; unfold leql; auto.
  Qed.

  Definition bot : t := Low.

  Definition all : list t :=  Low :: High :: nil.
  Lemma all_in_all : forall k, In k all.
  Proof.
    destruct k; unfold all;
      auto with datatypes.
  Qed.


  Inductive t' : Set :=
  | Simple (k:t)
  | Array (k:t) (k_elem:t').

  Definition head (k:t') : t :=
    match k with
      Simple k => k
      | Array k _ => k
    end. 

  Definition elem (k:t') : option t' :=
    match k with
      Simple k => None
      | Array _ k => Some k
    end. 

  Coercion head : t' >-> t.
(*  Coercion Simple : t >-> t'. *)

  Definition join' (k1:t) (k2:t') : t' :=
    match k2 with
      Simple k => Simple (join k1 k)
      | Array k ke => Array (join k1 k) ke
    end.

  Inductive leql' : t' -> t' -> Prop :=
  | leql_simpl : forall k1 k2, 
    leql k1 k2 -> leql' (Simple k1) (Simple k2)
  | leal_array : forall k1 k2 ke,
    leql k1 k2 -> leql' (Array k1 ke) (Array k2 ke)
  (*| leql_simpl_array : forall k1 k2 ke,
    leql k1 k2 -> leql' (Simple k1) (Array k2 ke)*).

End HighLow.

(** Here we choose the security lattice for the rest of the development *)
(** The choice of the lattice does not impact the rest of the
   development but in order to typecheck our example CSFW04.v, it is
   necessary to let this module 'open'. *)
Module L <: LEVEL := HighLow.
(** We can also close the module with
   Module L : LEVEL := HighLow.
*)

Lemma eq_dec : forall l l':L.t, {l=l'}+{~l=l'}.
Proof.
  intros x y; generalize (L.eq_t_spec x y); case (L.eq_t x y); auto.
Qed.
Lemma leql_dec : forall l l':L.t, {L.leql l l'}+{~L.leql l l'}.
Proof.
  intros x y; generalize (L.leql_t_spec x y); case (L.leql_t x y); auto.
Qed.


Definition lift_st (k:L.t) (st:list L.t') : list L.t' := map (L.join' k) st.

Fixpoint lift_rec (k:L.t) (keys:list N) (rt:BinNatMap.t L.t') : BinNatMap.t L.t' :=
  match keys with
    nil => rt
    | h :: t => 
        let new_rt := BinNatMap.update _ rt h (L.Simple k) in
          lift_rec (k) (t) (new_rt)
  end.

Definition lift_rt (k:L.t) (rt:BinNatMap.t L.t') : BinNatMap.t L.t' :=
  let keys := BinNatMap.dom _ rt in lift_rec (k) (keys) (rt).

Inductive leql'_opt : option L.t' -> option L.t' -> Prop :=
| leql'_opt_none : leql'_opt None None
| leql'_opt_some : forall k1 k2,
  L.leql' k1 k2 -> leql'_opt (Some k1) (Some k2).

Definition join_op (k:L.t) (ok:option L.t') : option L.t' :=
  match ok with
    None => None
    | Some k' => Some (L.join' k k')
  end.

Definition join_op' (k:L.t) (ok:option L.t) : L.t :=
  match ok with
    None => k
    | Some k' => (L.join k k')
  end.

Definition olift_st (ok:option L.t) (st:list L.t') : list L.t' :=
  match ok with
    None => st
    | Some k => lift_st k st
  end.

Definition olift_rt (ok:option L.t) (rt:BinNatMap.t L.t') : BinNatMap.t L.t' :=
  match ok with
    None => rt
    | Some k => lift_rt k rt
  end.

Fixpoint join_list (A:Type) (r:A->L.t) (l:list A) {struct l}: L.t :=
  match l with
    nil => L.bot
    | c::q => L.join (r c) (join_list A r q)
  end.
Implicit Arguments join_list [A].

Fixpoint eql'_test (x y:L.t') {struct x} : bool :=
  match x,y with
    | L.Simple x,L.Simple y => L.eq_t x y
    | L.Array x xe,L.Array y ye => (L.eq_t x y) && (eql'_test xe ye)
    | _,_ => false
  end.

Lemma eql'_test_prop : test_bool_spec (@eq L.t') eql'_test.
Proof.
  intros x; induction x; destruct y; simpl; try discriminate.
  generalize (L.eq_t_spec k k0); case (L.eq_t k k0); congruence.
  generalize (L.eq_t_spec k k0); case (L.eq_t k k0); try congruence.
  simpl.
  generalize (IHx y); case (eql'_test x y); congruence.
Qed.

Definition leql'_test (x y:L.t') : bool :=
  match x,y with
    | L.Simple x,L.Simple y => L.leql_t x y
    | L.Array x xe,L.Array y ye => (L.leql_t x y) && (eql'_test xe ye)
    | _,_ => false
  end.


Lemma leql'_test_prop : test_bool_spec L.leql' leql'_test.
Proof.
  intros x y; destruct x; destruct y; simpl; try (intros H; inversion H; fail).
  generalize (L.leql_t_spec k k0); case (L.leql_t k k0).
  intros; constructor; auto.
  intros H1 H2; elim H1; inversion H2; subst; auto.
  generalize (L.leql_t_spec k k0); case (L.leql_t k k0); simpl; intro.
  generalize (eql'_test_prop x y); case (eql'_test x y); intros.
  subst; constructor; auto.
  intros H1; inversion_clear H1 in H H0; intuition.
  intros H2; elim H; inversion H2; subst; auto.
Qed.


Fixpoint tsub_st (l1 l2:list L.t') {struct l1} : bool :=
  match l1,l2 with
    | nil,nil => true
    | k1::q1,k2::q2 => (leql'_test k1 k2) && (tsub_st q1 q2)
    | _,_ => false
  end.

Definition tsub_element (rt1 rt2 : BinNatMap.t L.t') (reg : N) : bool :=
  match BinNatMap.get _ rt1 reg, BinNatMap.get _ rt2 reg with
    | None, None => true
    | Some k1, Some k2 => (leql'_test k1 k2)
    | None, Some k2 => false
    | Some k1, None => true
  end.

Fixpoint tsub_rec (rt1 rt2 : BinNatMap.t L.t') (regs : list N) {struct regs} : bool :=
  match regs with
    | nil => true
    | reg :: t => (tsub_element (rt1) (rt2) (reg)) && (tsub_rec (rt1) (rt2) (t))
  end.

Definition tsub_rt (rt1 rt2 : BinNatMap.t L.t') : bool :=
  let keys := BinNatMap.dom _ rt2 in tsub_rec (rt1) (rt2) (keys).
