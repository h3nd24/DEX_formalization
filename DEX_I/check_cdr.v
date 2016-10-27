(** * check_cdr.v: executable CDR checker *)
(* Hendra : Removed exception related SOAP *)
Require Export Lib.
Require Export cdr.
Require Export ZArith.

Module Make (M:MAP).

  Section region.

    Definition PC : Set := M.key.

    Variable step : PC -> option PC -> Prop.
    Variable for_all_steps : (PC -> option PC->bool)  -> bool.
    Variable test_all_steps : (PC -> option PC->bool)  -> list (PC*bool).
    Variable for_all_steps_true : 
      forall test, for_all_steps test  = true ->
        forall i oj,
          step i oj -> test i oj = true.
    Variable for_all_succs : PC -> (option PC -> bool) -> bool.
    Variable for_all_succs_true : forall i test,
      for_all_succs i test = true ->
      forall oj, step i oj -> test oj = true.
    
    Definition result p := step p None.

    Variable reg : M.t (M.t bool).
    Variable jun : M.t PC.

    Definition region (i:PC) (j:PC) : Prop :=
      exists m,
        M.get reg (i) = Some m
        /\ M.get m j = Some true.

    Definition junc (i:PC) (j:PC) : Prop :=
      M.get jun (i) = Some j.
    
    Definition check_junc_func : bool :=
      M.for_all
        (fun i j1 => 
          match M.get jun i with
            | None => true
            | Some j2 =>  M.eq_key j1 j2
          end) jun.

    Lemma check_junc_func_correct : check_junc_func = true ->
      forall i j1 j2,
        junc i j1 -> junc i j2 -> j1=j2.
    Proof.
      unfold check_junc_func, junc; intros.
      generalize (M.for_all_true _ _ _ H _ _ H0); simpl.
      rewrite H1; intros.
      generalize (M.eq_key_spec j1 j2); rewrite H2; auto.    
    Qed.
    
    Definition in_region (i:PC) (j:PC) : bool :=
      match M.get reg (i) with
        | None => false
        | Some m => match M.get m j with
                      | Some true => true
                      | _ => false
                    end
      end.

    Lemma in_region_true : forall i j,
      in_region i j = true -> region i j.
    Proof.
      unfold in_region, region; intros i j.
      destruct (M.get reg (i)); try (intros; discriminate).
      case_eq (M.get t j); try (intros; discriminate).
      destruct b; intros; try discriminate.
      eauto.
    Qed.

    Definition test_junc (i:PC) (j:PC) : bool :=
      match M.get jun (i) with
        | None => false
        | Some j0 => M.eq_key j0 j
      end.

    Lemma test_junc_true : forall i j,
      test_junc i j = true -> junc i j.
    Proof.
      unfold test_junc, junc; intros i j.
      destruct (M.get jun (i)); intros; try discriminate.
      generalize (M.eq_key_spec p j); rewrite H; congruence.
    Qed.
    
     Definition check_soap1 : bool :=
      for_all_steps
        (fun i oj =>
          for_all_steps (fun i ok =>
            match oj, ok with
              | Some j, Some k => orb (M.eq_key j k) (orb (in_region i k) (test_junc i k))
              | _, _ => false
            end)). 

    Definition check_soap1' : list (PC*bool) :=
      test_all_steps
        (fun i oj =>
          for_all_steps (fun i ok =>
          match oj, ok with
            | None, NOne => true 
            | Some j, Some k => orb (M.eq_key j k) (orb (in_region i j) (test_junc i j))
            | _, _ => false
          end)).
        
    Lemma check_soap1_correct : check_soap1 = true ->
      forall i j k,
        step i (Some j) -> step i (Some k) -> j <> k ->
        region i k \/ junc i k.
    Proof.
      unfold check_soap1; intros.
      assert (T:=for_all_steps_true _ H _ _ H0); simpl in T.
      assert (T':=for_all_steps_true _ T _ _ H1); simpl in T'.
      elim orb_prop with (1:=T'); intros.
        generalize (M.eq_key_spec j k). rewrite H3; congruence.
      elim orb_prop with (1:=H3); intros.
      left; apply in_region_true; auto.
      right; apply test_junc_true; auto.
    Qed.

    Definition for_all_region (test:PC->PC->bool) : bool :=
      M.for_all
        (fun i m => 
           M.for_all 
             (fun j b => (negb b) || test i j)
             m)
        reg.

    Lemma for_all_region_true : forall test,
      for_all_region test = true ->
      forall i j, region i j -> test i j = true.
    Proof.
      unfold for_all_region, region; intros.
      destruct H0 as [m [H0 H1]].
      assert (T:=M.for_all_true _ _ _ H _ _ H0).
      elim orb_prop with (1:=M.for_all_true _ _ _ T _ _ H1); auto.
      intros; discriminate.
    Qed.

    Definition for_all_region1 (i0:PC) (test:PC->bool) : bool :=
      M.for_all
        (fun i m => 
           negb (M.eq_key i0 i) ||
           M.for_all 
             (fun j b => (negb b) || test j)
             m)
        reg.

    Lemma for_all_region1_true : forall i test,
      for_all_region1 i test = true ->
      forall j, region i j -> test j = true.
    Proof.
      unfold for_all_region1, region; intros.
      destruct H0 as [m [H0 H1]].
      assert (T:=M.for_all_true _ _ _ H _ _ H0).
      simpl in T.
      elim orb_prop with (1:=T); intros.
      generalize (M.eq_key_spec i i); destruct (M.eq_key i i); simpl in *; intros.
      discriminate.
      elim H3; auto.
      elim orb_prop with (1:=M.for_all_true _ _ _ H2 _ _ H1); auto.
      intros; discriminate.
    Qed.


    Definition for_all_region2 (i:PC) (test:PC->bool) : bool :=
      match M.get reg (i) with
        | None => true
        | Some m => M.for_all (fun j b => b && test j) m
      end.

    Lemma for_all_region2_true : forall test i,
      for_all_region2 i test = true ->
      forall j, region i j -> test j = true.
    Proof.
      unfold for_all_region2, region; intros.
      destruct H0 as [m [H0 H1]].
      rewrite H0 in H.
      assert (T:=M.for_all_true _ _ _ H _ _ H1).
      auto.
    Qed.

    Definition check_soap2 : bool := 
      for_all_region
        (fun i j =>
          for_all_succs j
            (fun ok => 
              match ok with
                | None => true
                | Some k => orb (in_region i k) (test_junc i k)
              end)).

    Lemma check_soap2_correct : check_soap2 = true ->
      forall i j k,
        region i j-> 
        step j (Some k) ->
        region i k \/ junc i k.
    Proof.
      unfold check_soap2; intros.
      generalize (for_all_region_true _ H _ _ H0); intros T.
      elim orb_prop with (1:=for_all_succs_true _ _ T _ H1); intros.
      left; apply in_region_true; auto.
      right; apply test_junc_true; auto.
    Qed.

    Definition test_all_region (test:PC->PC->bool) : list (PC*PC) :=
      M.fold 
        (fun i m l =>
            M.fold
              (fun j (b:bool) l =>
                if b then 
                  (if test i j then l else (i,j)::l)
                  else l)
              m l)
        reg nil.

    Definition test_soap2 : list (PC*PC) := 
      test_all_region
        (fun i j =>
          for_all_succs j
            (fun ok => 
              match ok with
                | None => true
                | Some k => orb (in_region i k) (test_junc i k)
              end)).


    Definition for_all_result (test:PC->bool) : bool :=
      for_all_steps
      (fun i oj => 
        match oj with
          | None => test i
          | Some _ => true
        end).

    Lemma for_all_result_true : forall test, for_all_result test = true ->
      forall i, result i -> test i = true.
    Proof.
      unfold for_all_result, result; intros.
      apply (for_all_steps_true _ H _ _ H0).
    Qed.

    Definition for_all_junc (test:PC->PC->bool) : bool :=
      M.for_all
        (fun i j => 
           test i j)
        jun.

    Lemma for_all_junc_true : forall test,
      for_all_junc test = true ->
      forall i j, junc i j -> test i j = true.
    Proof.
      unfold for_all_junc, junc; intros.
      apply (M.for_all_true _ _ _ H _ _ H0).
    Qed.

    Definition for_all_junc1 (i0:PC) (test:PC->bool) : bool :=
      M.for_all 
        (fun i j => (negb (M.eq_key i i0)) || (test j))
        jun.

    Lemma for_all_junc1_true : forall i test,
      for_all_junc1 i test = true ->
      forall j, junc i j -> test j = true.
    Proof.
      unfold for_all_junc1, junc; intros.
      elim orb_prop with (1:=M.for_all_true _ _ _ H _ _ H0); intros; auto.
      generalize (M.eq_key_spec i i); destruct (M.eq_key i i); intuition.
    Qed.

    Definition check_soap3 : bool :=
      for_all_junc
      (fun i k => 
        (match M.get reg (i) with
           | None => true
           | Some m => M.for_all 
             (fun j b => 
               (negb b) ||
                 (for_all_succs j
                   (fun ok => 
                     match ok with
                       | None => false
                       | Some k => true
                     end))) m
         end)).

    Lemma check_soap3_correct : check_soap3 = true ->
      forall i j k, 
       region i j -> 
       result j -> 
       ~ junc i k.
    Proof.
      unfold check_soap3, region, result; red; intros.
      assert (HH:=(for_all_junc_true _ H _ _ H2)); clear H H2.
      destruct H0 as [m [H H2]].
      simpl in HH.
      rewrite H in HH.
      elim orb_prop with (1:=M.for_all_true _ _ _ HH _ _ H2); simpl; intros.
      discriminate.
      generalize (for_all_succs_true _ _ H0 _ H1); intros; discriminate.
    Qed.

    Definition check_soaps : bool :=
      check_junc_func && 
      check_soap1 && 
      check_soap2 && 
      check_soap3 (*&& 
      check_soap4 && 
      check_soap5 && 
      check_soap5'*).

    Definition check_soaps' :=
      (check_junc_func,
        check_soap1,
        check_soap2, 
        check_soap3).

    Lemma check_soap_true :
      check_soaps = true ->
      { cdr : CDR step |
        forall i j, cdr.region cdr i j -> region i j }.
    Proof.
      unfold check_soaps; intros; 
        repeat match goal with
                 [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
               end.
      exists (make_CDR step region junc
               (check_junc_func_correct H0)
               (check_soap1_correct H3)
               (check_soap2_correct H2)
               (check_soap3_correct H1)).
      simpl; auto.    
    Qed.

    Definition for_all_in_region : PC -> (PC->bool) -> bool :=
      fun i test =>
        match M.get reg (i) with
          | None => true
          | Some m =>
            M.for_all (fun j b => (negb b) || test j)
            m
        end.
    Lemma for_all_in_region_correct : forall i test,
      for_all_in_region i test = true ->
      forall j, region i j -> test j = true.
    Proof.
      unfold region, for_all_in_region; intros.
      destruct H0 as [m [H0 H1]].
      rewrite H0 in H.
      elim orb_prop with (1:=M.for_all_true _ _ _ H _ _ H1); simpl; intros.
      discriminate.
      auto.
    Qed.

  End region.

End Make.