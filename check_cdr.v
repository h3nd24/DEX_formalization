(** * check_cdr.v: executable CDR checker *)
(* Hendra : Removed exception related SOAP *)
Require Export Lib.
Require Export cdr.
Require Export ZArith.

Module Make (M1:MAP) (M2:MAP).

  Module M' := MapPair_Base M1 M2.
  Module M := Map_Of_MapBase M'.
  
  Section region.
    
    Definition PC : Set := M1.key.
    Definition Kind: Set := M2.key.
    
    Variable step : PC -> Kind -> option PC -> Prop.
    Variable for_all_steps : (PC -> Kind -> option PC->bool)  -> bool.
    Variable test_all_steps : (PC -> Kind -> option PC->bool)  -> list (PC*bool).
    Variable for_all_steps_true : 
      forall test, for_all_steps test  = true ->
        forall i tau oj,
          step i tau oj -> test i tau oj = true.
    Variable for_all_succs : PC -> (Kind -> option PC -> bool) -> bool.
    Variable for_all_succs_true : forall i test,
      for_all_succs i test = true ->
      forall tau oj, step i tau oj -> test tau oj = true.
    
    Definition result p := exists k, step p k None.

    Variable reg : M.t (M1.t bool).
    Variable jun : M1.t (M2.t PC).

    Definition region (i:PC) (tau:Kind) (j:PC) : Prop :=
      exists m,
        M.get _ reg (i,tau) = Some m
        /\ M1.get m j = Some true.

    Definition junc (i:PC) (tau:Kind) (j:PC) : Prop :=
      M.get _ jun (i,tau) = Some j.
    
    Definition check_junc_func : bool :=
      M.for_all _
        (fun ikd j1 => 
          match M.get _ jun ikd with
            | None => true
            | Some j2 =>  M1.eq_key j1 j2
          end) jun.

    Lemma check_junc_func_correct : check_junc_func = true ->
      forall i j1 j2 kd,
        junc i kd j1 -> junc i kd j2 -> j1=j2.
    Proof.
      unfold check_junc_func, junc; intros.
      generalize (M.for_all_true _ _ _ H _ _ H0); simpl.
      rewrite H1; intros.
      generalize (M1.eq_key_spec j1 j2); rewrite H2; auto.    
    Qed.
    
    Definition in_region (i:PC) (tau:Kind) (j:PC) : bool :=
      match M.get _ reg (i,tau) with
        | None => false
        | Some m => match M1.get m j with
                      | Some true => true
                      | _ => false
                    end
      end.

    Lemma in_region_true : forall i tau j,
      in_region i tau j = true -> region i tau j.
    Proof.
      unfold in_region, region; intros i tau j.
      destruct (M.get (M1.t bool) reg (i, tau)); try (intros; discriminate).
      case_eq (M1.get t j); try (intros; discriminate).
      destruct b; intros; try discriminate.
      eauto.
    Qed.

    Definition test_junc (i:PC) (tau:Kind) (j:PC) : bool :=
      match M.get _ jun (i,tau) with
        | None => false
        | Some j0 => M1.eq_key j0 j
      end.

    Lemma test_junc_true : forall i tau j,
      test_junc i tau j = true -> junc i tau j.
    Proof.
      unfold test_junc, junc; intros i tau j.
      destruct (M.get _ jun (i, tau)); intros; try discriminate.
      generalize (M1.eq_key_spec p j); rewrite H; congruence.
    Qed.
    
    Definition check_soap1 : bool :=
      for_all_steps
        (fun i tau oj =>
          match oj with
            | None => true
            | Some j => orb (in_region i tau j) (test_junc i tau j)
          end).

    Definition check_soap1' : list (PC*bool) :=
      test_all_steps
        (fun i tau oj =>
          match oj with
            | None => true
            | Some j => orb (in_region i tau j) (test_junc i tau j)
          end).
        
    Lemma check_soap1_correct : check_soap1 = true ->
      forall i j kd,
        step i kd (Some j) -> 
        region i kd j \/ junc i kd j.
    Proof.
      unfold check_soap1; intros.
      assert (T:=for_all_steps_true _ H _ _ _ H0).
      elim orb_prop with (1:=T); intros.
      left; apply in_region_true; auto.
      right; apply test_junc_true; auto.
    Qed.

    Definition for_all_region (test:PC->Kind->PC->bool) : bool :=
      M.for_all _
        (fun ikd m => let (i,kd):=ikd in
           M1.for_all 
             (fun j b => (negb b) || test i kd j)
             m)
        reg.

    Lemma for_all_region_true : forall test,
      for_all_region test = true ->
      forall i tau j, region i tau j -> test i tau j = true.
    Proof.
      unfold for_all_region, region; intros.
      destruct H0 as [m [H0 H1]].
      assert (T:=M.for_all_true _ _ _ H _ _ H0).
      elim orb_prop with (1:=M1.for_all_true _ _ _ T _ _ H1); auto.
      intros; discriminate.
    Qed.

    Definition for_all_region1 (i0:PC) (test:Kind->PC->bool) : bool :=
      M.for_all _
        (fun ikd m => let (i,kd):=ikd in
           negb (M1.eq_key i0 i) ||
           M1.for_all 
             (fun j b => (negb b) || test kd j)
             m)
        reg.

    Lemma for_all_region1_true : forall i test,
      for_all_region1 i test = true ->
      forall tau j, region i tau j -> test tau j = true.
    Proof.
      unfold for_all_region1, region; intros.
      destruct H0 as [m [H0 H1]].
      assert (T:=M.for_all_true _ _ _ H _ _ H0).
      simpl in T.
      elim orb_prop with (1:=T); intros.
      generalize (M1.eq_key_spec i i); destruct (M1.eq_key i i); simpl in *; intros.
      discriminate.
      elim H3; auto.
      elim orb_prop with (1:=M1.for_all_true _ _ _ H2 _ _ H1); auto.
      intros; discriminate.
    Qed.


    Definition for_all_region2 (i:PC) (tau:Kind) (test:PC->bool) : bool :=
      match M.get _ reg (i,tau) with
        | None => true
        | Some m => M1.for_all (fun j b => b && test j) m
      end.

    Lemma for_all_region2_true : forall test i tau,
      for_all_region2 i tau test = true ->
      forall j, region i tau j -> test j = true.
    Proof.
      unfold for_all_region2, region; intros.
      destruct H0 as [m [H0 H1]].
      rewrite H0 in H.
      assert (T:=M1.for_all_true _ _ _ H _ _ H1).
      auto.
    Qed.

    Definition check_soap2 : bool := 
      for_all_region
        (fun i kd j =>
          for_all_succs j
            (fun tau ok => 
              match ok with
                | None => true
                | Some k => orb (in_region i kd k) (test_junc i kd k)
              end)).

    Lemma check_soap2_correct : check_soap2 = true ->
      forall i j k kd kd0,
        region i kd0 j-> 
        step j kd (Some k) ->
        region i kd0 k \/ junc i kd0 k.
    Proof.
      unfold check_soap2; intros.
      generalize (for_all_region_true _ H _ _ _ H0); intros T.
      elim orb_prop with (1:=for_all_succs_true _ _ T _ _ H1); intros.
      left; apply in_region_true; auto.
      right; apply test_junc_true; auto.
    Qed.

    Definition test_all_region (test:PC->Kind->PC->bool) : list (PC*Kind*PC) :=
      M.fold _ _ 
        (fun ikd m l =>
          let (i,kd):=ikd in
            M1.fold
              (fun j (b:bool) l =>
                if b then 
                  (if test i kd j then l else (i,kd,j)::l)
                  else l)
              m l)
        reg nil.

    Definition test_soap2 : list (PC*Kind*PC) := 
      test_all_region
        (fun i kd j =>
          for_all_succs j
            (fun tau ok => 
              match ok with
                | None => true
                | Some k => orb (in_region i kd k) (test_junc i kd k)
              end)).


    Definition for_all_result (test:PC->bool) : bool :=
      for_all_steps
      (fun i tau oj => 
        match oj with
          | None => test i
          | Some _ => true
        end).

    Lemma for_all_result_true : forall test, for_all_result test = true ->
      forall i, result i -> test i = true.
    Proof.
      unfold for_all_result, result; intros.
      destruct H0 as [tau H0].
      apply (for_all_steps_true _ H _ _ _ H0).
    Qed.

    Definition for_all_junc (test:PC->Kind->PC->bool) : bool :=
      M.for_all _
        (fun ikd j => let (i,kd):=ikd in
           test i kd j)
        jun.

    Lemma for_all_junc_true : forall test,
      for_all_junc test = true ->
      forall i tau j, junc i tau j -> test i tau j = true.
    Proof.
      unfold for_all_junc, junc; intros.
      apply (M.for_all_true _ _ _ H _ _ H0).
    Qed.

    Definition for_all_junc1 (i0:PC) (test:Kind->PC->bool) : bool :=
      M1.for_all 
        (fun i m => (negb (M1.eq_key i i0)) || (M2.for_all test m))
        jun.

    Lemma for_all_junc1_true : forall i test,
      for_all_junc1 i test = true ->
      forall tau j, junc i tau j -> test tau j = true.
    Proof.
      unfold for_all_junc1, junc; intros.
      unfold M.get in H0.
      unfold M'.get in H0.
      simpl in H0.
      case_eq (M1.get jun i); intros.
      rewrite H1 in H0.      
      elim orb_prop with (1:=M1.for_all_true _ _ _ H _ _ H1); intros.
      generalize (M1.eq_key_spec i i); destruct (M1.eq_key i i); intuition.
      apply (M2.for_all_true _ _ _ H2 _ _ H0).
      rewrite H1 in H0; discriminate.
    Qed.

    Definition check_soap3 : bool :=
      for_all_junc
      (fun i kd k => 
        (match M.get _ reg (i,kd) with
           | None => true
           | Some m => M1.for_all 
             (fun j b => 
               (negb b) ||
                 (for_all_succs j
                   (fun tau ok => 
                     match ok with
                       | None => false
                       | Some k => true
                     end))) m
         end)).

    Lemma check_soap3_correct : check_soap3 = true ->
      forall i j k kd, 
       region i kd j -> 
       result j -> 
       ~ junc i kd k.
    Proof.
      unfold check_soap3, region, result; red; intros.
      assert (HH:=(for_all_junc_true _ H _ _ _ H2)); clear H H2.
      destruct H0 as [m [H H2]].
      destruct H1 as [tau H1].
      simpl in HH.
      rewrite H in HH.
      elim orb_prop with (1:=M1.for_all_true _ _ _ HH _ _ H2); simpl; intros.
      discriminate.
      generalize (for_all_succs_true _ _ H0 _ _ H1); intros; discriminate.
    Qed.
(* DEX
    Definition check_soap4 : bool :=
      M1.for_all
      (fun i m => 
        M2.for_all
        (fun kd1 j1 =>
          M2.for_all 
          (fun kd2 j2 => 
            (M1.eq_key j1 j2) ||
              (in_region i kd1 j2) ||
                (in_region i kd2 j1)
          ) m) m
      ) jun.

    Lemma check_soap4_correct : check_soap4 = true ->
      forall i j1 j2 kd1 kd2,
        junc i kd1 j1 -> 
        junc i kd2 j2 -> 
        j1=j2 \/ region i kd1 j2 \/ region i kd2 j1.
    Proof.
      unfold junc, check_soap4; intros H i j1 j2 kd1 kd2.
      unfold M.get, M'.get; simpl.
      case_eq (M1.get jun i); intros; try discriminate.
      generalize (M1.for_all_true _ _ _ H _ _ H0); intros.
      generalize (M2.for_all_true _ _ _ H3 _ _ H1); intros.
      generalize (M2.for_all_true _ _ _ H4 _ _ H2); intros.
      destruct (orb_prop _ _ H5); clear H5.
      destruct (orb_prop _ _ H6); clear H6.
      left.
      generalize (M1.eq_key_spec j1 j2); rewrite H5; auto.
      right; left; apply in_region_true; auto.
      right; right; apply in_region_true; auto.
    Qed.

    Definition check_soap5 : bool :=
      for_all_junc
      (fun i kd' k => 
        (match M1.get reg i with
           | None => true
           | Some m => 
             M2.for_all
             (fun kd m' =>  
               M1.for_all 
               (fun j b =>        
                 (negb b) ||
                   (for_all_succs j
                     (fun tau ok => 
                       match ok with
                         | None => in_region i kd k
                         | Some _ => true
                       end)))
               m') m
         end)).

    Lemma check_soap5_correct : check_soap5 = true ->
      forall i j k kd kd', 
        region i kd j -> 
        result j -> 
        junc i kd' k ->
        region i kd k.
    Proof. 
      unfold check_soap5, result; intros.
      destruct H1 as [tau H1].
      generalize (for_all_junc_true _ H _ _ _ H2); clear H H2.
      intros T.
      destruct H0 as [m [Y2 Y3]].
      unfold M.get, M'.get in Y2.
      case_eq (M1.get reg i); intros; simpl in Y2; rewrite H in Y2; try discriminate.
      rewrite H in T.
      generalize (M2.for_all_true _ _ _ T _ _ Y2); clear T; intros T.
      generalize (M1.for_all_true _ _ _ T _ _ Y3); clear T; intros T.
      elim orb_prop with (1:=T); clear T; simpl.
      intros; discriminate.
      intros T; generalize (for_all_succs_true _ _ T _ _ H1).
      apply in_region_true.
    Qed.

    Definition check_soap5' : bool :=
      for_all_steps
        (fun i kd oj =>
          match oj with
            | Some _ => true
            | None => 
              (for_all_region1 i (fun kd' k => in_region i kd k))
              &&
              (for_all_junc1 i (fun kd' k => in_region i kd k))
          end).
              
    Lemma check_soap5'_correct : check_soap5' = true ->
      forall i k kd kd', 
       step i kd None ->
       (region i kd' k \/ junc i kd' k) ->
       region i kd k.
    Proof.
      unfold check_soap5'; intros.
      elim andb_prop with (1:=for_all_steps_true _ H _ _ _ H0); intros.
      destruct H1; clear H.
      apply in_region_true.
      eapply (for_all_region1_true _ _ H2); eauto.
      apply in_region_true.
      eapply (for_all_junc1_true _ _ H3); eauto.
    Qed.
*)
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
        check_soap3(*, 
        check_soap4, 
        check_soap5,
        check_soap5'*)).

    Lemma check_soap_true :
      check_soaps = true ->
      { cdr : CDR step |
        forall i tau j, cdr.region cdr i tau j -> region i tau j }.
    Proof.
      unfold check_soaps; intros; 
        repeat match goal with
                 [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
               end.
      exists (make_CDR region junc
               (check_junc_func_correct H0)
               (check_soap1_correct H3)
               (check_soap2_correct H2)
               (check_soap3_correct H1)
               (*(check_soap4_correct H3)
               (check_soap5_correct H2)
               (check_soap5'_correct H1)*)).
      simpl; auto.    
    Qed.

    Definition for_all_in_region : PC -> Kind -> (PC->bool) -> bool :=
      fun i k test =>
        match M.get _ reg (i,k) with
          | None => true
          | Some m =>
            M1.for_all (fun j b => (negb b) || test j)
            m
        end.
    Lemma for_all_in_region_correct : forall i k test,
      for_all_in_region i k test = true ->
      forall j, region i k j -> test j = true.
    Proof.
      unfold region, for_all_in_region; intros.
      destruct H0 as [m [H0 H1]].
      rewrite H0 in H.
      elim orb_prop with (1:=M1.for_all_true _ _ _ H _ _ H1); simpl; intros.
      discriminate.
      auto.
    Qed.

  End region.

End Make.
