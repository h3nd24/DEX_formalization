(** typing_rules.v: Typing rules, plus an executable type checker *)
(* Hendra : - Modified to suit DEX program. 
            - DEX has different instructions list from JVM.
            - Also trim the system to contain only Arithmetic *)
Require Export DEX_BigStepAnnot.
Require Export Bool.
Require Export DEX_step.
Import DEX_BigStep.DEX_BigStep DEX_Dom.DEX_Prog.

Import Level.L.
Import DEX_Dom.

Open Scope type_scope.

  Section DEX_typing_rules.   (** Typing rules **)
    Variable m : DEX_Method.
    Variable sgn : DEX_sign.
    Variable region : DEX_PC -> DEX_PC -> Prop.
    Variable se : DEX_PC -> L.t.
    Variable selift : DEX_PC -> L.t -> bool. 
    Variable ret : DEX_Reg.

    Infix "<=" := L.leql (at level 70).
    Infix "<='" := L.leql' (at level 70).
    Infix "U'" := L.join' (at level 60, right associativity).
    Infix "U" := L.join (at level 60, right associativity).

    Inductive texec : DEX_PC -> DEX_Instruction -> TypeRegisters -> option TypeRegisters -> Prop :=
    | DEX_nop : forall i rt,
      texec i DEX_Nop rt (Some rt)

    | DEX_move : forall i (rt:TypeRegisters) k_rs (k:DEX_ValKind) (r:DEX_Reg) (rs:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some k_rs ->
      texec i (DEX_Move k r rs) rt
        (Some (VarMap.update _ rt r ((se i) U k_rs)))

    | DEX_return_ : forall i (rt:TypeRegisters),
      sgn.(DEX_resType) = None ->
      texec i (DEX_Return) rt None

    | DEX_vReturn : forall i (rt:TypeRegisters) k_r kv (k:DEX_ValKind) (r:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      VarMap.get _ rt r = Some k_r ->
      sgn.(DEX_resType) = Some kv ->
      ((se i) U k_r) <= kv -> 
      texec i (DEX_VReturn k r) rt None

    | DEX_const : forall i (rt:TypeRegisters) (k:DEX_ValKind) (r:DEX_Reg) (v:Z),
      In r (VarMap.dom _ rt) ->
      texec i (DEX_Const k r v) rt (Some (VarMap.update _ rt r (L.Simple (se i))))
    
    | DEX_goto : forall i (rt:TypeRegisters) (o:DEX_OFFSET.t),
      texec i (DEX_Goto o) rt (Some rt)

    | DEX_packedSwitch : forall i k (rt:TypeRegisters) (r:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t),
      VarMap.get _ rt r = Some k ->
      (forall j, region i j -> k <= se j) -> 
      texec i (DEX_PackedSwitch r firstKey size l) rt (Some rt)

    | DEX_sparseSwitch : forall i k (rt:TypeRegisters) (reg:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)),
      VarMap.get _ rt reg = Some k ->
      (forall j, region i j -> k <= se j) -> 
      texec i (DEX_SparseSwitch reg size l) rt (Some rt)

    | DEX_ifcmp : forall i ka kb (rt:TypeRegisters) (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t),
      In ra (VarMap.dom _ rt) ->
      In rb (VarMap.dom _ rt) ->
      VarMap.get _ rt ra = Some ka ->
      VarMap.get _ rt rb = Some kb ->
      (forall j, region i j -> (ka U kb) <= se j) -> 
      texec i (DEX_Ifcmp cmp ra rb o) rt (Some rt)
     
    | DEX_ifz : forall i k (rt:TypeRegisters) (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t),
      In r (VarMap.dom _ rt) ->
      VarMap.get _ rt r = Some k ->
      (forall j, region i j -> k <= se j) -> 
      texec i (DEX_Ifz cmp r o) rt (Some rt)

    | DEX_ineg : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some ks ->
      texec i (DEX_Ineg r rs) rt (Some (VarMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_inot : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some ks ->
      texec i (DEX_Inot r rs) rt (Some (VarMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_i2b : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some ks ->
      texec i (DEX_I2b r rs) rt (Some (VarMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_i2s : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some ks ->
      texec i (DEX_I2s r rs) rt (Some (VarMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_ibinop : forall i ka kb (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg),
      In r (VarMap.dom _ rt) ->
      In ra (VarMap.dom _ rt) ->
      In rb (VarMap.dom _ rt) ->
      VarMap.get _ rt ra = Some ka ->
      VarMap.get _ rt rb = Some kb ->
      texec i (DEX_Ibinop op r ra rb) rt 
       (Some (VarMap.update _ rt r (L.Simple ((ka U kb) U (se i)))))
    
    | DEX_ibinopConst : forall i ks (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (rs:DEX_Reg) (v:Z),
      In r (VarMap.dom _ rt) ->
      In rs (VarMap.dom _ rt) ->
      VarMap.get _ rt rs = Some ks ->
      texec i (DEX_IbinopConst op r rs v) rt 
       (Some (VarMap.update _ rt r (L.Simple (ks U (se i)))))   
    .

    Section DEX_RT.
      Variable RT : DEX_PC -> TypeRegisters.

    Definition tsub_next (i:DEX_PC) (rt:TypeRegisters) : bool :=
      match next m i with
        | Some j => tsub_rt rt (RT j)
        | None => false
      end.

    Fixpoint in_test (e:DEX_Reg) (l:list DEX_Reg) : bool :=
      match l with
        | nil => false
        | cn::q => (Neq e cn) || (in_test e q)
      end.

    Lemma In_in_test_true : forall e l,
      In e l -> in_test e l = true.
    Proof.
      induction l; simpl; intros.
      elim H.
      destruct H; subst.
      generalize (Neq_spec e e).
      destruct (Neq e e) ; simpl; auto.
      rewrite IHl; auto.
      destruct (Neq e a) ; simpl; auto.
    Qed.

    Lemma in_test_true_In : forall e l,
      in_test e l = true -> In e l.
    Proof.
      induction l; simpl; intros.
      inversion H.
      apply orb_prop in H.
      elim H; intros.
      generalize (Neq_spec e a). intros. rewrite H0 in H1. left; symmetry; auto. 
      right.
      apply IHl; auto.
    Qed.

    Ltac clean_in_test :=
      try match goal with
        [ id1 : In ?e ?l, id2 : context[in_test ?e ?l = true] |- _ ] =>
          rewrite (In_in_test_true e l id1) in id2
      | [ id2 : context[in_test ?e ?l] |- _ ] =>
          rewrite (In_in_test_true e l) in id2; [idtac|assumption]
      end.

    Definition tcompat_op (ot:option DEX_type) (ok:option L.t') : bool :=
      match ot,ok with
        | None,None => true
        | Some _,Some _ => true
        | _,_ => false
      end.

    Lemma tcompat_op_true : forall (ot:option DEX_type) (ok:option L.t'),
      tcompat_op ot ok = true -> compat_op ot ok.
    Proof.
      destruct ot; destruct ok; simpl; intros; discriminate || constructor.
    Qed.

    Fixpoint le_nat_test (n1 n2:nat) {struct n1} : bool :=
       match n1 with
         | O => true
         | Datatypes.S p1 =>
             match n2 with
               | O => false
               | Datatypes.S p2 => le_nat_test p1 p2
             end
       end.

    Lemma le_nat_test_correct : forall n1 n2,
      if le_nat_test n1 n2 then (n1<=n2)%nat else (~(n1<=n2))%nat.
    Proof.
      induction n1; simpl.
      intros; omega.
      destruct n2; simpl.
      omega.
      generalize (IHn1 n2); destruct (le_nat_test n1 n2); omega.
    Qed.

    Lemma le_nat_test_true : forall n1 n2,
      le_nat_test n1 n2 = true -> (n1<=n2)%nat.
    Proof.
      intros.
      generalize (le_nat_test_correct n1 n2).
      rewrite H; auto.
    Qed.

   Lemma Reg_eq_dec : forall x y : DEX_Reg, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

   Definition DEX_tcheck (i:DEX_PC) (ins:DEX_Instruction) : bool :=
      match ins, RT i with
        | DEX_Nop, rt1 =>
          tsub_next i rt1

        | DEX_Move _ r rs, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some k_rs =>
                tsub_next i (VarMap.update _ rt1 r (L.join (se i) (k_rs)))
            | None => false
          end

        | DEX_Return, rt1 =>
          match sgn.(DEX_resType) with
            | None => true
            | _ => false
          end

        | DEX_VReturn _ r, rt1 =>          
          in_test r (VarMap.dom _ rt1) && 
          match sgn.(DEX_resType) with
            | None => false
            | Some kv => 
              match VarMap.get _ rt1 r with
                | None => false
                | Some k => leql_t (se i U k) kv 
              end
          end

        | DEX_Const _ r _, rt1 =>
          in_test r (VarMap.dom _ rt1) && 
          tsub_next i (VarMap.update _ rt1 r (L.Simple (se i)))

        | DEX_Goto o, rt1 => tsub_rt rt1 (RT (DEX_OFFSET.jump i o))

        | DEX_PackedSwitch r _ _ l, rt1 =>
          match VarMap.get _ rt1 r with
            | None => false
            | Some k => (selift i k) && (tsub_next i rt1) &&
               (for_all _
                 (fun o => tsub_rt rt1 (RT (DEX_OFFSET.jump i o))) l)  
          end
   
        | DEX_SparseSwitch r _ l, rt1 =>
          match VarMap.get _ rt1 r with
            | None => false
            | Some k => (selift i k) && (tsub_next i rt1) &&
               (for_all _
                 (fun o => tsub_rt rt1 (RT (DEX_OFFSET.jump i o)))
                 (@map _ _ (@snd _ _) l))
          end

        | DEX_Ifcmp _ ra rb o, rt1 =>
          in_test ra (VarMap.dom _ rt1) && in_test rb (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 ra, VarMap.get _ rt1 rb with
            | Some ka, Some kb =>
                (selift i (ka U kb)) && 
                (tsub_next i rt1) &&
                (tsub_rt rt1 (RT (DEX_OFFSET.jump i o)))
            | _, _ => false
          end

        | DEX_Ifz _ r o, rt1 =>
          in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 r with
            | Some k => 
                (selift i k) && 
                (tsub_next i rt1) &&
                (tsub_rt rt1 (RT (DEX_OFFSET.jump i o)))
            | None => false
          end        

        | DEX_Ineg r rs, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some ks => (tsub_next i (VarMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_Inot r rs, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some ks => (tsub_next i (VarMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_I2b r rs, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some ks => (tsub_next i (VarMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end

        | DEX_I2s r rs, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some ks => (tsub_next i (VarMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_Ibinop _ r ra rb, rt1 =>
          in_test r (VarMap.dom _ rt1) && in_test ra (VarMap.dom _ rt1) && in_test rb (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 ra, VarMap.get _ rt1 rb with
            | Some ka, Some kb => 
               (tsub_next i (VarMap.update _ rt1 r (L.Simple ((ka U kb) U (se i)))) )
            | _, _ => false
          end   

        | DEX_IbinopConst _ r rs _, rt1 =>
          in_test rs (VarMap.dom _ rt1) && in_test r (VarMap.dom _ rt1) && 
          match VarMap.get _ rt1 rs with
            | Some ks => (tsub_next i (VarMap.update _ rt1 r (L.Simple (ks U (se i)))) )
            | None => false
          end   
      end.

   Ltac flatten_bool :=
     repeat match goal with
       [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
     end.

   Variable selift_prop : forall i  k,
     selift i k = true ->
     forall j, region i j -> k <= (se j).

   Ltac replace_selift :=
     repeat match goal with
       [ id : selift _ _ = true |- _ ] =>  
         generalize (selift_prop _ _ id);
           clear id; intros id
     end.

   Lemma leql_prop : forall x y,
     L.leql_t x y = true -> x <= y.
   Proof.
     intros.
     generalize (L.leql_t_spec x y); rewrite H; auto.
   Qed.

   Ltac replace_leql :=
     repeat match goal with
       [ id : L.leql_t _ _ = true |- _ ] =>  
         generalize (leql_prop _ _ id);
           clear id; intros id
     | [ id : leql'_test ?x ?y = true |- _ ] =>  
       generalize (leql'_test_prop x y); rewrite id; clear id; intros id
     end.

   Ltac replace_for_all :=
     match goal with
       [ id1 : for_all _ _ ?l = true,
         id2 : In ?e ?l |- _] =>
       generalize (for_all_true _ _ _ id1 _ id2);
         clear id1; intros id1
     end.

   Ltac flatten :=
     flatten_bool; try replace_for_all; flatten_bool; replace_selift; clean_in_test; replace_leql.

   Lemma length_le_app_form : forall (A:Set) n (l:list A),
     (n<= length l)%nat -> exists l1, exists l2,
       l = l1++l2 /\ n = length l1.
   Proof.
     induction n; intros.
     exists (@nil A); exists l; split; auto.
     inversion H.
     exists l; exists (@nil A); split; auto.
     apply app_nil_end.
     elim IHn with l.
     intros l1 [l2 [H3 H2]].
     destruct l2.
     rewrite <- app_nil_end in H3; subst.
     apply False_ind; omega.
     exists (l1++(a::nil)); exists l2; split.
     rewrite <- app_cons; auto.
     rewrite length_app_cons_nil; congruence.
     omega.
   Qed.

   Ltac split_match :=
     repeat 
       match goal with
         | [ _ : context[match ?x with nil => _ | _ :: _ => _ end] |- _] => destruct x
         | [ _ : context[match ?x with L.Simple _ => _ | L.Array _ _ => _ end] |- _] => destruct x
         | [_ :  context [match ?x with
                            | DEX_Make.DEX_AddInt => _
                            | DEX_Make.DEX_AndInt => _
                            | DEX_Make.DEX_DivInt => _
                            | DEX_Make.DEX_MulInt => _
                            | DEX_Make.DEX_OrInt => _
                            | DEX_Make.DEX_RemInt => _
                            | DEX_Make.DEX_ShlInt => _
                            | DEX_Make.DEX_ShrInt => _
                            | DEX_Make.DEX_SubInt => _
                            | DEX_Make.DEX_UshrInt => _
                            | DEX_Make.DEX_XorInt => _
                          end] |- _] => destruct x
       end.

   Lemma tcheck_correct1 : forall i ins,
     DEX_tcheck i ins = true ->
      DEX_step m i ins None -> texec i ins (RT i) None.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck in *.
     (* Return *)
     try discriminate; flatten; constructor; auto.
     destruct (DEX_resType sgn); congruence.

     (* VReturn *)
     apply andb_prop in H; inversion H as [H3 H4].
     destruct (DEX_resType sgn) eqn:H1.
     destruct (VarMap.get t (RT i) rt) eqn:H2. 
     apply DEX_vReturn with (k_r:=t1) (kv:=t0); auto.
      apply VarMap.get_some_in_dom.
      unfold not; intros. rewrite H0 in H2. inversion H2.

    generalize (leql_t_spec (se i U t1) t0); intros.
    rewrite H4 in H0; auto.
     inversion H4.
     inversion H4.
   Qed.

   Ltac replace_tsub_next :=
     try match goal with
       [ id1 : tsub_next _ ?rt = true, id2 : next _ _ = _ |- _ ] =>
         unfold tsub_next in id1; rewrite id2 in id1
     end.

   Ltac search_tsub :=
     match goal with
       [ id1 : tsub_rt ?rt (RT _) = true |- _ ] =>
         exists rt; split; [clear id1 | exact id1]
         end.

   Ltac flatten2 := flatten; replace_tsub_next; search_tsub.

   Hint Constructors texec : texec.

   Lemma tcheck_correct2 : forall i ins,
     DEX_tcheck i ins = true ->
     forall j, DEX_step m i ins (Some j) ->
       exists rt,
       texec i ins (RT i) (Some rt)
       /\ tsub_rt rt (RT j) = true.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck in *;
        try (split_match; intuition; subst; try discriminate; 
         flatten2; eauto with texec; fail); 
    try (flatten; destruct (VarMap.get _ (RT i) rs) eqn:Hrs; try (inversion H2; fail);
    flatten2; constructor; try (apply in_test_true_In); auto; fail).
    
    (* const *)
    flatten2; constructor; try (apply in_test_true_In); auto.

     (* Ifcmp *)
     flatten.
     destruct (VarMap.get t (RT i) ra) eqn:Hra; try (inversion H2; fail). 
     destruct (VarMap.get t (RT i) rb) eqn:Hrb; try (inversion H2; fail).
     flatten_bool; replace_selift. inversion H1.
       (* next successor *)
       replace_tsub_next; search_tsub.
       apply DEX_ifcmp with (ka:=t0) (kb:=t1); try (apply in_test_true_In; auto; fail); auto. 
       (* target successor *) 
       rewrite H0. exists (RT i). split. 
       apply DEX_ifcmp with (ka:=t0) (kb:=t1); auto; try (apply in_test_true_In; auto; fail).  
       auto.
     (* Ifz *)
     flatten.
     destruct (VarMap.get t (RT i) r) eqn:Hr; try (inversion H2; fail).
     flatten_bool; replace_selift. inversion H1.
       (* next successor *)
       replace_tsub_next; search_tsub.
       apply DEX_ifz with (k:=t0); auto; try (apply in_test_true_In; auto; fail). 
       (* target successor *) 
       rewrite H. exists (RT i). split. 
       apply DEX_ifz with (k:=t0); auto; try (apply in_test_true_In; auto; fail). exact H3.

     (* Ibinop *)
     flatten.
     destruct (VarMap.get t (RT i) ra) eqn:Hra. try (inversion H2; fail).
     destruct (VarMap.get t (RT i) rb) eqn:Hrb; try (inversion H2; fail).
     flatten2; apply DEX_ibinop; auto; try (apply in_test_true_In; auto; fail). inversion H2.
     (* IbinopConst *)
     flatten.
     destruct (VarMap.get t (RT i) r) eqn:Hr; try (inversion H2; fail);
     flatten2; apply DEX_ibinopConst; try (apply in_test_true_In; auto; fail); apply Hr.
     (* PackedSwitch *)
     destruct (VarMap.get t (RT i) reg) eqn:Hr; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1. 
       (* default successor *)
       exists (RT i); split. apply DEX_packedSwitch with (k:=t0).
       apply Hr. apply H. unfold tsub_next in H3.
        inversion H4.
       rewrite H5 in H3. auto.
       (* other successors *)
       destruct (VarMap.get t (RT i) reg) eqn:Hr; try (inversion H; fail).
       flatten_bool; replace_selift.
       exists (RT i); split. apply DEX_packedSwitch with (k:=t0).
       apply Hr. apply H. replace_for_all. apply H2.
     (* SparseSwitch *)
     destruct (VarMap.get t (RT i) reg) eqn:Hr; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1. 
       (* default successor *)
       exists (RT i); split. apply DEX_sparseSwitch with (k:=t0).
       apply Hr. apply H. unfold tsub_next in H3.
       inversion H4.
       rewrite H5 in H3; auto.
       (* other successors *)
       destruct (VarMap.get t (RT i) reg) eqn:Hr; try (inversion H; fail).
       flatten_bool; replace_selift.
       exists (RT i); split. apply DEX_sparseSwitch with (k:=t0).
       apply Hr. apply H. replace_for_all. apply H2.
   Qed.
 End DEX_RT.
End DEX_typing_rules.