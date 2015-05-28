(** typing_rules.v: Typing rules, plus an executable type checker *)
Require Export DEX_BigStepAnnot.
Require Export Bool.
Require Export DEX_step.
Import DEX_StaticHandler.DEX_StaticHandler DEX_BigStep.DEX_BigStep DEX_Dom.DEX_Prog.

Import Level.L.
Import DEX_Dom.

Open Scope type_scope.

  Section DEX_typing_rules.   (** Typing rules **)
    Variable p : DEX_ExtendedProgram.
    Variable subclass_test : DEX_ClassName -> DEX_ClassName -> bool.
    Variable subclass_test_correct :
      forall c1 c2,
        if subclass_test c1 c2 then subclass_name p.(DEX_prog) c1 c2
          else ~ subclass_name p.(DEX_prog) c1 c2.
    Variable m : DEX_Method.
    Definition method_signature := DEX_METHOD.signature m.
    Variable sgn : DEX_sign.
    Variable region : DEX_PC -> DEX_tag -> DEX_PC -> Prop.
    Variable se : DEX_PC -> L.t.
    Variable selift : DEX_PC -> DEX_tag -> L.t -> bool.
    Variable ret : DEX_Reg.

    (* Notation handler := (handler subclass_test m). *)

    Infix "<=" := L.leql (at level 70).
    Infix "<='" := L.leql' (at level 70).
    Infix "U'" := L.join' (at level 60, right associativity).
    Infix "U" := L.join (at level 60, right associativity).

    Inductive texec : DEX_PC -> DEX_Instruction -> DEX_tag -> TypeRegisters -> option TypeRegisters -> Prop :=
    | nop : forall i rt,
      texec i Nop None rt (Some rt)

    | move_constrained : forall i (rt:TypeRegisters) k_rs (k:DEX_ValKind) (r:DEX_Reg) (rs:DEX_Reg),
      In r (locR p method_signature) ->
      Some k_rs = BinNatMap.get _ rt rs ->
      se i <= sgn.(DEX_lvt) r ->
      k_rs <=' sgn.(DEX_lvt) r ->
      texec i (Move k r rs) None rt 
       (Some (BinNatMap.update _ rt r ((se i) U' k_rs)))

    | move_unconstrained : forall i (rt:TypeRegisters) k_rs (k:DEX_ValKind) (r:DEX_Reg) (rs:DEX_Reg),
      ~In r (locR p method_signature) ->
      Some k_rs = BinNatMap.get _ rt rs ->
      texec i (Move k r rs) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_rs)))

    | moveResult_constrained : forall i (rt:TypeRegisters) k_res (k:DEX_ValKind) (r:DEX_Reg),
      In r (locR p method_signature) ->
      Some k_res = BinNatMap.get _ rt DEX_Registers.ret ->
      se i <= sgn.(DEX_lvt) r ->
      k_res <= sgn.(DEX_lvt) r ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))

    | moveResult_unconstrained : forall i (rt:TypeRegisters) k_res (k:DEX_ValKind) (r:DEX_Reg),
      ~In r (locR p method_signature) ->
      Some k_res = BinNatMap.get _ rt DEX_Registers.ret ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))

    | return_ : forall i (rt:TypeRegisters),
      sgn.(DEX_resType) = None ->
      texec i (Return) None rt None

    | vReturn : forall i (rt:TypeRegisters) k_r kv (k:DEX_ValKind) (r:DEX_Reg),
      Some k_r = BinNatMap.get _ rt r ->
      sgn.(DEX_resType) = Some kv ->
      (* DEX probably later ((se i) U' k_r) <=' kv -> *)
      texec i (VReturn k r) None rt None

    | const : forall i (rt:TypeRegisters) (k:DEX_ValKind) (r:DEX_Reg) (v:Z),
      texec i (Const k r v) None rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))
    
    | instanceOf : forall i (rt:TypeRegisters) k (r:DEX_Reg) (ro:DEX_Reg) (t:DEX_refType),
      Some k = BinNatMap.get _ rt ro ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (InstanceOf r ro t) None rt 
        (Some (BinNatMap.update _ rt r (L.Simple ((se i) U k))))
    
    | arrayLength : forall i k ke (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      Some (L.Array k ke) = BinNatMap.get _ rt rs ->
      texec i (ArrayLength r rs) None rt
        (Some (BinNatMap.update _ rt r (L.Simple k)))
    
    | new : forall i (rt:TypeRegisters) (r:DEX_Reg) (t:DEX_refType),
      texec i (New r t) None rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))

    | newArray : forall i (rt:TypeRegisters) k (r:DEX_Reg) (rl:DEX_Reg) (t:DEX_type),
      Some k = BinNatMap.get _ rt rl ->
      texec i (NewArray r rl t) None rt
        (Some (BinNatMap.update _ rt r (L.Array k (DEX_newArT p (m,i)))))

    | goto : forall i (rt:TypeRegisters) (o:DEX_OFFSET.t),
      texec i (Goto o) None rt (Some rt)

    | packedSwitch : forall i k (rt:TypeRegisters) (r:DEX_Reg) (firstKey:Z) (size:Z) (l:list DEX_OFFSET.t),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (PackedSwitch r firstKey size l) None rt (Some (lift_rt k rt))

    | sparseSwitch : forall i k (rt:TypeRegisters) (r:DEX_Reg) (size:Z) (l:list (Z * DEX_OFFSET.t)),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (SparseSwitch r size l) None rt (Some (lift_rt k rt))
    
    | ifcmp : forall i ka kb (rt:TypeRegisters) (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t),
      Some ka = BinNatMap.get _ rt ra ->
      Some kb = BinNatMap.get _ rt rb ->
      (forall j, region i None j -> (ka U kb) <= se j) -> 
      texec i (Ifcmp cmp ra rb o) None rt (Some (lift_rt (ka U kb) rt))
     
    | ifz : forall i k (rt:TypeRegisters) (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (Ifz cmp r o) None rt (Some (lift_rt k rt))

    | aget : forall i ka kc ki (rt:TypeRegisters) 
       (k:DEX_ArrayKind) (r:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      Some (L.Array ka kc) = BinNatMap.get _ rt ra ->
      Some ki = BinNatMap.get _ rt ri ->
      texec i (Aget k r ra ri) None rt 
        (Some (BinNatMap.update _ rt r ((ka U ki) U' kc)))

    | aput : forall i ks ka kc ki (rt:TypeRegisters)
       (k:DEX_ArrayKind) (rs:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      Some ks = BinNatMap.get _ rt rs ->
      Some (L.Array ka kc) = BinNatMap.get _ rt ra ->
      Some ki = BinNatMap.get _ rt ri ->
      ((ka U ki) U' ks) <=' kc ->
      L.leql (DEX_heapEffect sgn) kc ->
      texec i (Aput k rs ra ri) None rt (Some rt)

    | iget : forall i ko (rt:TypeRegisters) (k:DEX_ValKind) (r:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      Some ko = BinNatMap.get _ rt ro ->
      texec i (Iget k r ro f) None rt 
        (Some (BinNatMap.update _ rt r ((ko U (se i)) U' (DEX_ft p f))))

    | iput : forall i ks ko (rt:TypeRegisters) (k:DEX_ValKind) (rs:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      Some ks = BinNatMap.get _ rt rs ->
      Some ko = BinNatMap.get _ rt ro ->
      ((se i) U ko) U' ks <=' (DEX_ft p f) ->
      sgn.(DEX_heapEffect) <= (DEX_ft p f) ->
      texec i (Iput k rs ro f) None rt (Some rt)

(*    | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
    | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)

    | invokevirtual : forall i ro ko (rt:TypeRegisters) (m:DEX_MethodSignature) (n:Z) (par:list DEX_Reg),
      Some ro = hd_error par ->
      Some ko = BinNatMap.get _ rt ro ->
      length par = length (DEX_METHODSIGNATURE.parameters (snd m)) ->
      compat_type_rt_lvt (DEX_virtual_signature p (snd m) ko) (rt) (par) (Z.to_nat n) ->
      ko <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) -> 
      sgn.(DEX_heapEffect) <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) ->
      (* DEX *) (se i) <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) ->
      compat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_virtual_signature p (snd m) ko).(DEX_resType) -> 
      texec i (Invokevirtual m n par) None rt
      (Some (update_op rt DEX_Registers.ret
            (join_op (ko U (se i)) (DEX_virtual_signature p (snd m) ko).(DEX_resType)) ))
(*
    | Invokesuper (m:MethodSignature) (n:Z) (p:list Var)
    | Invokedirect (m:MethodSignature) (n:Z) (p:list Var)
*)
    | invokestatic : forall i (rt:TypeRegisters) (m:DEX_MethodSignature) (n:Z) (par:list DEX_Reg),
      length par = length (DEX_METHODSIGNATURE.parameters (snd m)) ->
      compat_type_rt_lvt (DEX_static_signature p (snd m)) (rt) (par) (Z.to_nat n) ->
      se i <= (DEX_static_signature p (snd m)).(DEX_heapEffect) -> 
      sgn.(DEX_heapEffect) <= (DEX_static_signature p (snd m)).(DEX_heapEffect) ->
      compat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_static_signature p (snd m)).(DEX_resType) -> 
      texec i (Invokestatic m n par) None rt
      (Some (update_op rt DEX_Registers.ret
            (join_op (se i) (DEX_static_signature p (snd m)).(DEX_resType)) ))
(*
    | Invokeinterface (m:MethodSignature) (n:Z) (p:list Var)
*)
    | ineg : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (Ineg r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | inot : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (Inot r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | i2b : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (I2b r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | i2s : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (I2s r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | ibinop : forall i ka kb (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg),
      Some ka = BinNatMap.get _ rt ra ->
      Some kb = BinNatMap.get _ rt rb ->
      texec i (Ibinop op r ra rb) None rt 
       (Some (BinNatMap.update _ rt r (L.Simple ((ka U kb) U (se i)))))
    
    | ibinopConst : forall i ks (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (rs:DEX_Reg) (v:Z),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (IbinopConst op r rs v) None rt 
       (Some (BinNatMap.update _ rt r (L.Simple (ks U (se i)))))   
    .

    Section DEX_RT.
      Variable RT : DEX_PC -> TypeRegisters.

    Definition tsub_next (i:DEX_PC) rt : bool :=
      match next m i with
        | Some j => tsub_rt rt (RT j)
        | None => false
      end.

(* DEX
    Definition exception_test (i:PC) (e:ClassName) (k:L.t) : bool :=
      match handler i e with
        | Some t => tsub (L.Simple k::nil) (S t)
        | None => L.leql_t k (sgn.(resExceptionType) e)
      end.
*)
    Fixpoint in_test (e:DEX_ClassName) (l:list DEX_ClassName) : bool :=
      match l with
        | nil => false
        | cn::q =>
          (eqClassName e cn) || (in_test e q)
      end.

    Lemma In_in_test_true : forall e l,
      In e l -> in_test e l = true.
    Proof.
      induction l; simpl; intros.
      elim H.
      destruct H; subst.
      generalize (eqClassName_spec e e).
      destruct (eqClassName e e) ; simpl; auto.
      rewrite IHl; auto.
      destruct (eqClassName e a) ; simpl; auto.
    Qed.

    Ltac clean_in_test :=
      try match goal with
        [ id1 : In ?e ?l, id2 : context[in_test ?e ?l = true] |- _ ] =>
          rewrite (In_in_test_true e l id1) in id2
      | [ id2 : context[in_test ?e ?l] |- _ ] =>
          rewrite (In_in_test_true e l) in id2; [idtac|assumption]
      end.

(* DEX
    Definition exception_test' (i:PC) (e:ClassName) (k:L.t) : bool :=
      if in_test e (throwableAt m i) then
        match handler i e with
          | Some t => tsub (L.Simple k::nil) (S t)
          | None => L.leql_t k (sgn.(resExceptionType) e)
        end
        else true.
*)

    Fixpoint tcompat_type_rt_lvt_aux (s:DEX_sign) (rt:TypeRegisters) 
      (p:list DEX_Reg) (n:nat) {struct n} : bool :=
      match n with (* could be optimised *)
        | O => true
        | Datatypes.S q => 
          match nth_error p (q)%nat with
          | None => false
          | Some x =>
            match BinNatMap.get _ rt x with
            | None => false
            | Some k => leql'_test k (DEX_lvt s (N_toReg (q)%nat))
            end && tcompat_type_rt_lvt_aux s rt p q
          end
      end.

    Lemma tcompat_type_rt_lvt_aux_true : forall s rt p n,
      tcompat_type_rt_lvt_aux s rt p n = true ->
      forall x, ((Reg_toN x)<n)%nat -> exists r k,
        nth_error p (Reg_toN x) = Some r /\ BinNatMap.get _ rt r = Some k /\
        L.leql' k (DEX_lvt s x).
    Proof.
      induction n. simpl.
      intros.
      apply False_ind; omega. simpl.

      caseeq (nth_error p0 n); intros.
      elim andb_prop with (1:=H0); clear H0; intros.
      destruct (BinNatMap.get t' rt d) eqn:H3; intros.
      elim (eq_excluded_middle _ (Reg_toN x) n); intros; subst.
      (* replace (n0 - Reg_toN x - 1)%nat with (n0 - S (Reg_toN x))%nat. *)
      exists d; exists t0; split; auto. (* Hendra *)
      split; auto.
      generalize (leql'_test_prop t0 (DEX_lvt s (N_toReg (Reg_toN x)))); rewrite H0. (* Hendra *)
      rewrite Reg_toN_bij1; auto. 
      apply IHn; auto. omega.
      inversion H0.
      inversion H0.
    Qed.

    Definition tcompat_type_rt_lvt (s:DEX_sign) (rt:TypeRegisters) (par:list DEX_Reg)
      (n:nat) : bool := tcompat_type_rt_lvt_aux s rt par n.

    Lemma tcompat_type_rt_lvt_true : forall s rt par n,
      tcompat_type_rt_lvt s rt par n = true ->
      compat_type_rt_lvt s rt par n.
    Proof.
      unfold tcompat_type_rt_lvt, compat_type_rt_lvt; intros.
      apply (tcompat_type_rt_lvt_aux_true _ _ _ _ H); auto.
    Qed.

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

(* DEX
    Fixpoint pop_n (A:Type) (n:nat) (l:list A) {struct n} : list A :=
      match n with
        | O => l
        | Datatypes.S p => match l with
                   | nil => nil
                   | x::q => pop_n A p q
                 end
      end.
    Implicit Arguments pop_n [A].

    Lemma pop_n_length_fst : forall A (l1 l2:list A),
      pop_n (length l1) (l1 ++ l2) = l2.
    Proof.
      induction l1; simpl; auto.
    Qed.
*)
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

(* Duplicate with the one in Annotated.v? 
    Definition compat_type_rt_lvt (s:sign) (rt:TypeRegisters) (n:nat) : Prop :=
      forall x, ((Reg_toN x)<n)%nat -> exists k,
        nth_error st (n-(Var_toN x)-1)%nat = Some k /\
        L.leql' k (lvt s x).
*)

   Lemma Reg_eq_dec : forall x y : DEX_Reg, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

   Definition DEX_tcheck (i:DEX_PC) (ins:DEX_Instruction) : bool :=
      match ins, RT i with
        | Nop, rt1 =>
          tsub_next i rt1

        | Move _ r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some k_rs =>
                (if in_dec Reg_eq_dec r (locR p method_signature) then
                   L.leql_t (se i) (sgn.(DEX_lvt) r) &&
                   leql'_test k_rs (sgn.(DEX_lvt) r)
                   else true) && 
                tsub_next i (BinNatMap.update _ rt1 r (L.join' (se i) (k_rs)))
            | None => false
          end
        
        | MoveResult _ r, rt1 =>
          (if in_dec Reg_eq_dec r (locR p method_signature) then
             match BinNatMap.get _ rt1 ret with
               | Some k_rs =>
                   L.leql_t (se i) (sgn.(DEX_lvt) r) &&
                   leql'_test k_rs (sgn.(DEX_lvt) r)
               | None => false
             end
          else true)
          &&
          tsub_next i (BinNatMap.update _ rt1 r (L.join' (se i) (sgn.(DEX_lvt) ret)))

        | Return, rt1 =>
          match sgn.(DEX_resType) with
            | None => true
            | _ => false
          end

        | VReturn _ r, rt1 =>          
          match sgn.(DEX_resType) with
            | None => false
            | Some kv => 
              match BinNatMap.get _ rt1 r with
                | None => false
                | Some k => leql'_test k kv 
              end
          end

        | Const _ r _, rt1 =>
          tsub_next i (BinNatMap.update _ rt1 r (L.Simple (se i)))

        | InstanceOf r ro _, rt1 =>
          match BinNatMap.get _ rt1 ro with
            | None => false
            | Some k =>
                (selift i None k) &&
                (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U k))))
          end

        | ArrayLength r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some (L.Array k ke) =>
                (tsub_next i (BinNatMap.update _ rt1 r (L.Simple k)))
            | _ => false
          end

        | New r _, rt1 =>
          tsub_next i (BinNatMap.update _ rt1 r (L.Simple (se i)))

        | NewArray r rl _, rt1 =>
          match BinNatMap.get _ rt1 rl with
            | None => false
            | Some k =>
                tsub_next i (BinNatMap.update _ rt1 r (L.Array k (DEX_newArT p (m,i))))
          end

        | Goto _, rt1 => tsub_next i rt1

        | PackedSwitch r _ _ _, rt1 =>
          match BinNatMap.get _ rt1 r with
            | None => false
            | Some k => (selift i None k) && (tsub_next i (lift_rt k rt1))
          end
   
        | SparseSwitch r _ _, rt1 =>
          match BinNatMap.get _ rt1 r with
            | None => false
            | Some k => (selift i None k) && (tsub_next i (lift_rt k rt1))
          end
      
        | Ifcmp _ ra rb _, rt1 =>
          match BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 rb with
            | Some ka, Some kb =>
                (selift i None (ka U kb)) && (tsub_next i (lift_rt (ka U kb) rt1))
            | _, _ => false
          end

        | Ifz _ r _, rt1 =>
          match BinNatMap.get _ rt1 r with
            | Some k => 
                (selift i None k) && (tsub_next i (lift_rt k rt1))
            | None => false
          end        

        | Aget _ r ra ri, rt1 =>
          match BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 ri with
            | Some (L.Array ka kc), Some ki =>
                tsub_next i (BinNatMap.update _ rt1 r ((ka U ki) U' kc))
            | _, _ => false
          end

        | Aput _ rs ra ri, rt1 =>
          match BinNatMap.get _ rt1 rs, BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 ri with
            | Some ks, Some (L.Array ka kc), Some ki =>
                (leql'_test ks kc) &&
                (L.leql_t ki kc) &&
                (L.leql_t ka kc) &&
                (L.leql_t (DEX_heapEffect sgn) kc) &&
                (tsub_next i rt1)
            | _, _, _ => false
          end

        | Iget _ r ro f, rt1 =>
          match BinNatMap.get _ rt1 ro with
            | Some ko =>
               (tsub_next i (BinNatMap.update _ rt1 r ((ko U (se i)) U' (DEX_ft p f))) )
            | None => false
          end

        | Iput _ rs ro f, rt1 =>
          match BinNatMap.get _ rt1 rs, BinNatMap.get _ rt1 ro with
            | Some ks, Some ko =>
               leql'_test (((se i) U ko) U' ks) (DEX_ft p f) &&
               L.leql_t sgn.(DEX_heapEffect) (DEX_ft p f) &&
               (tsub_next i rt1)
            | _, _ => false
          end        

(*    | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
    | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)

        | Invokevirtual m n (ro::par), rt1 =>
          match BinNatMap.get _ rt1 ro with
            | Some ko =>
              (le_nat_test (S (Z.to_nat n)) (length par)) &&
              (tcompat_type_rt_lvt (DEX_virtual_signature p (snd m) ko) (rt1) (par) (Z.to_nat n)) &&
              (L.leql_t ko (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (L.leql_t sgn.(DEX_heapEffect) (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (L.leql_t (se i) (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (tcompat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_virtual_signature p (snd m) ko).(DEX_resType)) &&
              (tsub_next i (update_op rt1 ret 
                           (join_op (ko U (se i)) (DEX_virtual_signature p (snd m) ko).(DEX_resType))) )
            | None => false    
          end

        | Invokestatic m n par, rt1 =>
            (le_nat_test (S (Z.to_nat n)) (length par)) &&
            (tcompat_type_rt_lvt (DEX_static_signature p (snd m)) (rt1) (par) (Z.to_nat n)) &&
            (L.leql_t sgn.(DEX_heapEffect) (DEX_static_signature p (snd m)).(DEX_heapEffect)) &&
            (L.leql_t (se i) (DEX_static_signature p (snd m)).(DEX_heapEffect)) &&
            (tcompat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_static_signature p (snd m)).(DEX_resType)) &&
            (tsub_next i (update_op rt1 ret 
                         (join_op (se i) (DEX_static_signature p (snd m)).(DEX_resType))) )

        | Ineg r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | Inot r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | I2b r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end

        | I2s r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | Ibinop _ r ra rb, rt1 =>
          match BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 rb with
            | Some ka, Some kb => 
               (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((ka U kb) U (se i)))) )
            | _, _ => false
          end   

        | IbinopConst _ r rs _, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | _, _ => false
      end.

   Ltac flatten_bool :=
     repeat match goal with
       [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
     end.

   Variable selift_prop : forall i tau k,
     selift i tau k = true ->
     forall j, region i tau j -> k <= (se j).

   Ltac replace_selift :=
     repeat match goal with
       [ id : selift _ _ _ = true |- _ ] =>  
         generalize (selift_prop _ _ _ id);
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
(* DEX
   Ltac replace_handler :=
     repeat match goal with
       [ id1 : StaticHandler.handler ?s ?m ?i ?e = _,
         id2 : context[StaticHandler.handler ?s ?m ?i ?e] |- _ ] =>
       rewrite id1 in id2
     end.
*)
   Ltac flatten :=
     flatten_bool; try replace_for_all; flatten_bool;
       (* DEX replace_handler; *) replace_selift; clean_in_test; replace_leql.

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
                            | DEX_Make.AddInt => _
                            | DEX_Make.AndInt => _
                            | DEX_Make.DivInt => _
                            | DEX_Make.MulInt => _
                            | DEX_Make.OrInt => _
                            | DEX_Make.RemInt => _
                            | DEX_Make.ShlInt => _
                            | DEX_Make.ShrInt => _
                            | DEX_Make.SubInt => _
                            | DEX_Make.UshrInt => _
                            | DEX_Make.XorInt => _
                          end] |- _] => destruct x
       end.


   Lemma tcheck_correct1 : forall i ins,
     DEX_tcheck i ins = true ->
     forall tau, DEX_step (* p subclass_test *) m i ins tau None ->
       texec i ins tau (RT i) None.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck (* DEX step.handler, exception_test, exception_test' *) in *.
     (* Return *)
     try discriminate; flatten; constructor; auto.
     destruct (DEX_resType sgn); congruence.

     (* VReturn *)
     destruct (DEX_resType sgn) eqn:H1.
     destruct (BinNatMap.get t' (RT i) rt) eqn:H2. 
     apply vReturn with (k_r:=t1) (kv:=t0). 
     rewrite H2; reflexivity. apply H1.
     inversion H.
     inversion H.
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
     forall tau j, DEX_step (* DEX p subclass_test *) m i ins tau (Some j) ->
       exists rt,
       texec i ins tau (RT i) (Some rt)
       /\ tsub_rt rt (RT j) = true.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck (* DEX step.handler, exception_test, exception_test'*) in *;
     try (split_match; intuition; subst; try discriminate; flatten2; eauto with texec; fail).
     (* move *)
     destruct (BinNatMap.get t' (RT i) rs) eqn:Hrs; try (inversion H; fail).
     split_match; intuition; try discriminate; flatten2.
     destruct (in_dec Reg_eq_dec rt (locR p method_signature)) eqn:HlocR.
     flatten_bool.
     apply move_constrained.
       apply i0.
       rewrite Hrs; reflexivity. 
       generalize (L.leql_t_spec (se i) (DEX_lvt sgn rt)); rewrite H; auto.
       generalize (leql'_test_prop (t0) (DEX_lvt sgn rt)); rewrite H2; auto.
     apply move_unconstrained.
       apply n.
       rewrite Hrs; reflexivity.
     
(* DEX
     split_match; intuition; try discriminate; flatten2.
     apply arraylength_np_caught with (t := j). apply H0. apply H2.
     
     split_match; try (case op in H; inversion H; fail).
     destruct op; flatten2; apply ibinop; auto.
 *)
     (* invokestatic *)
     flatten2.
     elim length_le_app_form with (n:=(length (METHODSIGNATURE.parameters (snd mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     rewrite T2.
     rewrite pop_n_length_fst.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     apply tcompat_op_true; auto.
     generalize (le_nat_test_correct (length (METHODSIGNATURE.parameters (snd mid)))
       (length (S i))); rewrite H0; auto.
     (**)
     flatten2.
     elim length_le_app_form with (n:=(length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     generalize (le_nat_test_correct (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)))
       (length (S i))).
     rewrite H0; auto.
     (* invokevirtual *)
     generalize H; clear H.
     case_eq (pop_n  (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid))) (S i)); intros.
     discriminate. 
     destruct t0 as [k1|]; try discriminate.
     (*destruct t as [k1|]; try discriminate.*)
     flatten2.
     elim length_le_app_form with (n:=(length (METHODSIGNATURE.parameters (snd mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     rewrite T1 in H; rewrite T2 in H; rewrite pop_n_length_fst in H.
     subst.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     apply tcompat_op_true; auto.
     generalize (le_nat_test_true _ _ H2); clear H2; intros H2.
     omega.
     (**)
     generalize H; clear H.
     case_eq (pop_n  (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid))) (S i)); intros.
     discriminate.
     destruct t0 as [k1|]; try discriminate.
     (*destruct t as [k1|]; try discriminate.*)
     flatten.
     elim length_le_app_form with (n:=(length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     rewrite T1 in H; rewrite T2 in H; rewrite pop_n_length_fst in H.
     subst.
     exists (lift k1 (L.Simple (L.join k1 ((virtual_signature p (snd mid) k1).(resExceptionType) e))::nil)).
     split.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     simpl.
     simpl in H13.
     destruct (S j); try discriminate.
     destruct t0; try discriminate.
     (*destruct t; try discriminate.*)
     flatten_bool.
     destruct t1; try discriminate.
     (*destruct t0; try discriminate.*)
     replace_leql.
     generalize (L.leql_t_spec (k1 U k1 U resExceptionType (virtual_signature p (snd mid) k1) e) k).
     destruct (L.leql_t (k1 U k1 U resExceptionType (virtual_signature p (snd mid) k1) e) k); auto.
     intros.
     elim H13.
     apply L.join_least.
     apply L.leql_trans with (2:=H).
     apply L.join_left.
     auto.     
     generalize (le_nat_test_true _ _ H3); clear H3; intros H3.
     omega.
     (* vaload *)
   Qed.
 End DEX_S.
*)
  End DEX_typing_rules.