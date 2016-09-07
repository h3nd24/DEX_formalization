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

(* Module Make (M:MAP). *)

(*   Module DEX_Step := DEX_step.Make M. *)
  Section DEX_typing_rules.   (** Typing rules **)
(* DEX 
    Variable p : DEX_ExtendedProgram.
    Variable subclass_test : DEX_ClassName -> DEX_ClassName -> bool.
    Variable subclass_test_correct :
      forall c1 c2,
        if subclass_test c1 c2 then subclass_name p.(DEX_prog) c1 c2
          else ~ subclass_name p.(DEX_prog) c1 c2.
    (*Variable m : DEX_Method.*)
*)
    (* Definition address := M.key.
    Variable codes : M.t (DEX_Instruction*(option address*list DEX_ClassName)).
    Variable jumpAddress : address -> DEX_OFFSET.t -> address.

    Definition nextAddress (pc:address): option address :=
    match M.get codes pc with
      | Some p => fst (snd p)
      | None => None
    end.

    Definition instructionAtAddress (pc:address) : option DEX_Instruction :=
    match M.get codes pc with
      |Some p => Some (fst p)
      |None => None
    end.

    Variable locR : list DEX_Reg. *)
    (*Variable m : MapN.t (DEX_Instruction*(option DEX_PC * list DEX_ClassName)).*)
    (*Definition method_signature := DEX_METHOD.signature m.*)
    Variable m : DEX_Method.
    Variable sgn : DEX_sign.
    Variable region : DEX_PC -> (* DEX_tag -> *) DEX_PC -> Prop.
    Variable se : DEX_PC -> L.t.
    Variable selift : DEX_PC -> (* DEX_tag -> *) L.t -> bool. 
    Variable ret : DEX_Reg.

    (* Notation handler := (handler subclass_test m). *)

    Infix "<=" := L.leql (at level 70).
    Infix "<='" := L.leql' (at level 70).
    Infix "U'" := L.join' (at level 60, right associativity).
    Infix "U" := L.join (at level 60, right associativity).

    Inductive texec : DEX_PC -> DEX_Instruction -> (* DEX_tag -> *) TypeRegisters -> option TypeRegisters -> Prop :=
(*     Inductive texec : address -> DEX_Instruction -> DEX_tag -> TypeRegisters -> option TypeRegisters -> Prop := *)
    | DEX_nop : forall i rt,
      texec i DEX_Nop (* None *) rt (Some rt)

    (* | DEX_move_constrained : forall i (rt:TypeRegisters) k_rs (k:DEX_ValKind) (r:DEX_Reg) (rs:DEX_Reg),
      In r locR ->
      BinNatMap.get _ rt rs = Some k_rs ->
      se i <= sgn.(DEX_lvt) r ->
      k_rs <=' sgn.(DEX_lvt) r ->
      texec i (DEX_Move k r rs) None rt 
       (Some (BinNatMap.update _ rt r ((se i) U' k_rs))) *)

    | DEX_move : forall i (rt:TypeRegisters) k_rs (k:DEX_ValKind) (r:DEX_Reg) (rs:DEX_Reg),
(*       ~In r locR -> *)
      BinNatMap.get _ rt rs = Some k_rs ->
      texec i (DEX_Move k r rs) (* None *) rt
        (Some (BinNatMap.update _ rt r ((se i) U k_rs)))

(* DEX Method
    | moveResult_constrained : forall i (rt:TypeRegisters) k_res (k:DEX_ValKind) (r:DEX_Reg),
      In r (locR p method_signature) ->
      BinNatMap.get _ rt ret = Some k_res ->
      se i <= sgn.(DEX_lvt) r ->
      k_res <=' sgn.(DEX_lvt) r ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))

    | moveResult_unconstrained : forall i (rt:TypeRegisters) k_res (k:DEX_ValKind) (r:DEX_Reg),
      ~In r (locR p method_signature) ->
      BinNatMap.get _ rt ret = Some k_res ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))
*)

    | DEX_return_ : forall i (rt:TypeRegisters),
      sgn.(DEX_resType) = None ->
      texec i (DEX_Return) (* None *) rt None

    | DEX_vReturn : forall i (rt:TypeRegisters) k_r kv (k:DEX_ValKind) (r:DEX_Reg),
      BinNatMap.get _ rt r = Some k_r ->
      sgn.(DEX_resType) = Some kv ->
      ((se i) U k_r) <= kv -> 
      texec i (DEX_VReturn k r) (* None *) rt None

    | DEX_const : forall i (rt:TypeRegisters) (k:DEX_ValKind) (r:DEX_Reg) (v:Z),
      texec i (DEX_Const k r v) (* None *) rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))
    
(* DEX Object
    | instanceOf : forall i (rt:TypeRegisters) k (r:DEX_Reg) (ro:DEX_Reg) (t:DEX_refType),
      BinNatMap.get _ rt ro = Some k ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (InstanceOf r ro t) None rt 
        (Some (BinNatMap.update _ rt r (L.Simple ((se i) U k))))
    
    | arrayLength : forall i k ke (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      BinNatMap.get _ rt rs = Some (L.Array k ke) ->
      texec i (ArrayLength r rs) None rt
        (Some (BinNatMap.update _ rt r (L.Simple k)))
    
    | new : forall i (rt:TypeRegisters) (r:DEX_Reg) (t:DEX_refType),
      texec i (New r t) None rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))

    | newArray : forall i (rt:TypeRegisters) k (r:DEX_Reg) (rl:DEX_Reg) (t:DEX_type),
      BinNatMap.get _ rt rl = Some k ->
      texec i (NewArray r rl t) None rt
        (Some (BinNatMap.update _ rt r (L.Array k (DEX_newArT p (m,i)))))
*)

    | DEX_goto : forall i (rt:TypeRegisters) (o:DEX_OFFSET.t),
      texec i (DEX_Goto o) (* None *) rt (Some rt)
(* Hendra 11082016 focus on DEX I
    | DEX_packedSwitch : forall i k (rt:TypeRegisters) (r:DEX_Reg) (firstKey:Z) (size:nat) (l:list DEX_OFFSET.t),
      BinNatMap.get _ rt r = Some k ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (DEX_PackedSwitch r firstKey size l) None rt (Some (lift_rt k rt))

    | DEX_sparseSwitch : forall i k (rt:TypeRegisters) (r:DEX_Reg) (size:nat) (l:list (Z * DEX_OFFSET.t)),
      BinNatMap.get _ rt r = Some k ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (DEX_SparseSwitch r size l) None rt (Some (lift_rt k rt))
*)

    | DEX_ifcmp : forall i ka kb (rt:TypeRegisters) (cmp:DEX_CompInt) (ra:DEX_Reg) (rb:DEX_Reg) (o:DEX_OFFSET.t),
      BinNatMap.get _ rt ra = Some ka ->
      BinNatMap.get _ rt rb = Some kb ->
      (forall j, region i (* None *) j -> (ka U kb) <= se j) -> 
      texec i (DEX_Ifcmp cmp ra rb o) (* None *) rt (Some (*lift_rt (ka U kb)*) rt)
     
    | DEX_ifz : forall i k (rt:TypeRegisters) (cmp:DEX_CompInt) (r:DEX_Reg) (o:DEX_OFFSET.t),
      BinNatMap.get _ rt r = Some k ->
      (forall j, region i (* None *) j -> k <= se j) -> 
      texec i (DEX_Ifz cmp r o) (* None *) rt (Some (*lift_rt k rt*)rt)
(* DEX object and method
    | aget : forall i ka kc ki (rt:TypeRegisters) 
       (k:DEX_ArrayKind) (r:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      BinNatMap.get _ rt ra = Some (L.Array ka kc) ->
      BinNatMap.get _ rt ri = Some ki ->
      texec i (Aget k r ra ri) None rt 
        (Some (BinNatMap.update _ rt r ((ka U ki) U' kc)))

    | aput : forall i ks ka kc ki (rt:TypeRegisters)
       (k:DEX_ArrayKind) (rs:DEX_Reg) (ra:DEX_Reg) (ri:DEX_Reg),
      BinNatMap.get _ rt rs = Some ks ->
      BinNatMap.get _ rt ri = Some ki ->
      BinNatMap.get _ rt ra = Some (L.Array ka kc) ->
      ks <=' kc ->
      ki <= kc ->
      ka <= kc ->
      L.leql (DEX_heapEffect sgn) kc ->
      texec i (Aput k rs ra ri) None rt (Some rt)

    | iget : forall i ko (rt:TypeRegisters) (k:DEX_ValKind) (r:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      BinNatMap.get _ rt ro = Some ko ->
      texec i (Iget k r ro f) None rt 
        (Some (BinNatMap.update _ rt r ((ko U (se i)) U' (DEX_ft p f))))

    | iput : forall i ks ko (rt:TypeRegisters) (k:DEX_ValKind) (rs:DEX_Reg) (ro:DEX_Reg) (f:DEX_FieldSignature),
      BinNatMap.get _ rt rs = Some ks ->
      BinNatMap.get _ rt ro = Some ko ->
      ((se i) U ko) U' ks <=' (DEX_ft p f) ->
      sgn.(DEX_heapEffect) <= (DEX_ft p f) ->
      texec i (Iput k rs ro f) None rt (Some rt)

(*    | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
    | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)

    | invokevirtual : forall i ro ko (rt:TypeRegisters) (m:DEX_MethodSignature) (n:Z) (par:list DEX_Reg),
      hd_error par = Some ro ->
      BinNatMap.get _ rt ro = Some ko ->
      length par = length (DEX_METHODSIGNATURE.parameters (snd m)) ->
      compat_type_rt_lvt (DEX_virtual_signature p (snd m) ko) (rt) (par) (Z.to_nat n) ->
      ko <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) -> 
      sgn.(DEX_heapEffect) <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) ->
      (* DEX *) (se i) <= (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect) ->
      compat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_virtual_signature p (snd m) ko).(DEX_resType) -> 
      texec i (Invokevirtual m n par) None rt
      (Some (update_op rt ret
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
      (Some (update_op rt ret
            (join_op (se i) (DEX_static_signature p (snd m)).(DEX_resType)) ))
(*
    | Invokeinterface (m:MethodSignature) (n:Z) (p:list Var)
*)
*)
    | DEX_ineg : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      BinNatMap.get _ rt rs = Some ks ->
      texec i (DEX_Ineg r rs) (* None *) rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_inot : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      BinNatMap.get _ rt rs = Some ks ->
      texec i (DEX_Inot r rs) (* None *) rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_i2b : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      BinNatMap.get _ rt rs = Some ks ->
      texec i (DEX_I2b r rs) (* None *) rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_i2s : forall i ks (rt:TypeRegisters) (r:DEX_Reg) (rs:DEX_Reg),
      BinNatMap.get _ rt rs = Some ks ->
      texec i (DEX_I2s r rs) (* None *) rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | DEX_ibinop : forall i ka kb (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (ra:DEX_Reg) (rb:DEX_Reg),
      BinNatMap.get _ rt ra = Some ka ->
      BinNatMap.get _ rt rb = Some kb ->
      texec i (DEX_Ibinop op r ra rb) (* None *) rt 
       (Some (BinNatMap.update _ rt r (L.Simple ((ka U kb) U (se i)))))
    
    | DEX_ibinopConst : forall i ks (rt:TypeRegisters) (op:DEX_BinopInt) (r:DEX_Reg) (rs:DEX_Reg) (v:Z),
      BinNatMap.get _ rt rs = Some ks ->
      texec i (DEX_IbinopConst op r rs v) (* None *) rt 
       (Some (BinNatMap.update _ rt r (L.Simple (ks U (se i)))))   
    .

    Section DEX_RT.
      Variable RT : DEX_PC -> TypeRegisters.

    Definition tsub_next (i:DEX_PC) (rt:TypeRegisters) : bool :=
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
(* 
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
            | Some k => L.leql_t k (DEX_lvt s (N_toReg (q)%nat))
            end && tcompat_type_rt_lvt_aux s rt p q
          end
      end.

    Lemma tcompat_type_rt_lvt_aux_true : forall s rt p n,
      tcompat_type_rt_lvt_aux s rt p n = true ->
      forall x, ((Reg_toN x)<n)%nat -> exists r k,
        nth_error p (Reg_toN x) = Some r /\ BinNatMap.get _ rt r = Some k /\
        L.leql k (DEX_lvt s x).
    Proof.
      induction n. simpl.
      intros.
      apply False_ind; omega. simpl.

      caseeq (nth_error p n); intros.
      elim andb_prop with (1:=H0); clear H0; intros.
      destruct (BinNatMap.get t rt d) eqn:H3; intros.
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
    Qed. *)

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
        | DEX_Nop, rt1 =>
          tsub_next i rt1

        | DEX_Move _ r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some k_rs =>
                (* (if in_dec Reg_eq_dec r locR then
                   L.leql_t (se i) (sgn.(DEX_lvt) r) &&
                   leql'_test k_rs (sgn.(DEX_lvt) r)
                   else true) &&  *)
                tsub_next i (BinNatMap.update _ rt1 r (L.join (se i) (k_rs)))
            | None => false
          end
(* DEX Method        
        | MoveResult _ r, rt1 =>
          match BinNatMap.get _ rt1 ret with
            | Some k_ret =>
              (if in_dec Reg_eq_dec r (locR p method_signature) then
                 L.leql_t (se i) (sgn.(DEX_lvt) r) &&
                 leql'_test k_ret (sgn.(DEX_lvt) r)
               else true)
               && 
               (tsub_next i (BinNatMap.update _ rt1 r (L.join' (se i) (k_ret))))
            | None => false
          end
*)

        | DEX_Return, rt1 =>
          match sgn.(DEX_resType) with
            | None => true
            | _ => false
          end

        | DEX_VReturn _ r, rt1 =>          
          match sgn.(DEX_resType) with
            | None => false
            | Some kv => 
              match BinNatMap.get _ rt1 r with
                | None => false
                | Some k => leql_t (se i U k) kv 
              end
          end

        | DEX_Const _ r _, rt1 =>
          tsub_next i (BinNatMap.update _ rt1 r (L.Simple (se i)))

(* DEX Object
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
*)
        | DEX_Goto o, rt1 => tsub_rt rt1 (RT (DEX_OFFSET.jump i o))

(* Hendra 11082016 focus on DEX I - 
        | DEX_PackedSwitch r _ _ l, rt1 =>
          match BinNatMap.get _ rt1 r with
            | None => false
            | Some k => (selift i None k) && (tsub_next i (lift_rt k rt1)) &&
               (for_all _
                 (fun o => tsub_rt (lift_rt k rt1) (RT ((*DEX_OFFSET.*)jumpAddress i o))) l)  
          end
   
        | DEX_SparseSwitch r _ l, rt1 =>
          match BinNatMap.get _ rt1 r with
            | None => false
            | Some k => (selift i None k) && (tsub_next i (lift_rt k rt1)) &&
               (for_all _
                 (fun o => tsub_rt (lift_rt k rt1) (RT ((*DEX_OFFSET.*)jumpAddress i o)))
                 (@map _ _ (@snd _ _) l))
          end
*)    
        | DEX_Ifcmp _ ra rb o, rt1 =>
          match BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 rb with
            | Some ka, Some kb =>
                (selift i (* None *) (ka U kb)) && 
                (tsub_next i (*lift_rt (ka U kb) rt1*) rt1) &&
                (tsub_rt (*lift_rt (ka U kb) rt1*) rt1 (RT (DEX_OFFSET.jump i o)))
            | _, _ => false
          end

        | DEX_Ifz _ r o, rt1 =>
          match BinNatMap.get _ rt1 r with
            | Some k => 
                (selift i (* None *) k) && 
                (tsub_next i (*lift_rt k rt1*)rt1) &&
                (tsub_rt (*lift_rt k rt1*) rt1 (RT (DEX_OFFSET.jump i o)))
            | None => false
          end        

(* DEX Object and Method
        | Aget _ r ra ri, rt1 =>
          match BinNatMap.get _ rt1 ri, BinNatMap.get _ rt1 ra with
            | Some ki, Some (L.Array ka kc) =>
                tsub_next i (BinNatMap.update _ rt1 r ((ka U ki) U' kc))
            | _, _ => false
          end

        | Aput _ rs ra ri, rt1 =>
          match BinNatMap.get _ rt1 rs, BinNatMap.get _ rt1 ri, BinNatMap.get _ rt1 ra with
            | Some ks, Some ki, Some (L.Array ka kc) =>
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
              (beq_nat (Z.to_nat n) (length (DEX_METHODSIGNATURE.parameters (snd m)))) &&
              (beq_nat (Z.to_nat n) (length (ro::par))) &&
              (tcompat_type_rt_lvt (DEX_virtual_signature p (snd m) ko) (rt1) ((ro::par)) (Z.to_nat n)) &&
              (L.leql_t ko (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (L.leql_t sgn.(DEX_heapEffect) (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (L.leql_t (se i) (DEX_virtual_signature p (snd m) ko).(DEX_heapEffect)) &&
              (tcompat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_virtual_signature p (snd m) ko).(DEX_resType)) &&
              (tsub_next i (update_op rt1 ret 
                           (join_op (ko U (se i)) (DEX_virtual_signature p (snd m) ko).(DEX_resType))) )
            | None => false    
          end

        | Invokestatic m n par, rt1 =>
            (beq_nat (Z.to_nat n) (length (DEX_METHODSIGNATURE.parameters (snd m)))) &&
            (beq_nat (Z.to_nat n) (length par)) &&
            (tcompat_type_rt_lvt (DEX_static_signature p (snd m)) (rt1) (par) (Z.to_nat n)) &&
            (L.leql_t sgn.(DEX_heapEffect) (DEX_static_signature p (snd m)).(DEX_heapEffect)) &&
            (L.leql_t (se i) (DEX_static_signature p (snd m)).(DEX_heapEffect)) &&
            (tcompat_op (DEX_METHODSIGNATURE.result (snd m)) (DEX_static_signature p (snd m)).(DEX_resType)) &&
            (tsub_next i (update_op rt1 ret 
                         (join_op (se i) (DEX_static_signature p (snd m)).(DEX_resType))) )
*)

        | DEX_Ineg r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_Inot r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_I2b r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end

        | DEX_I2s r rs, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((se i) U ks))) )
            | None => false
          end   

        | DEX_Ibinop _ r ra rb, rt1 =>
          match BinNatMap.get _ rt1 ra, BinNatMap.get _ rt1 rb with
            | Some ka, Some kb => 
               (tsub_next i (BinNatMap.update _ rt1 r (L.Simple ((ka U kb) U (se i)))) )
            | _, _ => false
          end   

        | DEX_IbinopConst _ r rs _, rt1 =>
          match BinNatMap.get _ rt1 rs with
            | Some ks => (tsub_next i (BinNatMap.update _ rt1 r (L.Simple (ks U (se i)))) )
            | None => false
          end   
(*
        | _, _ => false
*)
      end.

   Ltac flatten_bool :=
     repeat match goal with
       [ id : _ && _ = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
     end.

   Variable selift_prop : forall i (* tau *) k,
     selift i (* tau *) k = true ->
     forall j, region i (* tau *) j -> k <= (se j).

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
     (* forall tau,  *)DEX_step (* p subclass_test *) m i ins (* tau *) None ->
       texec i ins (* tau *) (RT i) None.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck (* DEX step.handler, exception_test, exception_test' *) in *.
     (* Return *)
     try discriminate; flatten; constructor; auto.
     destruct (DEX_resType sgn); congruence.

     (* VReturn *)
     destruct (DEX_resType sgn) eqn:H1.
     destruct (BinNatMap.get t (RT i) rt) eqn:H2. 
     apply DEX_vReturn with (k_r:=t1) (kv:=t0). 
     rewrite H2; reflexivity. apply H1.
    generalize (leql_t_spec (se i U t1) t0); intros.
    rewrite H in H0; auto.
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
(* 
   Lemma option_same : 
   forall i,
     match M.get codes i with
       | Some p => fst (snd p)
       | None => None
      end = match M.get codes i with
              | Some p => fst (snd p)
              | None => None
            end.
   Proof.
     intros. caseeq (M.get codes i). trivial. trivial.
   Qed.

   Lemma nextAddress_same : forall i, nextAddress i = 
     DEX_Step.nextAddress codes i.
   Proof.
     intros. unfold nextAddress, DEX_Step.nextAddress.
     apply option_same.
   Qed. *)

   (* Ltac rewrite_nextAddress :=
     try match goal with
       [ id1 : DEX_Step.nextAddress _ _ = _ |- _ ] => rewrite <- nextAddress_same in id1
         end.
 *)
   Ltac flatten2 := flatten; (* rewrite_nextAddress; *) replace_tsub_next; search_tsub.

   Hint Constructors texec : texec.
(*
   Lemma map_deterministic : 
   forall (A:Type) (m:M.t A) i r1 r2, 
     M.get m i = r1 ->
     M.get m i = r2 -> r1 = r2.
   Proof.
     intros.
     revert r2 H0.
     induction H.
       intros r2. trivial.
   Qed.
*)

   Lemma tcheck_correct2 : forall i ins,
     DEX_tcheck i ins = true ->
     forall (* tau  *)j, DEX_step (* DEX p subclass_test *) (* codes jumpAddress *) m i ins (* tau *) (Some j) ->
       exists rt,
       texec i ins (* tau *) (RT i) (Some rt)
       /\ tsub_rt rt (RT j) = true.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold DEX_tcheck (* DEX step.handler, exception_test, exception_test'*) in *;
       try (split_match; intuition; subst; try discriminate; 
         flatten2; eauto with texec; fail);
    try (destruct (BinNatMap.get t' (RT i) rs) eqn:Hrs; try (inversion H; fail);
     flatten2; constructor; apply Hrs; fail);
    try (
     destruct (BinNatMap.get t (RT i) rs) eqn:Hrs; try (inversion H; fail);
     split_match; intuition; try discriminate; flatten2; constructor; auto; fail).
     (* move *)
     
     (* (*destruct (in_dec Reg_eq_dec rt locR) eqn:HlocR.*)
     (* flatten_bool. replace_leql.*)
     (* apply DEX_move_constrained.
       apply i0.
       apply Hrs. 
       apply H. apply H3.
     apply DEX_move_unconstrained.
       apply n.
       rewrite Hrs; reflexivity. *)
    apply DEX_move; auto. *)
(*
     (* moveresult *)
     destruct (BinNatMap.get t' (RT i) ret) eqn:Hrs; try (inversion H; fail).
     destruct (in_dec Reg_eq_dec rt (locR p method_signature)) eqn:HlocR.
     flatten_bool; replace_leql; replace_tsub_next; search_tsub.
     apply moveResult_constrained.
       apply i0.
       apply Hrs.
       apply H.
       apply H3.
     flatten_bool; replace_tsub_next; search_tsub.
     apply moveResult_unconstrained.
       apply n.
       apply Hrs.
     (* InstanceOf *)
     destruct (BinNatMap.get t' (RT i) r) eqn:Hrs; try (inversion H; fail).
     flatten2; apply instanceOf.
     apply Hrs.
     apply H0.
     (* Arraylength *)
     destruct (BinNatMap.get t' (RT i) rs) eqn:Hrs; try (inversion H; fail).
     split_match; try (inversion H; fail).
     flatten_bool; replace_leql; replace_tsub_next; search_tsub.
     apply arrayLength with (ke:=t0); apply Hrs.
     (* NewArray *)
     destruct (BinNatMap.get t' (RT i) rl) eqn:Hrl; try (inversion H; fail).
     flatten2; apply newArray; apply Hrl.
 *) 
     (* Ifcmp *)
     destruct (BinNatMap.get t (RT i) ra) eqn:Hra; try (inversion H; fail).
     destruct (BinNatMap.get t (RT i) rb) eqn:Hrb; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1.
       (* next successor *)
       replace_tsub_next; search_tsub.
       apply DEX_ifcmp with (ka:=t0) (kb:=t1). apply Hra. apply Hrb. apply H.
       (* target successor *) 
       rewrite H0. exists (*lift_rt (t0 U t1) (RT i)*) (RT i). split. 
       apply DEX_ifcmp with (ka:=t0) (kb:=t1). apply Hra. apply Hrb. apply H. exact H2.
     (* Ifcmp *)
     destruct (BinNatMap.get t (RT i) r) eqn:Hr; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1.
       (* next successor *)
       (* rewrite_nextAddress; *) replace_tsub_next; search_tsub.
       apply DEX_ifz with (k:=t0). apply Hr. apply H.
       (* target successor *) 
       rewrite H0. exists (*lift_rt t0 (RT i)*) (RT i). split. 
       apply DEX_ifz with (k:=t0). apply Hr. apply H. exact H2.
(*
     (* Aget *)
     destruct (BinNatMap.get t' (RT i) ri) eqn:Hri; try (inversion H; fail).
     destruct (BinNatMap.get t' (RT i) ra) eqn:Hra; try (inversion H; fail).
     split_match; try (inversion H; fail).
     flatten2. apply aget. apply Hra. apply Hri.
     (* Aput *)
     destruct (BinNatMap.get t' (RT i) rs) eqn:Hrs; try (inversion H; fail).
     destruct (BinNatMap.get t' (RT i) ri) eqn:Hri; try (inversion H; fail).
     destruct (BinNatMap.get t' (RT i) ra) eqn:Hra; try (inversion H; fail).
     split_match; try (inversion H; fail).
     flatten2. apply aput with (ks:=t0) (ka:=k0) (kc:=t2) (ki:=t1).
     apply Hrs. apply Hri. apply Hra. apply H. apply H5. apply H4. apply H3.
     (* Iget *)
     destruct (BinNatMap.get t' (RT i) ro) eqn:Hro; try (inversion H; fail);
     flatten2; apply iget; apply Hro.
     (* Iput *)
     destruct (BinNatMap.get t' (RT i) rs) eqn:Hrs; try (inversion H; fail).
     destruct (BinNatMap.get t' (RT i) ro) eqn:Hro; try (inversion H; fail).
     flatten2; apply iput with (ks:=t0) (ko:=t1). apply Hrs. apply Hro. apply H. apply H3.
     (* Invokevirtual *)
     destruct p0 eqn:Hp0; try (inversion H; fail).
     destruct (BinNatMap.get t' (RT i) d) eqn:Hro; try (inversion H; fail).
     flatten2. apply invokevirtual with (ro:=d). 
     trivial. apply Hro. apply eq_trans with (y:=(Z.to_nat n)).
     symmetry; apply beq_nat_eq; auto. 
     apply beq_nat_eq; auto.
     apply tcompat_type_rt_lvt_true; auto. 
     apply H6. apply H5. apply H4.
     apply tcompat_op_true; auto.
     (* Invokestatic *)
     flatten2. apply invokestatic. 
     apply eq_trans with (y:=(Z.to_nat n)).
     symmetry; apply beq_nat_eq; auto. 
     apply beq_nat_eq; auto.
     apply tcompat_type_rt_lvt_true; auto. 
     apply H4. apply H5.
     apply tcompat_op_true; auto.
*)
     (* Ibinop *)
     destruct (BinNatMap.get t (RT i) ra) eqn:Hra; try (inversion H; fail).
     destruct (BinNatMap.get t (RT i) rb) eqn:Hrb; try (inversion H; fail).
     flatten2; apply DEX_ibinop. apply Hra. apply Hrb.
     (* IbinopConst *)
     destruct (BinNatMap.get t (RT i) r) eqn:Hr; try (inversion H; fail);
     flatten2; apply DEX_ibinopConst; apply Hr.
(* Hendra 11082016 focus on DEX I - 
     (* PackedSwitch *)
     destruct (BinNatMap.get t' (RT i) rt) eqn:Hr; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1. 
       (* default successor *)
       exists (lift_rt t0 (RT i)); split. apply DEX_packedSwitch.
       apply Hr. apply H. inversion H0. unfold tsub_next in H3.
        inversion H4.
       rewrite_nextAddress.
       rewrite H5 in H3. rewrite <- H6. apply H3.
       (* other successors *)
       exists (lift_rt t0 (RT i)); split. apply DEX_packedSwitch.
       apply Hr. apply H. replace_for_all. apply H2.
     (* SparseSwitch *)
     destruct (BinNatMap.get t' (RT i) rt) eqn:Hr; try (inversion H; fail).
     flatten_bool; replace_selift. inversion H1. 
       (* default successor *)
       exists (lift_rt t0 (RT i)); split. apply DEX_sparseSwitch.
       apply Hr. apply H. inversion H0. unfold tsub_next in H3.
       inversion H4.
       rewrite_nextAddress. 
       rewrite H5 in H3. rewrite <- H6. apply H3.
       (* other successors *)
       exists (lift_rt t0 (RT i)); split. apply DEX_sparseSwitch.
       apply Hr. apply H. replace_for_all. apply H2.
*)
   Qed.
 End DEX_RT.
End DEX_typing_rules.

(* End Make. *)