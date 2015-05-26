(** typing_rules.v: Typing rules, plus an executable type checker *)
Require Export JVM_BigStepAnnot.
Require Export Bool.
Require Export JVM_step.
Import JVM_StaticHandler.JVM_StaticHandler JVM_BigStep.JVM_BigStep JVM_Dom.JVM_Prog.

Import Level.L.
Open Scope type_scope.

  Section JVM_typing_rules.   (** Typing rules **)
    Variable JVM_p : JVM_ExtendedProgram.
    Variable subclass_test : JVM_ClassName -> JVM_ClassName -> bool.
    Variable subclass_test_correct :
      forall c1 c2,
        if subclass_test c1 c2 then subclass_name JVM_p.(JVM_prog) c1 c2
          else ~ subclass_name JVM_p.(JVM_prog) c1 c2.
    Variable m : JVM_Method.
    Variable sgn : JVM_sign.
    Variable region : JVM_PC -> JVM_tag -> JVM_PC -> Prop.
    Variable se : JVM_PC -> L.t.
    Variable selift : JVM_PC -> JVM_tag -> L.t -> bool.
(* DEX
    Notation handler := (handler subclass_test m).
*)
    Infix "<=" := L.leql (at level 70).
    Infix "<='" := L.leql' (at level 70).
    Infix "U'" := L.join' (at level 60, right associativity).
    Infix "U" := L.join (at level 60, right associativity).

    Inductive texec : JVM_PC -> JVM_Instruction -> JVM_tag -> TypeStack -> option TypeStack -> Prop :=
    | aconst_null : forall i st,
      texec i Aconst_null None st (Some (L.Simple (se i)::st))
    | arraylength : forall i k ke st,
      (forall j, region i None j -> k <= se j) -> 
      (* DEX texec i Arraylength None (L.Array k ke::st)  (Some (L.Simple k::(elift m i k st))) *)
      texec i Arraylength None (L.Array k ke::st)  (Some (L.Simple k::st)) 
(* DEX 
    | arraylength_np_caught : forall i t (k:L.t') st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      handler i np = Some t ->
      texec i Arraylength (Some np) (k::st)  (Some (L.Simple k::nil))
    | arraylength_np_uncaught : forall i (k:L.t') st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i Arraylength (Some np) (k::st) None
    | athrow_caught : forall e i t k st,
      In e (Dom.Prog.throwableAt m i) ->
      handler i e = Some t ->
      (forall j, region i (Some e) j -> k <= se j) -> 
      texec i Athrow (Some e) (L.Simple k::st) (Some (L.Simple k::nil))
    | athrow_uncaught : forall e i k st,
      In e (Dom.Prog.throwableAt m i) ->
      k <= sgn.(resExceptionType) e ->
      handler i e = None ->
      (forall j, region i (Some e) j -> k <= se j) -> 
      texec i Athrow (Some e) (L.Simple k::st) None
    | checkcast1 : forall i t (k:L.t') st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Checkcast t) None (k::st) (Some (k::elift m i k st))
    | checkcast_caught : forall i t te (k:L.t') st,
      (forall j, region i (Some cc) j -> k <= se j) -> 
      handler i cc = Some te ->
      texec i (Checkcast t) (Some cc) (k::st) (Some (L.Simple k::nil))
    | checkcast_uncaught : forall i t (k:L.t') st,
      (forall j, region i (Some cc) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) cc ->
      handler i cc = None ->
      texec i (Checkcast t) (Some cc) (k::st) None
*)
    | const : forall i t z st,
      texec i (Const t z) None st (Some (L.Simple (se i)::st))
    | dup : forall i k st,
      texec i Dup None (k::st) (Some (k::k::st))
    | dup_x1 : forall i k1 k2 st,
      texec i Dup_x1 None  (k1::k2::st) (Some (k1::k2::k1::st))
    | dup_x2 : forall i k1 k2 k3 st,
      texec i Dup_x2 None (k1::k2::k3::st) (Some (k1::k2::k3::k1::st))
    | dup2 : forall i k1 k2 st,
      texec i Dup2 None (k1::k2::st) (Some (k1::k2::k1::k2::st))
    | dup2_x1 : forall i k1 k2 k3 st,
      texec i Dup2_x1 None (k1::k2::k3::st) (Some (k1::k2::k3::k1::k2::st))
    | dup2_x2 : forall i k1 k2 k3 k4 st,
      texec i Dup2_x2 None (k1::k2::k3::k4::st) (Some (k1::k2::k3::k4::k1::k2::st))
    | getfield : forall i f k st,
      (forall j, region i None j -> k <= se j) -> 
      (* DEX texec i (Getfield f) None (L.Simple k::st) (Some ((k U' (ft p f))::(elift m i k st))) *)
      texec i (Getfield f) None (L.Simple k::st) (Some ((k U' (JVM_ft JVM_p f))::st))
(* DEX
    | getfield_np_caught : forall i t f k st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      handler i np = Some t ->
      texec i (Getfield f) (Some np) (L.Simple k::st) (Some (L.Simple k::nil))
    | getfield_np_uncaught : forall i f k st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Getfield f) (Some np) (L.Simple k::st) None
*)
    | goto : forall i o st,
      texec i (Goto o) None st (Some st)
    | i2b : forall i k st,
      texec i I2b None (L.Simple k::st) (Some (L.Simple k::st))
    | i2s : forall i k st,
      texec i I2s None (L.Simple k::st) (Some (L.Simple k::st))
    | ibinop : forall i op k1 k2 st st',
(* DEX
      (match op with 
                | DivInt => forall j, region i None j -> k1 <= se j 
                | RemInt => forall j, region i None j -> k1 <= se j 
                | _ => True
              end) ->   
      st' =  (match op with 
                | DivInt => elift m i k1 st
                | RemInt => elift m i k1 st
                | _ => st
              end)->
*)
      texec i (Ibinop op) None (L.Simple k1::L.Simple k2::st) (Some (L.Simple (L.join k1 k2)::st'))
(* DEX
    | ibinop_ae_caught : forall i t op k1 k2 st,
      (forall j, region i (Some ae) j -> k1 <= se j) -> 
      op = DivInt \/ op = RemInt ->
      handler i ae = Some t ->
      texec i (Ibinop op) (Some ae) (L.Simple k1::L.Simple k2::st) (Some (L.Simple k1::nil))
    | ibinop_ae_uncaught : forall i op k1 k2 st,
      (forall j, region i (Some ae) j -> k1 <= se j) -> 
      k1 <= sgn.(resExceptionType) ae ->
      op = DivInt \/ op = RemInt ->
      handler i ae = None ->
      texec i (Ibinop op) (Some ae) (L.Simple k1::L.Simple k2::st) None
*)
    | if_acmp : forall i cmp o k1 k2 st,
      (forall j, region i None j -> L.join k1 k2 <= se j) -> 
      texec i (If_acmp cmp o) None (L.Simple k1::L.Simple k2::st) (Some (lift_st (L.join k1 k2) st))
    | if_icmp : forall i cmp o k1 k2 st,
      (forall j, region i None j -> L.join k1 k2 <= se j) -> 
      texec i (If_icmp cmp o) None (L.Simple k1::L.Simple k2::st) (Some (lift_st (L.join k1 k2) st))
    | ifeq : forall i cmp o k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (If0 cmp o) None (L.Simple k::st) (Some (lift_st k st))
    | ifnull : forall i cmp o (k:L.t') st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Ifnull cmp o) None (k::st) (Some (lift_st k st))
    | iinc : forall i x c st,
      se i <= sgn.(JVM_lvt) x -> 
      texec i (Iinc x c) None st (Some st)
    | ineg : forall i k st,
      texec i Ineg None (k::st) (Some (k::st))
    | instanceof : forall i t (k:L.t') st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Instanceof t) None (k::st) (Some (k::st))
    | invokestatic : forall i (mid:JVM_MethodSignature) st1 st2,
      length st1 = length (JVM_METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (JVM_static_signature JVM_p (snd mid)) (st1++st2) (length st1) ->
      se i <= (JVM_static_signature JVM_p (snd mid)).(JVM_heapEffect) -> 
(* DEX
      (forall j, region i None j -> 
        join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid)) <= se j) ->
*)
      compat_op (JVM_METHODSIGNATURE.result (snd mid)) (JVM_static_signature JVM_p (snd mid)).(JVM_resType) ->
      sgn.(JVM_heapEffect) <= (JVM_static_signature JVM_p (snd mid)).(JVM_heapEffect) -> 
      texec i (Invokestatic mid) None 
      (st1++st2)
(* DEX
      (Some (lift (join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid))) 
        (cons_option (join_op (se i) (static_signature p (snd mid)).(resType)) st2)))
*)
      (Some (cons_option (join_op (se i) (JVM_static_signature JVM_p (snd mid)).(JVM_resType)) st2))
(* DEX
    | invokestatic_caught : forall i (mid:MethodSignature) st1 st2 cn,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (static_signature p (snd mid)) (st1++st2) (length st1) ->
      se i <= (static_signature p (snd mid)).(heapEffect) -> 
      (forall j, region i (Some cn) j -> 
        (static_signature p (snd mid)).(resExceptionType) cn <= se j) ->
      sgn.(heapEffect) <= (static_signature p (snd mid)).(heapEffect) -> 
      texec i (Invokestatic mid) (Some cn)
      (st1++st2)
      (Some (L.Simple (L.join (se i) ((static_signature p (snd mid)).(resExceptionType) cn))::nil))
    | invokestatic_uncaught : forall i (mid:MethodSignature) st1 st2 cn,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (static_signature p (snd mid)) (st1++st2) (length st1) ->
      se i <= (static_signature p (snd mid)).(heapEffect) -> 
      (forall j, region i (Some cn) j -> 
        (static_signature p (snd mid)).(resExceptionType) cn <= se j) ->
      se i <= (sgn.(resExceptionType) cn) -> 
      ((static_signature p (snd mid)).(resExceptionType) cn) <= (sgn.(resExceptionType) cn) -> 
      sgn.(heapEffect) <= (static_signature p (snd mid)).(heapEffect) -> 
      texec i (Invokestatic mid) (Some cn)
      (st1++st2) None
*)
    | invokevirtual : forall i (mid:JVM_MethodSignature) st1 k1 st2,
      length st1 = length (JVM_METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (JVM_virtual_signature JVM_p (snd mid) k1) (st1++L.Simple k1::st2) (1+(length st1)) ->
      k1 <= (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_heapEffect) -> 
(* DEX
      (forall j, region i None j -> 
        L.join (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid)))
        k1 <= se j) ->
*)
      compat_op (JVM_METHODSIGNATURE.result (snd mid)) (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_resType) ->
      sgn.(JVM_heapEffect) <= (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_heapEffect) -> 
      texec i (Invokevirtual mid) None 
      (st1++L.Simple k1::st2) 
(* DEX
      (Some (lift k1 (lift (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) 
        (cons_option (join_op k1 (virtual_signature p (snd mid) k1).(resType)) st2))))
*)
      (Some (lift_st k1 (cons_option (join_op k1 (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_resType)) st2)))
(* DEX
    | invokevirtual_caught : forall i (mid:MethodSignature) st1 k1 st2 cn,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (virtual_signature p (snd mid) k1) (st1++L.Simple k1::st2) (1+(length st1)) ->
      k1 <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      (forall j, region i (Some cn) j -> 
        L.join ((virtual_signature p (snd mid) k1).(resExceptionType) cn)
        k1 <= se j) ->
      sgn.(heapEffect) <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      texec i (Invokevirtual mid) (Some cn)
      (st1++L.Simple k1::st2) 
      (Some (lift k1 (L.Simple (L.join k1 ((virtual_signature p (snd mid) k1).(resExceptionType) cn))::nil))) 
    | invokevirtual_uncaught : forall i (mid:MethodSignature) st1 k1 st2 cn,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (virtual_signature p (snd mid) k1) (st1++L.Simple k1::st2) (1+(length st1)) ->
      k1 <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      (forall j, region i (Some cn) j -> 
        L.join ((virtual_signature p (snd mid) k1).(resExceptionType) cn)
        k1 <= se j) ->
      k1 <= (sgn.(resExceptionType) cn) -> 
      ((virtual_signature p (snd mid) k1).(resExceptionType) cn) <= (sgn.(resExceptionType) cn) -> 
      sgn.(heapEffect) <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      texec i (Invokevirtual mid) (Some cn)
      (st1++L.Simple k1::st2)  None
*)
    | lookupswitch : forall i d l k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Lookupswitch d l) None (L.Simple k::st) (Some (lift_st k st))
    | new : forall i c st,
      texec i (New c) None st (Some (L.Simple (se i)::st))
    | newarray : forall i t k st,
      (forall j, region i None j -> k <= se j) -> 
(* DEX      texec i (Newarray t) None (L.Simple k::st) (Some (L.Array k (newArT p (m,i))::elift m i k st)) *)
      texec i (Newarray t) None (L.Simple k::st) (Some (L.Array k (JVM_newArT JVM_p (m,i))::st))
(* DEX
    | newarray_nase_caught : forall i t te k st,
      (forall j, region i (Some nase) j -> k <= se j) -> 
      handler i nase = Some te ->
      texec i (Newarray t) (Some nase) (L.Simple k::st) (Some (L.Simple k::nil))
    | newarray_nase_uncaught : forall i t k st,
      (forall j, region i (Some nase) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) nase ->
      handler i nase = None ->
      texec i (Newarray t) (Some nase) (L.Simple k::st) None
*)
    | nop : forall i st,
      texec i Nop None st (Some st)
    | pop : forall i k st,
      texec i Pop None (k::st) (Some st)
    | pop2 : forall i k1 k2 st,
      texec i Pop2 None (k1::k2::st) (Some st)
    | putfield : forall i f k1 k2 st,
      k1 <=' JVM_ft JVM_p f -> 
      k2 <= JVM_ft JVM_p f -> 
      se i <= JVM_ft JVM_p f -> 
      sgn.(JVM_heapEffect) <= JVM_ft JVM_p f -> 
      (forall j, region i None j -> k2 <= se j) -> 
(* DEX      texec i (Putfield f) None (k1::L.Simple k2::st) (Some (elift m i k2 st)) *)
      texec i (Putfield f) None (k1::L.Simple k2::st) (Some (st))
(* DEX
    | putfield_np_caught : forall i t f k1 k2 st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      handler i np = Some t ->
      texec i (Putfield f) (Some np) (k1::L.Simple k2::st) (Some (L.Simple k2::nil))
    | putfield_np_uncaught : forall i f k1 k2 st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      k2 <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Putfield f) (Some np) (k1::L.Simple k2::st) None
*)
    | return_ : forall i st,
      sgn.(JVM_resType) = None ->
      texec i Return None st None
    | swap : forall i k1 k2 st,
      texec i Swap None (k1::k2::st) (Some (k2::k1::st))
    | tableswitch : forall i d lo hi l k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Tableswitch d lo hi l) None (L.Simple k::st) (Some (lift_st k st))
    | vaload : forall i t k1 k2 ke st,
      (forall j, region i None j -> k2 <= se j) -> 
      (forall j, region i None j -> (L.join k1 k2) <= se j) -> 
(* DEX      texec i (Vaload t)  None (L.Simple k1::L.Array k2 ke::st) (Some (L.join' (L.join k1 k2) ke::elift m i (L.join k1 k2) st)) *)
      texec i (Vaload t)  None (L.Simple k1::L.Array k2 ke::st) (Some (L.join' (L.join k1 k2) ke::st))
(* DEX
    | vaload_np_caught : forall i te t k1 k2 ke st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      handler i np = Some te ->
      texec i (Vaload t) (Some np) (L.Simple k1::L.Array k2 ke::st) (Some (L.Simple k2::nil))
    | vaload_np_uncaught : forall i t k1 k2 ke st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      k2 <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Vaload t) (Some np) (L.Simple k1::L.Array k2 ke::st) None
    | vaload_iob_caught : forall i te t k1 k2 ke st,
      (forall j, region i (Some iob) j -> k1 U k2 <= se j) -> 
      handler i iob = Some te ->
      texec i (Vaload t) (Some iob) (L.Simple k1::L.Array k2 ke::st) (Some (L.Simple (k1 U k2)::nil))
    | vaload_iob_uncaught : forall i t k1 k2 ke st,
      (forall j, region i (Some iob) j -> k1 U k2 <= se j) -> 
      k1 U k2 <= sgn.(resExceptionType) iob ->
      handler i iob = None ->
      texec i (Vaload t) (Some iob) (L.Simple k1::L.Array k2 ke::st) None
*)
    | vastore : forall i t kv ki ka ke st,
      kv <=' ke -> 
      ki <= ke -> 
      ka <= ke ->
      (forall j, region i None j -> ka <= se j) -> 
      (forall j, region i None j -> (L.join ki ka) <= (se j)) -> 
      (forall j, region i None j -> ke <= (se j)) -> 
      L.leql (JVM_heapEffect sgn) ke ->
(* DEX      texec i (Vastore t) None (kv::L.Simple ki::L.Array ka ke::st) (Some (elift m i ke st)) *)
      texec i (Vastore t) None (kv::L.Simple ki::L.Array ka ke::st) (Some (st))
(* DEX
    | vastore_np_caught : forall i te t kv ki ka ke st,
      (forall j, region i (Some np) j -> ka <= se j) ->
      handler i np = Some te ->
      texec i (Vastore t) (Some np) (kv::L.Simple ki::L.Array ka ke::st) (Some (L.Simple ka::nil))
    | vastore_np_uncaught : forall i t kv ki ka ke st,
      (forall j, region i (Some np) j -> ka <= se j) -> 
      ka <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Vastore t) (Some np) (kv::L.Simple ki::L.Array ka ke::st) None
    | vastore_ase_caught : forall i te t ki ka (kv ke:L.t') st,
      (forall j, region i (Some ase) j -> (L.join kv (L.join ki ka)) <= se j) ->
      handler i ase = Some te ->
      texec i (Vastore t) (Some ase) (kv::L.Simple ki::L.Array ka ke::st) (Some (L.Simple (L.join kv (L.join ki ka))::nil))
    | vastore_ase_uncaught : forall i t ki ka (kv ke:L.t') st,
      (forall j, region i (Some ase) j -> (L.join kv (L.join ki ka)) <= se j) -> 
      (L.join kv (L.join ki ka)) <= sgn.(resExceptionType) ase ->
      handler i ase = None ->
      texec i (Vastore t) (Some ase) (kv::L.Simple ki::L.Array ka ke::st) None
    | vastore_iob_caught : forall i te t ki ka (kv ke:L.t') st,
      (forall j, region i (Some iob) j -> (L.join ki ka) <= se j) ->
      handler i iob = Some te ->
      texec i (Vastore t) (Some iob) (kv::L.Simple ki::L.Array ka ke::st) (Some (L.Simple (L.join ki ka)::nil))
    | vastore_iob_uncaught : forall i t ki ka (kv ke:L.t') st,
      (forall j, region i (Some iob) j -> (L.join ki ka) <= se j) -> 
      (L.join ki ka) <= sgn.(resExceptionType) iob ->
      handler i iob = None ->
      texec i (Vastore t) (Some iob) (kv::L.Simple ki::L.Array ka ke::st) None
*)
    | vload : forall i t x st,
      texec i (Vload t x) None st (Some (L.join' (se i) (sgn.(JVM_lvt) x)::st))
    | vstore : forall i t x k st,
      se i <= sgn.(JVM_lvt) x -> 
      L.leql' k (sgn.(JVM_lvt) x) ->      
      texec i (Vstore t x) None (k::st) (Some st)
    | vreturn : forall i x k kv st,
      sgn.(JVM_resType) = Some kv ->
      L.leql' k kv ->      
      texec i (Vreturn x) None (k::st) None.

    Section JVM_S.
      Variable S : JVM_PC -> TypeStack.

    Definition tsub_next (i:JVM_PC) st : bool :=
      match next m i with
        | Some j => tsub_st st (S j)
        | None => false
      end.
(*
    Definition exception_test (i:PC) (e:ClassName) (k:L.t) : bool :=
      match handler i e with
        | Some t => tsub (L.Simple k::nil) (S t)
        | None => L.leql_t k (sgn.(resExceptionType) e)
      end.
*)
    Fixpoint in_test (e:JVM_ClassName) (l:list JVM_ClassName) : bool :=
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
    Definition exception_test' (i:JVM_PC) (e:JVM_ClassName) (k:L.t) : bool :=
      if in_test e (throwableAt m i) then
        match handler i e with
          | Some t => tsub (L.Simple k::nil) (S t)
          | None => L.leql_t k (sgn.(resExceptionType) e)
        end
        else true.
*)
    Fixpoint tcompat_type_st_lvt_aux (s:JVM_sign) (st:TypeStack) (n0 n:nat) {struct n} : bool :=
      match n with (* could be optimised *)
        | O => true
        | Datatypes.S q => let x := N_toVar q in
            match nth_error st (n0-n)%nat with
              | None => false
              | Some k => leql'_test k (JVM_lvt s x)
            end && tcompat_type_st_lvt_aux s st n0 q
      end.

    Lemma tcompat_type_st_lvt_aux_true : forall s st n0 n,
      tcompat_type_st_lvt_aux s st n0 n = true ->
      forall x, ((Var_toN x)<n)%nat -> exists k,
        nth_error st (n0-(Var_toN x)-1)%nat = Some k /\
        L.leql' k (JVM_lvt s x).
    Proof.
      induction n; simpl.
      intros.
      apply False_ind; omega.
      caseeq (nth_error st (n0 - Datatypes.S n)); intros.
      elim andb_prop with (1:=H0); clear H0; intros.
      elim (eq_excluded_middle _ (Var_toN x) n); intros; subst.
      replace (n0 - Var_toN x - 1)%nat with (n0 - Datatypes.S (Var_toN x))%nat.
      exists t0; split; auto. (* Hendra *)
      generalize (leql'_test_prop t0 (JVM_lvt s (N_toVar (Var_toN x)))); rewrite H0. (* Hendra *)
      rewrite Var_toN_bij1; auto.
      omega.
      apply IHn; auto.
      omega.
      simpl in H0; discriminate.
    Qed.

    Definition tcompat_type_st_lvt (s:JVM_sign) (st:TypeStack) (n:nat) : bool :=
      tcompat_type_st_lvt_aux s st n n.

    Lemma tcompat_type_st_lvt_true : forall s st n,
      tcompat_type_st_lvt s st n = true ->
      compat_type_st_lvt s st n.
    Proof.
      unfold tcompat_type_st_lvt, compat_type_st_lvt; intros.
      apply (tcompat_type_st_lvt_aux_true _ _ _ _ H); auto.
    Qed.

    Definition tcompat_op (ot:option JVM_type) (ok:option L.t') : bool :=
      match ot,ok with
        | None,None => true
        | Some _,Some _ => true
        | _,_ => false
      end.

    Lemma tcompat_op_true : forall (ot:option JVM_type) (ok:option L.t'),
      tcompat_op ot ok = true -> compat_op ot ok.
    Proof.
      destruct ot; destruct ok; simpl; intros; discriminate || constructor.
    Qed.

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

    Definition compat_type_st_lvt (s:JVM_sign) (st:TypeStack) (n:nat) : Prop :=
      forall x, ((Var_toN x)<n)%nat -> exists k,
        nth_error st (n-(Var_toN x)-1)%nat = Some k /\
        L.leql' k (JVM_lvt s x).

   Definition JVM_tcheck (i:JVM_PC) (ins:JVM_Instruction) : bool :=
      match ins,S i with
        | Aconst_null,   st1 => 
          tsub_next i (L.Simple (se i)::st1)
        | Arraylength,   (L.Array k ke::st) =>
          (selift i None k) &&
(* DEX          (tsub_next i (L.Simple k::(elift m i k st))) && *)
          (tsub_next i (L.Simple k::st)) 
(* DEX    && 
          for_all _ 
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
*)
(* DEX          
        | Athrow,        (L.Simple k::st) =>
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
        | Checkcast _,   k::st =>
          (selift i None k) &&
          (tsub_next i (k::elift m i k st)) &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
*)
        | Const _ _,       st =>
          tsub_next i (L.Simple (se i)::st) 
        | Dup,             k::st =>
          tsub_next i (k::k::st)
        | Dup_x1,          k1::k2::st =>
          tsub_next i (k1::k2::k1::st) 
        | Dup_x2,          k1::k2::k3::st =>
          tsub_next i (k1::k2::k3::k1::st) 
        | Dup2,            k1::k2::st =>
          tsub_next i (k1::k2::k1::k2::st) 
        | Dup2_x1,         k1::k2::k3::st =>
          tsub_next i (k1::k2::k3::k1::k2::st) 
        | Dup2_x2,         k1::k2::k3::k4::st =>
          tsub_next i (k1::k2::k3::k4::k1::k2::st) 
        | Getfield f,      L.Simple k::st =>
          (selift i None k) && 
          (tsub_next i ((k U' (JVM_ft JVM_p f))::st))
(* DEX
          (tsub_next i ((k U' (JVM_ft p f))::(elift m i k st))) &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
*)
        | Goto o,          st =>
          tsub_st st (S (JVM_OFFSET.jump i o)) 
        | I2b,             L.Simple k::st =>
          tsub_next i (L.Simple k::st) 
        | I2s,             L.Simple k::st =>
          tsub_next i (L.Simple k::st) 
(* DEX
        | Ibinop DivInt,       L.Simple k1::L.Simple k2::st =>
          (selift i None k1) &&
          (tsub_next i (L.Simple (L.join k1 k2)::(elift m i k1 st))) &&
          for_all _
            (fun e => (selift i (Some e) k1) && (exception_test i e k1))
            (throwableAt m i)
        | Ibinop RemInt,       L.Simple k1::L.Simple k2::st =>
          (selift i None k1) &&
          (tsub_next i (L.Simple (L.join k1 k2)::(elift m i k1 st))) &&
          for_all _
            (fun e => (selift i (Some e) k1) && (exception_test i e k1))
            (throwableAt m i)
*)
        | Ibinop _,       L.Simple k1::L.Simple k2::st =>
          tsub_next i (L.Simple (L.join k1 k2)::st)
        | If_acmp _ o,    L.Simple k1::L.Simple k2::st =>
          (selift i None (L.join k1 k2)) &&
          (tsub_next i (lift_st (L.join k1 k2) st)) &&
          (tsub_st (lift_st (L.join k1 k2) st) (S (JVM_OFFSET.jump i o)))
        | If_icmp _ o,    L.Simple k1::L.Simple k2::st =>
          (selift i None (L.join k1 k2)) &&
          (tsub_next i (lift_st (L.join k1 k2) st)) &&
          (tsub_st (lift_st (L.join k1 k2) st) (S (JVM_OFFSET.jump i o)))
        | If0 _ o,        L.Simple k::st =>
          (selift i None k) &&
          (tsub_next i (lift_st k st)) &&
          (tsub_st (lift_st k st) (S (JVM_OFFSET.jump i o)))
        | Ifnull _ o,        k::st =>
          (selift i None k) &&
          (tsub_next i (lift_st k st)) &&
          (tsub_st (lift_st k st) (S (JVM_OFFSET.jump i o)))
        | Iinc x c,         st =>
          (L.leql_t (se i) (sgn.(JVM_lvt) x)) &&
          (tsub_next i st)
        | Ineg,             k::st =>
          tsub_next i (k::st)
        | Instanceof _,     k::st =>
          (selift i None k) &&
          (tsub_next i (k::st))
        | Invokestatic mid, st =>
          let n := length (JVM_METHODSIGNATURE.parameters (snd mid)) in
          let sgn' := (JVM_static_signature JVM_p (snd mid)) in 
(* DEX          let ke' := (join_list sgn'.(resExceptionType) (throwableBy p (snd mid))) in *)
            le_nat_test n (length st) &&
            (tcompat_type_st_lvt (JVM_static_signature JVM_p (snd mid)) st n) &&
            (L.leql_t (se i) sgn'.(JVM_heapEffect)) &&
(* DEX
            (selift i None ke') && 
            for_all _
              (fun e => (selift i (Some e) (sgn'.(resExceptionType) e) &&
                        (exception_test i e (L.join (se i) (sgn'.(resExceptionType) e)))) &&
                        (L.leql_t (se i) (sgn.(resExceptionType) e))) 
              (throwableBy p (snd mid)) &&
*)
            (tcompat_op (JVM_METHODSIGNATURE.result (snd mid)) sgn'.(JVM_resType)) &&
            (L.leql_t sgn.(JVM_heapEffect) sgn'.(JVM_heapEffect)) && 
(* DEX            tsub_next i (lift_st ke' (cons_option (join_op (se i) sgn'.(JVM_resType)) (pop_n n st)))*)
            tsub_next i (cons_option (join_op (se i) sgn'.(JVM_resType)) (pop_n n st))
        | Invokevirtual mid, st =>
          let n := length (JVM_METHODSIGNATURE.parameters (snd mid)) in
            match pop_n n st with
              | (L.Simple k1)::st2 =>
                le_nat_test (Datatypes.S n) (length st) &&
                (tcompat_type_st_lvt (JVM_virtual_signature JVM_p (snd mid) k1) st (Datatypes.S n)) &&
                (L.leql_t k1 (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_heapEffect)) &&
     (* DEX           (selift i None (L.join (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) k1)) && *)
(* DEX
                (for_all _
                  (fun cn => 
                    (selift i (Some cn) (L.join ((virtual_signature p (snd mid) k1).(resExceptionType) cn) k1)) &&
                    (exception_test i cn (L.Simple (L.join k1 ((virtual_signature p (snd mid) k1).(resExceptionType) cn)))) &&
                    (L.leql_t k1 (sgn.(resExceptionType) cn)) &&
                    (L.leql_t ((virtual_signature p (snd mid) k1).(resExceptionType) cn) (sgn.(resExceptionType) cn)))
                  (throwableAt m i ++ throwableBy p (snd mid))) &&
*)
                (tcompat_op (JVM_METHODSIGNATURE.result (snd mid)) (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_resType)) &&
                (L.leql_t sgn.(JVM_heapEffect) (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_heapEffect)) &&
(* DEX                tsub_next i (lift_st k1 (lift (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) *)
                tsub_next i (lift_st k1 (cons_option (join_op k1 (JVM_virtual_signature JVM_p (snd mid) k1).(JVM_resType)) st2))
              | _ => false
            end
        | Lookupswitch d l, L.Simple k::st =>
          (selift i None k) &&
          (for_all _
            (fun o => tsub_st (lift_st k st) (S (JVM_OFFSET.jump i o)))
            (d::@map _ _ (@snd _ _) l)) &&
          tsub_next i (lift_st k st)
        | New c, st =>
          tsub_next i (L.Simple (se i)::st)
        | Newarray t, (L.Simple k::st) =>
          (selift i None k) &&
(* DEX          tsub_next i (L.Array k (JVM_newArT p (m,i))::elift m i k st) && *)
          tsub_next i (L.Array k (JVM_newArT JVM_p (m,i))::st) 
(* DEX    &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
*)
        | Nop, st => tsub_next i st
        | Pop, k::st => tsub_next i  st
        | Pop2, k1::k2::st => tsub_next i st
        | Putfield f, (k1::L.Simple k2::st) =>
          leql'_test k1 (JVM_ft JVM_p f) &&
          L.leql_t k2 (JVM_ft JVM_p f) &&
          L.leql_t (se i) (JVM_ft JVM_p f) &&
          L.leql_t sgn.(JVM_heapEffect) (JVM_ft JVM_p f) &&
          selift i None k2 && tsub_next i st
(* DEX
          &&
          tsub_next i (elift m i k2 st) &&
          for_all _
            (fun e => (selift i (Some e) k2) && (exception_test i e k2))
            (throwableAt m i)
*)
        | Return, st =>
          match sgn.(JVM_resType) with
            | None => true
            | _ => false
          end
        | Swap, k1::k2::st => tsub_next i (k2::k1::st)
        | Tableswitch d lo hi l, L.Simple k::st =>
          (selift i None k) &&
          (tsub_next i (lift_st k st)) &&
          (for_all _
            (fun o => tsub_st (lift_st k st) (S (JVM_OFFSET.jump i o)))
            (d::l))          
        | Vaload t, L.Simple k1::L.Array k2 ke::st =>
          (selift i None k2) &&
          (selift i None (L.join k1 k2)) &&
(* DEX
          (tsub_next i (L.join' (L.join k1 k2) ke::elift m i (L.join k1 k2) st)) &&
          (selift i (Some np) k2) && (exception_test' i np k2) &&
          (selift i (Some iob) (k1 U k2)) && (exception_test' i iob (k1 U k2)) 
*)
          (tsub_next i (L.join' (L.join k1 k2) ke::st))
        | Vastore t, kv::L.Simple ki::L.Array ka ke::st =>
          (leql'_test kv ke) &&
          (L.leql_t ki ke) &&
          (L.leql_t ka ke) &&
          (selift i None ka) &&
          (selift i None (L.join ki ka)) &&
          (selift i None ke) &&
          (L.leql_t (JVM_heapEffect sgn) ke) &&
(* DEX          (tsub_next i (elift m i ke st)) && *)
          (tsub_next i st)
(* DEX
          (selift i (Some np) ka) && (exception_test' i np ka) &&
          (selift i (Some ase) (L.join kv (L.join ki ka))) && (exception_test' i ase (L.join kv (L.join ki ka))) && 
          (selift i (Some iob) (L.join ki ka)) && (exception_test' i iob (L.join ki ka)) 
*)
        | Vload t x, st =>
          tsub_next i (L.join' (se i) (sgn.(JVM_lvt) x)::st)
        | Vstore t x, k::st =>
          L.leql_t (se i) (sgn.(JVM_lvt) x) &&
          leql'_test k (sgn.(JVM_lvt) x) &&
          tsub_next i st
        | Vreturn x, k::st =>
          match sgn.(JVM_resType) with
            | None => false
            | Some kv => leql'_test k kv 
          end
        | _,_ => false      end.

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
       [ id1 : JVM_StaticHandler.handler ?s ?m ?i ?e = _,
         id2 : context[StaticHandler.handler ?s ?m ?i ?e] |- _ ] =>
       rewrite id1 in id2
     end.
*)
   Ltac flatten :=
     flatten_bool; try replace_for_all; flatten_bool;
(* DEX       replace_handler; *)
       replace_selift; clean_in_test; replace_leql.

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
                            | JVM_Make.AddInt => _
                            | JVM_Make.AndInt => _
                            | JVM_Make.DivInt => _
                            | JVM_Make.MulInt => _
                            | JVM_Make.OrInt => _
                            | JVM_Make.RemInt => _
                            | JVM_Make.ShlInt => _
                            | JVM_Make.ShrInt => _
                            | JVM_Make.SubInt => _
                            | JVM_Make.UshrInt => _
                            | JVM_Make.XorInt => _
                          end] |- _] => destruct x
       end.


   Lemma tcheck_correct1 : forall i ins,
     JVM_tcheck i ins = true ->
     forall tau, JVM_step (* DEX JVM_p subclass_test  *) m i ins tau None ->
       texec i ins tau (S i) None.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold JVM_tcheck (*, step.handler, exception_test, exception_test'*) in *;
     try (destruct (S i) as [ | [|]]; intros; try discriminate; flatten;
       constructor; auto).
(* DEX     
     destruct H2;subst;  split_match; intros; try discriminate.
     (* Ibinop *)
     split_match; intros; try discriminate; flatten.
     constructor; auto.
     split_match; intros; try discriminate; flatten.
     constructor; auto.
     (* Invokestatic *)
     flatten_bool.
     generalize (le_nat_test_true _ _ H0); clear H0; intros H0.
     destruct (length_le_app_form _ _ _ H0) as [st1 [st2 [T1 T2]]].
     rewrite T1.
     constructor; flatten; auto.
     apply tcompat_type_st_lvt_true.
     congruence.
     apply L.leql_trans with (2:=H11); apply L.join_right.
     (* Invokevirtual *)
     case_eq (pop_n  (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid))) (S i)).
     intros HH; rewrite HH in H; flatten_bool.
     discriminate.
     intros k1 st2 HH; rewrite HH in H.
     destruct k1 as [k1|]; try discriminate.
     flatten_bool.
     generalize (le_nat_test_true _ _ H0); clear H0; intros H0.
     assert (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)) <= length (S i))%nat.
     omega.
     destruct (length_le_app_form _ _ _ H) as [st1 [st3 [T1 T2]]].
     rewrite T1.
     rewrite T1 in HH; rewrite T2 in HH; rewrite pop_n_length_fst in HH.
     subst.
     flatten.
     rewrite T1 in *.
     constructor; flatten; auto.
     apply tcompat_type_st_lvt_true.
     rewrite <- T2; auto.
     (* Putfield *)
     destruct (S i) as [ | k1 l]; intros; try discriminate.
     destruct l as [ | k2 l]; intros; try discriminate.
     destruct k2 as [ k2 |]; intros; try discriminate.
     flatten.
     constructor; auto.
*)
     (* return*) 
     destruct (JVM_resType sgn); congruence.
     destruct (JVM_resType sgn); congruence.
     destruct (JVM_resType sgn); congruence.
(* DEX
     (* Vaload *)
     destruct (S i) as [ |k1 l]; intros; try discriminate.
     destruct k1 as [k1|]; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [k2|]; try discriminate.
     flatten.
     constructor; auto.
     auto.
replace_leql.
     auto.

     destruct (S i) as [ |k1 l]; intros; try discriminate.
     destruct k1 as [k1|]; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [k2|]; try discriminate.
     flatten.
     constructor; auto.
     rewrite (In_in_test_true _ _ H1) in *; flatten; auto.

     (* Vastore *)
     destruct (S i) as [ |kv l]; intros; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [ki|]; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [|ka ke]; try discriminate.
     flatten.
     constructor; auto.
     rewrite (In_in_test_true _ _ H1) in *; flatten; auto.
   
     destruct (S i) as [ |kv l]; intros; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [ki|]; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [|ka ke]; try discriminate.
     flatten.
     constructor; auto.
     rewrite (In_in_test_true _ _ H1) in *; flatten; auto.

     destruct (S i) as [ |kv l]; intros; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [ki|]; try discriminate.
     destruct l as [|k2 l]; try discriminate.
     destruct k2 as [|ka ke]; try discriminate.
     flatten.
     econstructor; eauto.
*)
     (* Vreturn *)
     destruct (S i) as [ |k l]; intros; try discriminate.
     generalize H; clear H; case_eq (JVM_resType sgn); intros; try discriminate.
     econstructor; eauto.
     generalize (leql'_test_prop k t0). (* Hendra *)
     rewrite H0; auto.
   Qed.

   Ltac replace_tsub_next :=
     try match goal with
       [ id1 : tsub_next _ ?st = true, id2 : next _ _ = _ |- _ ] =>
         unfold tsub_next in id1; rewrite id2 in id1
     end.

   Ltac search_tsub :=
     match goal with
       [ id1 : tsub_st ?st (S _) = true |- _ ] =>
         exists st; split; [clear id1 | exact id1]
         end.

   Ltac flatten2 := flatten; replace_tsub_next; search_tsub.

   Hint Constructors texec : texec.

   Lemma tcheck_correct2 : forall i ins,
     JVM_tcheck i ins = true ->
     forall tau j, JVM_step (* DEX p subclass_test *) m i ins tau (Some j) ->
       exists st,
       texec i ins tau (S i) (Some st)
       /\ tsub_st st (S j) = true.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold JVM_tcheck (* DEX, step.handler, exception_test, exception_test'*) in *;
     try (split_match; intuition; subst; try discriminate; flatten2; eauto with texec; fail).
(* DEX
     split_match; intuition; try discriminate; flatten2.
     apply arraylength_np_caught with (t := j). apply H0. apply H2.
     
     split_match; try (case op in H; inversion H; fail).
     destruct op; flatten2; apply ibinop; auto.
*) 
     (* invokestatic *)
     flatten2.
     elim length_le_app_form with (n:=(length (JVM_METHODSIGNATURE.parameters (snd mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     rewrite T2.
     rewrite pop_n_length_fst.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     apply tcompat_op_true; auto.
     generalize (le_nat_test_correct (length (JVM_METHODSIGNATURE.parameters (snd mid)))
       (length (S i))); rewrite H0; auto.
     (**)
(* DEX
     flatten2.
     elim length_le_app_form with (n:=(length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)))) (l:=(S i)).
     intros st1 [st2 [T1 T2]].
     rewrite T1.
     constructor; auto.
     rewrite <- T1; rewrite <- T2; apply tcompat_type_st_lvt_true; auto.
     generalize (le_nat_test_correct (length (METHODSIGNATURE.parameters (@snd ClassName METHODSIGNATURE.t mid)))
       (length (S i))).
     rewrite H0; auto.
*)
     (* invokevirtual *)
     generalize H; clear H.
     case_eq (pop_n  (length (JVM_METHODSIGNATURE.parameters (@snd JVM_ClassName JVM_METHODSIGNATURE.t mid))) (S i)); intros.
     discriminate. 
     destruct t0 as [k1|]; try discriminate.
     (*destruct t as [k1|]; try discriminate.*)
     flatten2.
     elim length_le_app_form with (n:=(length (JVM_METHODSIGNATURE.parameters (snd mid)))) (l:=(S i)).
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
(* DEX invokevirtual exception
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
*)
   Qed.
 End JVM_S.
  End JVM_typing_rules.


