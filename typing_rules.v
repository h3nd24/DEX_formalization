(** typing_rules.v: Typing rules, plus an executable type checker *)
Require Export BigStepAnnot.
Require Export Bool.
Require Export step.
Import StaticHandler.StaticHandler BigStep.BigStep Dom.Prog.

Import Level.L.
Import Dom.

Open Scope type_scope.

  Section typing_rules.   (** Typing rules **)
    Variable p : ExtendedProgram.
    Variable subclass_test : ClassName -> ClassName -> bool.
    Variable subclass_test_correct :
      forall c1 c2,
        if subclass_test c1 c2 then subclass_name p.(prog) c1 c2
          else ~ subclass_name p.(prog) c1 c2.
    Variable m : Method.
    Definition method_signature := METHOD.signature m.
    Variable sgn : sign.
    Variable region : PC -> tag -> PC -> Prop.
    Variable se : PC -> L.t.
    Variable selift : PC -> tag -> L.t -> bool.

    (* Notation handler := (handler subclass_test m). *)

    Infix "<=" := L.leql (at level 70).
    Infix "<='" := L.leql' (at level 70).
    Infix "U'" := L.join' (at level 60, right associativity).
    Infix "U" := L.join (at level 60, right associativity).

    Inductive texec : PC -> Instruction -> tag -> TypeRegisters -> option TypeRegisters -> Prop :=
    | nop : forall i rt,
      texec i Nop None rt (Some rt)

    | move_constrained : forall i (rt:TypeRegisters) k_rs (k:ValKind) (r:Var) (rs:Var),
      In r (locR p method_signature) ->
      Some k_rs = BinNatMap.get _ rt rs ->
      se i <= sgn.(lvt) r ->
      k_rs <= sgn.(lvt) r ->
      texec i (Move k r rs) None rt 
       (Some (BinNatMap.update _ rt r ((se i) U' k_rs)))

    | move_unconstrained : forall i (rt:TypeRegisters) k_rs (k:ValKind) (r:Var) (rs:Var),
      ~In r (locR p method_signature) ->
      Some k_rs = BinNatMap.get _ rt rs ->
      texec i (Move k r rs) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_rs)))

    | moveResult_constrained : forall i (rt:TypeRegisters) k_res (k:ValKind) (r:Var),
      In r (locR p method_signature) ->
      Some k_res = BinNatMap.get _ rt LocalVar.ret ->
      se i <= sgn.(lvt) r ->
      k_res <= sgn.(lvt) r ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))

    | moveResult_unconstrained : forall i (rt:TypeRegisters) k_res (k:ValKind) (r:Var),
      ~In r (locR p method_signature) ->
      Some k_res = BinNatMap.get _ rt LocalVar.ret ->
      texec i (MoveResult k r) None rt
        (Some (BinNatMap.update _ rt r ((se i) U' k_res)))

    | return_ : forall i (rt:TypeRegisters),
      sgn.(resType) = None ->
      texec i (Return) None rt None

    | vReturn : forall i (rt:TypeRegisters) k_r kv (k:ValKind) (r:Var),
      Some k_r = BinNatMap.get _ rt r ->
      sgn.(resType) = Some kv ->
      ((se i) U' k_r) <=' kv ->
      texec i (VReturn k r) None rt None

    | const : forall i (rt:TypeRegisters) (k:ValKind) (r:Var) (v:Z),
      texec i (Const k r v) None rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))
    
    | instanceOf : forall i (rt:TypeRegisters) k (r:Var) (ro:Var) (t:refType),
      Some k = BinNatMap.get _ rt ro ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (InstanceOf r ro t) None rt 
        (Some (BinNatMap.update _ rt r (L.Simple ((se i) U k))))
    
    | arrayLength : forall i k ke (rt:TypeRegisters) (r:Var) (rs:Var),
      Some (L.Array k ke) = BinNatMap.get _ rt rs ->
      texec i (ArrayLength r rs) None rt
        (Some (BinNatMap.update _ rt r (L.Simple k)))
    
    | new : forall i (rt:TypeRegisters) (r:Var) (t:refType),
      texec i (New r t) None rt (Some (BinNatMap.update _ rt r (L.Simple (se i))))

    | newArray : forall i (rt:TypeRegisters) k (r:Var) (rl:Var) (t:type),
      Some k = BinNatMap.get _ rt rl ->
      texec i (NewArray r rl t) None rt
        (Some (BinNatMap.update _ rt r (L.Array k (newArT p (m,i)))))

    | goto : forall i (rt:TypeRegisters) (o:OFFSET.t),
      texec i (Goto o) None rt (Some rt)

    | packedSwitch : forall i k (rt:TypeRegisters) (r:Var) (firstKey:Z) (size:Z) (l:list OFFSET.t),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (PackedSwitch r firstKey size l) None rt (Some (lift k rt))

    | sparseSwitch : forall i k (rt:TypeRegisters) (r:Var) (size:Z) (l:list (Z * OFFSET.t)),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (SparseSwitch r size l) None rt (Some (lift k rt))
    
    | ifcmp : forall i k (rt:TypeRegisters) (cmp:CompInt) (ra:Var) (rb:Var) (o:OFFSET.t),
      Some k = BinNatMap.get _ rt ra ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (Ifcmp cmp ra rb o) None rt (Some (lift k rt))
     
    | ifz : forall i k (rt:TypeRegisters) (cmp:CompInt) (r:Var) (o:OFFSET.t),
      Some k = BinNatMap.get _ rt r ->
      (forall j, region i None j -> k <= se j) -> 
      texec i (Ifz cmp r o) None rt (Some (lift k rt))

    | aget : forall i ka kc ki (rt:TypeRegisters) 
       (k:ArrayKind) (r:Var) (ra:Var) (ri:Var),
      Some (L.Array ka kc) = BinNatMap.get _ rt ra ->
      Some ki = BinNatMap.get _ rt ri ->
      texec i (Aget k r ra ri) None rt 
        (Some (BinNatMap.update _ rt r ((ka U ki) U' kc)))

    | aput : forall i ks ka kc ki (rt:TypeRegisters)
       (k:ArrayKind) (rs:Var) (ra:Var) (ri:Var),
      Some ks = BinNatMap.get _ rt rs ->
      Some (L.Array ka kc) = BinNatMap.get _ rt ra ->
      Some ki = BinNatMap.get _ rt ri ->
      ((ka U ki) U' ks) <=' kc ->
      texec i (Aput k rs ra ri) None rt (Some rt)

    | iget : forall i ko (rt:TypeRegisters) (k:ValKind) (r:Var) (ro:Var) (f:FieldSignature),
      Some ko = BinNatMap.get _ rt ro ->
      texec i (Iget k r ro f) None rt 
        (Some (BinNatMap.update _ rt ro ((ko U (se i)) U' (ft p f))))

    | iput : forall i ks ko (rt:TypeRegisters) (k:ValKind) (rs:Var) (ro:Var) (f:FieldSignature),
      Some ks = BinNatMap.get _ rt rs ->
      Some ko = BinNatMap.get _ rt ro ->
      ((se i) U ko) U' ks <=' (ft p f) ->
      texec i (Iput k rs ro f) None rt (Some rt)

(*    | Sget (k:ValKind) (rt:Var) (f:FieldSignature)
    | Sput (k:ValKind) (rs:Var) (f:FieldSignature) *)

    | invokevirtual : forall i ko (rt:TypeRegisters) (m:MethodSignature) (n:Z) (par:list Var),
      length par = length (METHODSIGNATURE.parameters (snd m)) ->
      compat_type_rt_lvt (virtual_signature p (snd m) ko) (rt) (par) (n) ->
      ko <= (virtual_signature p (snd m) ko).(heapEffect) -> 
      sgn.(heapEffect) <= (virtual_signature p (snd m) ko).(heapEffect) ->
      (* DEX *) (se i) <= (virtual_signature p (snd m) ko).(heapEffect) ->
      compat_op (METHODSIGNATURE.result (snd m)) (virtual_signature p (snd m) ko).(resType) -> 
      texec i (Invokevirtual m n p) None rt
      (Some (BinNatMap.update _ rt (BinNatMap.get _ rt LocalVar.ret)
            (join_op (ko U (se i)) (virtual_signature p (snd m) ko).(resType)) ))
(*
    | Invokesuper (m:MethodSignature) (n:Z) (p:list Var)
    | Invokedirect (m:MethodSignature) (n:Z) (p:list Var)
*)
    | invokestatic : forall i (rt:TypeRegisters) (m:MethodSignature) (n:Z) (p:list Var),
      length p = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (static_signature p (snd mid)) (st1++st2) (length st1) ->
      se i <= (static_signature p (snd mid)).(heapEffect) -> 
      (forall j, region i None j -> 
        join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid)) <= se j) ->
      compat_op (METHODSIGNATURE.result (snd mid)) (static_signature p (snd mid)).(resType) ->
      sgn.(heapEffect) <= (static_signature p (snd mid)).(heapEffect) -> 
      texec i (Invokestatic mid) None 
      (st1++st2)
      (Some (lift (join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid))) 
        (cons_option (join_op (se i) (static_signature p (snd mid)).(resType)) st2)))
(*
    | Invokeinterface (m:MethodSignature) (n:Z) (p:list Var)
*)
    | ineg : forall i ks (rt:TypeRegisters) (r:Var) (rs:Var),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (Ineg r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | inot : forall i ks (rt:TypeRegisters) (r:Var) (rs:Var),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (Inot r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | i2b : forall i ks (rt:TypeRegisters) (r:Var) (rs:Var),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (I2b r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | i2s : forall i ks (rt:TypeRegisters) (r:Var) (rs:Var),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (I2s r rs) None rt (Some (BinNatMap.update _ rt r (L.Simple ((se i) U ks))))

    | ibinop : forall i ka kb (rt:TypeRegisters) (op:BinopInt) (r:Var) (ra:Var) (rb:Var),
      Some ka = BinNatMap.get _ rt ra ->
      Some kb = BinNatMap.get _ rt rb ->
      texec i (Ibinop op r ra rb) None rt 
       (Some (BinNatMap.update _ rt r (L.Simple ((ka U kb) U (se i)))))
    
    | ibinopConst : forall i ks (rt:TypeRegisters) (op:BinopInt) (r:Var) (rs:Var) (v:Z),
      Some ks = BinNatMap.get _ rt rs ->
      texec i (IbinopConst op r rs v) None rt 
       (Some (BinNatMap.update _ rt r (L.Simple (ks U (se i)))))   
    .


    


   | aconst_null : forall i st,
      texec i Aconst_null None st (Some (L.Simple (se i)::st))
    | arraylength : forall i k ke st,
      (forall j, region i None j -> k <= se j) -> 
      texec i Arraylength None (L.Array k ke::st)  (Some (L.Simple k::(elift m i k st)))
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
      texec i (Getfield f) None (L.Simple k::st) (Some ((k U' (ft p f))::(elift m i k st)))
    | getfield_np_caught : forall i t f k st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      handler i np = Some t ->
      texec i (Getfield f) (Some np) (L.Simple k::st) (Some (L.Simple k::nil))
    | getfield_np_uncaught : forall i f k st,
      (forall j, region i (Some np) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Getfield f) (Some np) (L.Simple k::st) None
    | goto : forall i o st,
      texec i (Goto o) None st (Some st)
    | i2b : forall i k st,
      texec i I2b None (L.Simple k::st) (Some (L.Simple k::st))
    | i2s : forall i k st,
      texec i I2s None (L.Simple k::st) (Some (L.Simple k::st))
    | ibinop : forall i op k1 k2 st st',
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
      texec i (Ibinop op) None (L.Simple k1::L.Simple k2::st) (Some (L.Simple (L.join k1 k2)::st'))
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
    | if_acmp : forall i cmp o k1 k2 st,
      (forall j, region i None j -> L.join k1 k2 <= se j) -> 
      texec i (If_acmp cmp o) None (L.Simple k1::L.Simple k2::st) (Some (lift (L.join k1 k2) st))
    | if_icmp : forall i cmp o k1 k2 st,
      (forall j, region i None j -> L.join k1 k2 <= se j) -> 
      texec i (If_icmp cmp o) None (L.Simple k1::L.Simple k2::st) (Some (lift (L.join k1 k2) st))
    | ifeq : forall i cmp o k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (If0 cmp o) None (L.Simple k::st) (Some (lift k st))
    | ifnull : forall i cmp o (k:L.t') st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Ifnull cmp o) None (k::st) (Some (lift k st))
    | iinc : forall i x c st,
      se i <= sgn.(lvt) x -> 
      texec i (Iinc x c) None st (Some st)
    | ineg : forall i k st,
      texec i Ineg None (k::st) (Some (k::st))
    | instanceof : forall i t (k:L.t') st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Instanceof t) None (k::st) (Some (k::st))
    | invokestatic : forall i (mid:MethodSignature) st1 st2,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (static_signature p (snd mid)) (st1++st2) (length st1) ->
      se i <= (static_signature p (snd mid)).(heapEffect) -> 
      (forall j, region i None j -> 
        join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid)) <= se j) ->
      compat_op (METHODSIGNATURE.result (snd mid)) (static_signature p (snd mid)).(resType) ->
      sgn.(heapEffect) <= (static_signature p (snd mid)).(heapEffect) -> 
      texec i (Invokestatic mid) None 
      (st1++st2)
      (Some (lift (join_list (static_signature p (snd mid)).(resExceptionType) (throwableBy p (snd mid))) 
        (cons_option (join_op (se i) (static_signature p (snd mid)).(resType)) st2)))
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
    | invokevirtual : forall i (mid:MethodSignature) st1 k1 st2,
      length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
      compat_type_st_lvt (virtual_signature p (snd mid) k1) (st1++L.Simple k1::st2) (1+(length st1)) ->
      k1 <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      (forall j, region i None j -> 
        L.join (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid)))
        k1 <= se j) ->
      compat_op (METHODSIGNATURE.result (snd mid)) (virtual_signature p (snd mid) k1).(resType) ->
      sgn.(heapEffect) <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
      texec i (Invokevirtual mid) None 
      (st1++L.Simple k1::st2) 
      (Some (lift k1 (lift (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) 
        (cons_option (join_op k1 (virtual_signature p (snd mid) k1).(resType)) st2))))
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
    | lookupswitch : forall i d l k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Lookupswitch d l) None (L.Simple k::st) (Some (lift k st))
    | new : forall i c st,
      texec i (New c) None st (Some (L.Simple (se i)::st))
    | newarray : forall i t k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Newarray t) None (L.Simple k::st) (Some (L.Array k (newArT p (m,i))::elift m i k st))
    | newarray_nase_caught : forall i t te k st,
      (forall j, region i (Some nase) j -> k <= se j) -> 
      handler i nase = Some te ->
      texec i (Newarray t) (Some nase) (L.Simple k::st) (Some (L.Simple k::nil))
    | newarray_nase_uncaught : forall i t k st,
      (forall j, region i (Some nase) j -> k <= se j) -> 
      k <= sgn.(resExceptionType) nase ->
      handler i nase = None ->
      texec i (Newarray t) (Some nase) (L.Simple k::st) None
    | nop : forall i st,
      texec i Nop None st (Some st)
    | pop : forall i k st,
      texec i Pop None (k::st) (Some st)
    | pop2 : forall i k1 k2 st,
      texec i Pop2 None (k1::k2::st) (Some st)
    | putfield : forall i f k1 k2 st,
      k1 <=' ft p f -> 
      k2 <= ft p f -> 
      se i <= ft p f -> 
      sgn.(heapEffect) <= ft p f -> 
      (forall j, region i None j -> k2 <= se j) -> 
      texec i (Putfield f) None (k1::L.Simple k2::st) (Some (elift m i k2 st))
    | putfield_np_caught : forall i t f k1 k2 st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      handler i np = Some t ->
      texec i (Putfield f) (Some np) (k1::L.Simple k2::st) (Some (L.Simple k2::nil))
    | putfield_np_uncaught : forall i f k1 k2 st,
      (forall j, region i (Some np) j -> k2 <= se j) -> 
      k2 <= sgn.(resExceptionType) np ->
      handler i np = None ->
      texec i (Putfield f) (Some np) (k1::L.Simple k2::st) None
    | return_ : forall i st,
      sgn.(resType) = None ->
      texec i Return None st None
    | swap : forall i k1 k2 st,
      texec i Swap None (k1::k2::st) (Some (k2::k1::st))
    | tableswitch : forall i d lo hi l k st,
      (forall j, region i None j -> k <= se j) -> 
      texec i (Tableswitch d lo hi l) None (L.Simple k::st) (Some (lift k st))
    | vaload : forall i t k1 k2 ke st,
      (forall j, region i None j -> k2 <= se j) -> 
      (forall j, region i None j -> (L.join k1 k2) <= se j) -> 
      texec i (Vaload t)  None (L.Simple k1::L.Array k2 ke::st) (Some (L.join' (L.join k1 k2) ke::elift m i (L.join k1 k2) st))
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
    | vastore : forall i t kv ki ka ke st,
      kv <=' ke -> 
      ki <= ke -> 
      ka <= ke ->
      (forall j, region i None j -> ka <= se j) -> 
      (forall j, region i None j -> (L.join ki ka) <= (se j)) -> 
      (forall j, region i None j -> ke <= (se j)) -> 
      L.leql (heapEffect sgn) ke ->
      texec i (Vastore t) None (kv::L.Simple ki::L.Array ka ke::st) (Some (elift m i ke st))
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
    | vload : forall i t x st,
      texec i (Vload t x) None st (Some (L.join' (se i) (sgn.(lvt) x)::st))
    | vstore : forall i t x k st,
      se i <= sgn.(lvt) x -> 
      L.leql' k (sgn.(lvt) x) ->      
      texec i (Vstore t x) None (k::st) (Some st)
    | vreturn : forall i x k kv st,
      sgn.(resType) = Some kv ->
      L.leql' k kv ->      
      texec i (Vreturn x) None (k::st) None.

    Section S.
      Variable S : PC -> TypeStack.

    Definition tsub_next (i:PC) st : bool :=
      match next m i with
        | Some j => tsub st (S j)
        | None => false
      end.

    Definition exception_test (i:PC) (e:ClassName) (k:L.t) : bool :=
      match handler i e with
        | Some t => tsub (L.Simple k::nil) (S t)
        | None => L.leql_t k (sgn.(resExceptionType) e)
      end.

    Fixpoint in_test (e:ClassName) (l:list ClassName) : bool :=
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

    Definition exception_test' (i:PC) (e:ClassName) (k:L.t) : bool :=
      if in_test e (throwableAt m i) then
        match handler i e with
          | Some t => tsub (L.Simple k::nil) (S t)
          | None => L.leql_t k (sgn.(resExceptionType) e)
        end
        else true.

    Fixpoint tcompat_type_st_lvt_aux (s:sign) (st:TypeStack) (n0 n:nat) {struct n} : bool :=
      match n with (* could be optimised *)
        | O => true
        | Datatypes.S q => let x := N_toVar q in
            match nth_error st (n0-n)%nat with
              | None => false
              | Some k => leql'_test k (lvt s x)
            end && tcompat_type_st_lvt_aux s st n0 q
      end.

    Lemma tcompat_type_st_lvt_aux_true : forall s st n0 n,
      tcompat_type_st_lvt_aux s st n0 n = true ->
      forall x, ((Var_toN x)<n)%nat -> exists k,
        nth_error st (n0-(Var_toN x)-1)%nat = Some k /\
        L.leql' k (lvt s x).
    Proof.
      induction n; simpl.
      intros.
      apply False_ind; omega.
      caseeq (nth_error st (n0 - Datatypes.S n)); intros.
      elim andb_prop with (1:=H0); clear H0; intros.
      elim (eq_excluded_middle _ (Var_toN x) n); intros; subst.
      replace (n0 - Var_toN x - 1)%nat with (n0 - Datatypes.S (Var_toN x))%nat.
      exists t0; split; auto. (* Hendra *)
      generalize (leql'_test_prop t0 (lvt s (N_toVar (Var_toN x)))); rewrite H0. (* Hendra *)
      rewrite Var_toN_bij1; auto.
      omega.
      apply IHn; auto.
      omega.
      simpl in H0; discriminate.
    Qed.

    Definition tcompat_type_st_lvt (s:sign) (st:TypeStack) (n:nat) : bool :=
      tcompat_type_st_lvt_aux s st n n.

    Lemma tcompat_type_st_lvt_true : forall s st n,
      tcompat_type_st_lvt s st n = true ->
      compat_type_st_lvt s st n.
    Proof.
      unfold tcompat_type_st_lvt, compat_type_st_lvt; intros.
      apply (tcompat_type_st_lvt_aux_true _ _ _ _ H); auto.
    Qed.

    Definition tcompat_op (ot:option type) (ok:option L.t') : bool :=
      match ot,ok with
        | None,None => true
        | Some _,Some _ => true
        | _,_ => false
      end.

    Lemma tcompat_op_true : forall (ot:option type) (ok:option L.t'),
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

    Definition compat_type_st_lvt (s:sign) (st:TypeStack) (n:nat) : Prop :=
      forall x, ((Var_toN x)<n)%nat -> exists k,
        nth_error st (n-(Var_toN x)-1)%nat = Some k /\
        L.leql' k (lvt s x).

   Definition tcheck (i:PC) (ins:Instruction) : bool :=
      match ins,S i with
        | Aconst_null,   st1 => 
          tsub_next i (L.Simple (se i)::st1)
        | Arraylength,   (L.Array k ke::st) =>
          (selift i None k) &&
          (tsub_next i (L.Simple k::(elift m i k st))) &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
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
          (tsub_next i ((k U' (ft p f))::(elift m i k st))) &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
        | Goto o,          st =>
          tsub st (S (OFFSET.jump i o)) 
        | I2b,             L.Simple k::st =>
          tsub_next i (L.Simple k::st) 
        | I2s,             L.Simple k::st =>
          tsub_next i (L.Simple k::st) 
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
        | Ibinop _,       L.Simple k1::L.Simple k2::st =>
          tsub_next i (L.Simple (L.join k1 k2)::st)
        | If_acmp _ o,    L.Simple k1::L.Simple k2::st =>
          (selift i None (L.join k1 k2)) &&
          (tsub_next i (lift (L.join k1 k2) st)) &&
          (tsub (lift (L.join k1 k2) st) (S (OFFSET.jump i o)))
        | If_icmp _ o,    L.Simple k1::L.Simple k2::st =>
          (selift i None (L.join k1 k2)) &&
          (tsub_next i (lift (L.join k1 k2) st)) &&
          (tsub (lift (L.join k1 k2) st) (S (OFFSET.jump i o)))
        | If0 _ o,        L.Simple k::st =>
          (selift i None k) &&
          (tsub_next i (lift k st)) &&
          (tsub (lift k st) (S (OFFSET.jump i o)))
        | Ifnull _ o,        k::st =>
          (selift i None k) &&
          (tsub_next i (lift k st)) &&
          (tsub (lift k st) (S (OFFSET.jump i o)))
        | Iinc x c,         st =>
          (L.leql_t (se i) (sgn.(lvt) x)) &&
          (tsub_next i st)
        | Ineg,             k::st =>
          tsub_next i (k::st)
        | Instanceof _,     k::st =>
          (selift i None k) &&
          (tsub_next i (k::st))
        | Invokestatic mid, st =>
          let n := length (METHODSIGNATURE.parameters (snd mid)) in
          let sgn' := (static_signature p (snd mid)) in 
          let ke' := (join_list sgn'.(resExceptionType) (throwableBy p (snd mid))) in
            le_nat_test n (length st) &&
            (tcompat_type_st_lvt (static_signature p (snd mid)) st n) &&
            (L.leql_t (se i) sgn'.(heapEffect)) &&
            (selift i None ke') &&
            for_all _
              (fun e => (selift i (Some e) (sgn'.(resExceptionType) e) &&
                        (exception_test i e (L.join (se i) (sgn'.(resExceptionType) e)))) &&
                        (L.leql_t (se i) (sgn.(resExceptionType) e))) 
              (throwableBy p (snd mid)) &&
            (tcompat_op (METHODSIGNATURE.result (snd mid)) sgn'.(resType)) &&
            (L.leql_t sgn.(heapEffect) sgn'.(heapEffect)) && 
            tsub_next i (lift ke' (cons_option (join_op (se i) sgn'.(resType)) (pop_n n st)))
        | Invokevirtual mid, st =>
          let n := length (METHODSIGNATURE.parameters (snd mid)) in
            match pop_n n st with
              | (L.Simple k1)::st2 =>
                le_nat_test (Datatypes.S n) (length st) &&
                (tcompat_type_st_lvt (virtual_signature p (snd mid) k1) st (Datatypes.S n)) &&
                (L.leql_t k1 (virtual_signature p (snd mid) k1).(heapEffect)) &&
                (selift i None (L.join (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) k1)) &&
                (for_all _
                  (fun cn => 
                    (selift i (Some cn) (L.join ((virtual_signature p (snd mid) k1).(resExceptionType) cn) k1)) &&
                    (exception_test i cn (L.Simple (L.join k1 ((virtual_signature p (snd mid) k1).(resExceptionType) cn)))) &&
                    (L.leql_t k1 (sgn.(resExceptionType) cn)) &&
                    (L.leql_t ((virtual_signature p (snd mid) k1).(resExceptionType) cn) (sgn.(resExceptionType) cn)))
                  (throwableAt m i ++ throwableBy p (snd mid))) &&
                (tcompat_op (METHODSIGNATURE.result (snd mid)) (virtual_signature p (snd mid) k1).(resType)) &&
                (L.leql_t sgn.(heapEffect) (virtual_signature p (snd mid) k1).(heapEffect)) &&
                tsub_next i (lift k1 (lift (join_list (virtual_signature p (snd mid) k1).(resExceptionType) (throwableBy p (snd mid))) 
                  (cons_option (join_op k1 (virtual_signature p (snd mid) k1).(resType)) st2)))
              | _ => false
            end
        | Lookupswitch d l, L.Simple k::st =>
          (selift i None k) &&
          (for_all _
            (fun o => tsub (lift k st) (S (OFFSET.jump i o)))
            (d::@map _ _ (@snd _ _) l)) &&
          tsub_next i (lift k st)
        | New c, st =>
          tsub_next i (L.Simple (se i)::st)
        | Newarray t, (L.Simple k::st) =>
          (selift i None k) &&
          tsub_next i (L.Array k (newArT p (m,i))::elift m i k st) &&
          for_all _
            (fun e => (selift i (Some e) k) && (exception_test i e k))
            (throwableAt m i)
        | Nop, st => tsub_next i st
        | Pop, k::st => tsub_next i  st
        | Pop2, k1::k2::st => tsub_next i st
        | Putfield f, (k1::L.Simple k2::st) =>
          leql'_test k1 (ft p f) &&
          L.leql_t k2 (ft p f) &&
          L.leql_t (se i) (ft p f) &&
          L.leql_t sgn.(heapEffect) (ft p f) &&
          selift i None k2 &&
          tsub_next i (elift m i k2 st) &&
          for_all _
            (fun e => (selift i (Some e) k2) && (exception_test i e k2))
            (throwableAt m i)
        | Return, st =>
          match sgn.(resType) with
            | None => true
            | _ => false
          end
        | Swap, k1::k2::st => tsub_next i (k2::k1::st)
        | Tableswitch d lo hi l, L.Simple k::st =>
          (selift i None k) &&
          (tsub_next i (lift k st)) &&
          (for_all _
            (fun o => tsub (lift k st) (S (OFFSET.jump i o)))
            (d::l))          
        | Vaload t, L.Simple k1::L.Array k2 ke::st =>
          (selift i None k2) &&
          (selift i None (L.join k1 k2)) &&
          (tsub_next i (L.join' (L.join k1 k2) ke::elift m i (L.join k1 k2) st)) &&
          (selift i (Some np) k2) && (exception_test' i np k2) &&
          (selift i (Some iob) (k1 U k2)) && (exception_test' i iob (k1 U k2)) 
        | Vastore t, kv::L.Simple ki::L.Array ka ke::st =>
          (leql'_test kv ke) &&
          (L.leql_t ki ke) &&
          (L.leql_t ka ke) &&
          (selift i None ka) &&
          (selift i None (L.join ki ka)) &&
          (selift i None ke) &&
          (L.leql_t (heapEffect sgn) ke) &&
          (tsub_next i (elift m i ke st)) &&
          (selift i (Some np) ka) && (exception_test' i np ka) &&
          (selift i (Some ase) (L.join kv (L.join ki ka))) && (exception_test' i ase (L.join kv (L.join ki ka))) && 
          (selift i (Some iob) (L.join ki ka)) && (exception_test' i iob (L.join ki ka)) 
        | Vload t x, st =>
          tsub_next i (L.join' (se i) (sgn.(lvt) x)::st)
        | Vstore t x, k::st =>
          L.leql_t (se i) (sgn.(lvt) x) &&
          leql'_test k (sgn.(lvt) x) &&
          tsub_next i st
        | Vreturn x, k::st =>
          match sgn.(resType) with
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

   Ltac replace_handler :=
     repeat match goal with
       [ id1 : StaticHandler.handler ?s ?m ?i ?e = _,
         id2 : context[StaticHandler.handler ?s ?m ?i ?e] |- _ ] =>
       rewrite id1 in id2
     end.

   Ltac flatten :=
     flatten_bool; try replace_for_all; flatten_bool;
       replace_handler; replace_selift; clean_in_test; replace_leql.

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
                            | Make.AddInt => _
                            | Make.AndInt => _
                            | Make.DivInt => _
                            | Make.MulInt => _
                            | Make.OrInt => _
                            | Make.RemInt => _
                            | Make.ShlInt => _
                            | Make.ShrInt => _
                            | Make.SubInt => _
                            | Make.UshrInt => _
                            | Make.XorInt => _
                          end] |- _] => destruct x
       end.


   Lemma tcheck_correct1 : forall i ins,
     tcheck i ins = true ->
     forall tau, step p subclass_test m i ins tau None ->
       texec i ins tau (S i) None.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold tcheck, step.handler, exception_test, exception_test' in *;
     try (destruct (S i) as [ | [|]]; intros; try discriminate; flatten;
       constructor; auto).
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
     (* return*) 
     destruct (resType sgn); congruence.
     destruct (resType sgn); congruence.
     destruct (resType sgn); congruence.
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
     (* Vreturn *)
     destruct (S i) as [ |k l]; intros; try discriminate.
     generalize H; clear H; case_eq (resType sgn); intros; try discriminate.
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
       [ id1 : tsub ?st (S _) = true |- _ ] =>
         exists st; split; [clear id1 | exact id1]
         end.

   Ltac flatten2 := flatten; replace_tsub_next; search_tsub.

   Hint Constructors texec : texec.

   Lemma tcheck_correct2 : forall i ins,
     tcheck i ins = true ->
     forall tau j, step p subclass_test m i ins tau (Some j) ->
       exists st,
       texec i ins tau (S i) (Some st)
       /\ tsub st (S j) = true.
   Proof.
     intros.
     inversion_clear H0 in H;
       unfold tcheck, step.handler, exception_test, exception_test' in *;
     try (split_match; intuition; subst; try discriminate; flatten2; eauto with texec; fail).
     split_match; intuition; try discriminate; flatten2.
     apply arraylength_np_caught with (t := j). apply H0. apply H2.
     
     split_match; try (case op in H; inversion H; fail).
     destruct op; flatten2; apply ibinop; auto.
 
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
 End S.
  End typing_rules.


