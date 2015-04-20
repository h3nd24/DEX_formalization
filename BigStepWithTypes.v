(** BigStepWithTypes.v: Intermediate bigstep semantics where we mixed semantic and typing rules (used only as an intermediate step in the proof) *)
Require Export ZArith.
Require Export IndistRelations.

Module BigStepWithTypes.

  Open Scope type_scope.

  Import BigStepAnnot.BigStepAnnot BigStep.BigStep Dom Prog .
  Import Level.L.

  Section p.
    Variable kobs: L.t.
    Variable p : ExtendedProgram.
    Notation ft := (ft p).

    Section annot.
      Variable se : PC -> L.t.
      Variable region : PC -> option ClassName -> PC -> Prop.
      
      Definition newb (k:L.t) (b:FFun.t Location) (loc:Location) : FFun.t Location :=
        if L.leql_dec k kobs then (FFun.extends b loc) 
          else b.

      Infix "<=" := L.leql (at level 70).
      Infix "<='" := L.leql' (at level 70).
      Infix "U'" := L.join' (at level 60, right associativity).
      Infix "U" := L.join (at level 60, right associativity).


      Inductive NormalStep_aconst_null (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | aconst_null : forall h pc pc' s l st b,

        next m pc = Some pc' ->

        NormalStep_aconst_null m sgn 
        (pc,(h,s,l)) st b (pc',(h,(Null::s),l)) (L.Simple (se pc)::st) b.

      Inductive NormalStep_arraylength (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | arraylength : forall h pc pc' s l loc length tp x k ke st b, 

        next m pc = Some pc' ->
        Heap.typeof  h loc = Some (Heap.LocationArray length tp x) ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_arraylength m sgn 
        (pc,(h,(Ref loc::s),l)) (L.Array k ke::st) b (pc',(h,(Num (I length)::s),l)) (L.Simple k::(elift m pc k st)) b.

      Inductive NormalStep_checkcast1 (t:refType) (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | checkcast1 : forall h pc pc' s l val b (k:L.t') st,

        next m pc = Some pc' ->
        assign_compatible p.(prog) h val (ReferenceType t) ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_checkcast1 t m sgn 
        (pc,(h,(val::s),l)) (k::st) b (pc',(h,(val::s),l)) (k::elift m pc k st) b.

      Inductive NormalStep_const (t:primitiveType) (z:Z) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | const : forall h pc pc' s l st b,

        next m pc = Some pc' ->
        (   (t=BYTE /\ -2^7 <= z < 2^7)
          \/ (t=SHORT /\ -2^15 <= z < 2^15)
          \/ (t=INT /\ -2^31 <= z < 2^31)   )%Z ->

        NormalStep_const t z m sgn 
        (pc,(h,s,l)) st b (pc',(h,(Num (I (Int.const z))::s),l)) (L.Simple (se pc)::st) b.

      Inductive NormalStep_dup (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup : forall h pc pc' s l v k st b,

        next m pc = Some pc' ->

        NormalStep_dup m sgn 
        (pc,(h,(v::s),l)) (k::st) b (pc',(h,(v::v::s),l)) (k::k::st) b.

      Inductive NormalStep_dup_x1 (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup_x1 : forall h pc pc' s l v1 v2 k1 k2 st b,

        next m pc = Some pc' ->

        NormalStep_dup_x1 m sgn 
        (pc,(h,(v1::v2::s),l)) (k1::k2::st) b (pc',(h,(v1::v2::v1::s),l)) (k1::k2::k1::st) b.

      Inductive NormalStep_dup_x2 (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup_x2 : forall h pc pc' s l v1 v2 v3 k1 k2 k3 st b,

        next m pc = Some pc' ->

        NormalStep_dup_x2 m sgn 
        (pc,(h,(v1::v2::v3::s),l)) (k1::k2::k3::st) b (pc',(h,(v1::v2::v3::v1::s),l)) (k1::k2::k3::k1::st) b.

      Inductive NormalStep_dup2 (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup2 : forall h pc pc' s l v1 v2 k1 k2 b st,

        next m pc = Some pc' ->

        NormalStep_dup2 m sgn 
        (pc,(h,(v1::v2::s),l)) (k1::k2::st) b (pc',(h,(v1::v2::v1::v2::s),l)) (k1::k2::k1::k2::st) b.

      Inductive NormalStep_dup2_x1 (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup2_x1 : forall h pc pc' s l v1 v2 v3 k1 k2 k3 st b,

        next m pc = Some pc' ->

        NormalStep_dup2_x1 m sgn 
        (pc,(h,(v1::v2::v3::s),l)) (k1::k2::k3::st) b (pc',(h,(v1::v2::v3::v1::v2::s),l)) (k1::k2::k3::k1::k2::st) b.

      Inductive NormalStep_dup2_x2 (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | dup2_x2 : forall h pc pc' s l v1 v2 v3 v4 k1 k2 k3 k4 st b,

        next m pc = Some pc' ->

        NormalStep_dup2_x2 m sgn 
        (pc,(h,(v1::v2::v3::v4::s),l)) (k1::k2::k3::k4::st) b (pc',(h,(v1::v2::v3::v4::v1::v2::s),l)) (k1::k2::k3::k4::k1::k2::st) b.

      Inductive NormalStep_getfield (f:FieldSignature) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | getfield : forall h pc pc' s l loc v cn k st b,

        next m pc = Some pc' ->
        Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
        defined_field p.(prog) cn f ->
        Heap.get h (Heap.DynamicField loc f) = Some v ->    
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_getfield f m sgn 
        (pc,(h,(Ref loc::s),l)) (L.Simple k::st) b (pc',(h,(v::s),l)) ((k U' (ft f))::(elift m pc k st)) b.


      Inductive NormalStep_goto (o:OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | goto : forall h pc s l st b,

        NormalStep_goto o m sgn 
        (pc,(h,s,l)) st b (OFFSET.jump pc o,(h,s,l)) st b.

      Inductive NormalStep_i2b (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | i2b : forall h pc pc' s l i k st b,

        next m pc = Some pc' ->

        NormalStep_i2b m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b (pc',(h,(Num (I (b2i (i2b i)))::s),l)) (L.Simple k::st) b.

      Inductive NormalStep_i2s (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | i2s : forall h pc pc' s l i k st b,

        next m pc = Some pc' ->

        NormalStep_i2s m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b  (pc',(h,(Num (I (s2i (i2s i)))::s),l)) (L.Simple k::st) b.

      Inductive NormalStep_ibinop (m:Method) (sgn:sign)  : BinopInt ->
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | ibinop : forall h pc pc' s l i1 i2 k1 k2 st b st' op,

        next m pc = Some pc' ->
        (op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0%Z) -> 
        st' = (match op with 
                 | DivInt => elift m pc k1 st
                 | RemInt => elift m pc k1 st
                 | _ => st
               end) ->
        (match op with 
           | DivInt => forall j, region pc None j -> k1 <= (se j)
           | RemInt => forall j, region pc None j -> k1 <= (se j)
           | _ => True
         end) ->

        NormalStep_ibinop m sgn op
        (pc,(h,(Num (I i2)::Num (I i1)::s),l)) (L.Simple k1::L.Simple k2::st) b
        (pc',(h,(Num (I (SemBinopInt op i1 i2))::s),l)) (L.Simple (L.join k1 k2)::st') b.

      Inductive NormalStep_if_acmp (cmp:CompRef) (o:OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | if_acmp_step_jump : forall h pc s l val2 val1  k1 k2 st b,

        SemCompRef cmp val1 val2 ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_if_acmp cmp o m sgn 
        (pc,(h,(val2:: val1::s),l)) (L.Simple k1::L.Simple k2::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift (L.join k1 k2) st) b
      | if_acmp_step_continue : forall h pc pc' s l val2 val1  k1 k2 st b,

        next m pc = Some pc' ->
        ~ SemCompRef cmp val1 val2 ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_if_acmp cmp o m sgn  
        (pc,(h,(val2:: val1::s),l)) (L.Simple k1::L.Simple k2::st) b
        (pc',(h,s,l)) (lift (L.join k1 k2) st) b.

      Inductive NormalStep_if_icmp (cmp:CompInt) (o:OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | if_icmp : forall h pc s l i2 i1 k1 k2 st b,
        instructionAt m pc = Some (If_icmp cmp o) ->
        SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_if_icmp cmp o m sgn 
        (pc,(h,(Num(I i2)::Num(I i1)::s),l)) (L.Simple k1::L.Simple k2::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift (L.join k1 k2) st) b
      | if_icmpeq : forall h pc pc' s l i2 i1 k1 k2 st b,
        next m pc = Some pc' ->
        ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_if_icmp cmp o m sgn 
        (pc,(h,(Num(I i2)::Num(I i1)::s),l)) (L.Simple k1::L.Simple k2::st) b
        (pc',(h,s,l)) (lift (L.join k1 k2) st) b.

      Inductive NormalStep_if0 (cmp:CompInt) (o:OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | ifeq_jump : forall h pc s l i k st b,
        SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_if0 cmp o m sgn 
        (pc,(h,(Num(I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift k st) b
      | ifeq_continue : forall h pc pc' s l i k st b,

        next m pc = Some pc' ->
        ~ SemCompInt cmp (Int.toZ i) 0 ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_if0 cmp o m sgn 
        (pc,(h,(Num(I i)::s),l)) (L.Simple k::st) b
        (pc',(h,s,l)) (lift k st) b.

      Inductive NormalStep_ifnull (cmp:CompRef) (o:OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | ifnull_step_jump : forall h pc s l loc  (k:L.t') st b,
        instructionAt m pc = Some (Ifnull cmp o) ->
        SemCompRef cmp loc Null ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_ifnull cmp o m sgn 
        (pc,(h,(loc::s),l)) (k::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift k st) b
      | ifnull_step_continue : forall h pc pc' s l loc (k:L.t') st b,

        next m pc = Some pc' ->
        ~ SemCompRef cmp loc Null ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_ifnull cmp o m sgn 
        (pc,(h,(loc::s),l)) (k::st) b
        (pc',(h,s,l)) (lift k st) b.

      Inductive NormalStep_iinc (x:Var) (z:Z) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | iinc : forall h pc s l pc' i st b,

        next m pc = Some pc' ->
        (-2^7 <= z < 2^7)%Z ->
        METHOD.valid_var m x ->
        LocalVar.get l x = Some (Num (I i)) ->
        (se  pc) <= (sgn.(lvt) x) -> 

        NormalStep_iinc x z m sgn 
        (pc,(h,s,l)) st b
        (pc',(h,s,(LocalVar.update l x (Num (I (Int.add i (Int.const z))))))) st b.

      Inductive NormalStep_ineg (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | ineg : forall h pc s l pc' i k st b,

        next m pc = Some pc' ->

        NormalStep_ineg m sgn 
        (pc,(h,(Num (I i)::s),l)) (k::st) b
        (pc',(h,(Num (I (Int.neg i))::s),l)) (k::st) b.

      Inductive NormalStep_instanceof (t:refType) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | instanceof1 : forall h pc pc' s l loc (k:L.t') st b,

        next m pc = Some pc' ->
        assign_compatible p.(prog) h (Ref loc) (ReferenceType t) ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_instanceof t m sgn 
        (pc,(h,(Ref loc::s),l)) (k::st) b
        (pc',(h,(Num (I (Int.const 1))::s),l)) (k::st) b
      | instanceof2 : forall h pc pc' s l v (k:L.t') st b,

        next m pc = Some pc' ->
        isReference v ->
        (~ assign_compatible p.(prog) h v (ReferenceType t) \/ v=Null) ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_instanceof t m sgn
        (pc,(h,(v::s),l)) (k::st) b
        (pc',(h,(Num (I (Int.const 0))::s),l)) (k::st) b.

      Inductive NormalStep_lookupswitch (def:OFFSET.t) (listkey:list (Z*OFFSET.t)) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | lookupswitch1 : forall h pc s l i i' o' k st b,

        List.In (pair i' o')listkey ->
        i' = Int.toZ i ->
        (forall j, region pc None j -> k <= se j) -> 

        NormalStep_lookupswitch def listkey m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc o',(h,s,l)) (lift k st) b
      | lookupswitch2 : forall h pc s l i k st b,

        (forall i' o', List.In (pair i' o')listkey ->  i' <> Int.toZ i) ->
        (forall j, region pc None j -> k <= se j) -> 

        NormalStep_lookupswitch def listkey m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc def,(h,s,l)) (lift k st) b.

      Inductive NormalStep_new (c:ClassName) (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | new : forall h pc pc' s l loc h' st b,

        next m pc = Some pc' ->
        Heap.new h p.(prog) (Heap.LocationObject c) = Some (pair loc h') ->

        NormalStep_new c m sgn 
        (pc,(h,s,l)) st b
        (pc',(h',(Ref loc::s),l)) (L.Simple (se pc)::st) (newb (se pc) b loc).

      Inductive NormalStep_newarray (t:type) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | newarray : forall h pc pc' s l i loc h' k st b,

        next m pc = Some pc' ->
        (0 <= Int.toZ i)%Z -> 
        Heap.new h p.(prog) (Heap.LocationArray i t (m,pc)) = Some (pair loc h') ->
        (forall j, region pc None j -> k <= (se j)) -> 

        NormalStep_newarray t m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (pc',(h',(Ref loc::s),l)) (L.Array k (newArT p (m,pc))::elift m pc k st) (newb k b loc).

      Inductive NormalStep_nop (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | nop : forall h pc pc' s l st b,

        next m pc = Some pc' ->

        NormalStep_nop m sgn (pc,(h,s,l)) st b (pc',(h,s,l)) st b. 

      Inductive NormalStep_pop (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | pop : forall h pc pc' s l v k st b,

        next m pc = Some pc' ->

        NormalStep_pop m sgn (pc,(h,(v::s),l)) (k::st) b (pc',(h,s,l)) st b.

      Inductive NormalStep_pop2 (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | pop2 : forall h pc pc' s l v1 v2 k1 k2 st b,

        next m pc = Some pc' ->

        NormalStep_pop2 m sgn (pc,(h,(v1::v2::s),l)) (k1::k2::st) b (pc',(h,s,l)) st b.

      Inductive NormalStep_putfield (f:FieldSignature) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | putfield : forall h pc pc' s l loc cn v k1 k2 st b,

        next m pc = Some pc' ->
        Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
        defined_field p.(prog) cn f ->
        assign_compatible p.(prog) h v (FIELDSIGNATURE.type (snd f)) ->
        k1 <=' (ft f) -> 
        k2 <= (ft f) -> 
        (se pc) <= (ft f) -> 
        sgn.(heapEffect) <= (ft f) -> 
        (forall j, region pc None j -> k2 <= (se j)) -> 

        NormalStep_putfield f m sgn 
        (pc,(h,(v::(Ref loc)::s),l)) (k1::L.Simple k2::st) b
        (pc',(Heap.update h (Heap.DynamicField loc f) v,s,l)) (elift m pc k2 st) b.


      Inductive NormalStep_swap (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | swap : forall h pc pc' s l v1 v2 k1 k2 st b,

        next m pc = Some pc' ->

        NormalStep_swap m sgn 
        (pc,(h,(v1::v2::s),l)) (k1::k2::st) b
        (pc',(h,(v2::v1::s),l)) (k2::k1::st) b.

      Inductive NormalStep_tableswitch (def:OFFSET.t) (low high:Z) (list_offset:list OFFSET.t) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | tableswitch1 : forall h pc s l i st b k,

        Z_of_nat (length list_offset) = (high - low + 1)%Z ->
        (Int.toZ i < low \/ high < Int.toZ i)%Z ->
        (forall j, region pc None j -> k <= se j) -> 
        
        NormalStep_tableswitch def low high list_offset m sgn
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc def,(h,s,l)) (lift k st) b
      | tableswitch2 : forall h pc s l n i st b o k,

        Z_of_nat (length list_offset) = (high - low + 1)%Z ->
        (low <= Int.toZ i <= high)%Z ->
        Z_of_nat n = ((Int.toZ i) - low)%Z ->
        nth_error list_offset n = Some o ->
        (forall j, region pc None j -> k <= se j) -> 
        
        NormalStep_tableswitch def low high list_offset m sgn 
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) b
        (OFFSET.jump pc o,(h,s,l)) (lift k st) b.

      Inductive NormalStep_vaload (k:ArrayKind)  (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | vaload : forall h pc pc' s l loc val i length t k1 k2 mpc st b,

        next m pc = Some pc' ->
        Heap.typeof h loc = Some (Heap.LocationArray length t mpc) ->
        compat_ArrayKind_type k t ->
        (0 <= Int.toZ i < Int.toZ length)%Z ->
        Heap.get h (Heap.ArrayElement loc (Int.toZ i)) = Some val ->
        compat_ArrayKind_type k t ->
        compat_ArrayKind_value k val ->
        (forall j, region pc None j -> k2 <= (se j)) -> 
        (forall j, region pc None j -> (L.join k1 k2) <= (se j)) -> 

        NormalStep_vaload k m sgn 
        (pc,(h,((Num (I i))::(Ref loc)::s),l)) (L.Simple k1::L.Array k2 (newArT p mpc)::st) b
        (pc',(h,(conv_for_stack val::s),l)) (L.join' (L.join k1 k2) (newArT p mpc)::elift m pc (L.join k1 k2) st) b.

      Inductive NormalStep_vastore (k:ArrayKind) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | vastore : forall h pc pc' s l loc val i length t kv ki ka mpc b st,

        next m pc = Some pc' ->
        Heap.typeof h loc = Some (Heap.LocationArray length t mpc) ->
        assign_compatible p.(prog) h val t ->
        (0 <= Int.toZ i < Int.toZ length)%Z ->
        compat_ArrayKind_type k t ->
        compat_ArrayKind_value k val ->
        kv <=' (newArT p mpc) -> ki <= (newArT p mpc) -> ka <= (newArT p mpc) ->
        L.leql (heapEffect sgn) (newArT p mpc) ->
        (forall j, region pc None j -> ka <= (se j)) -> 
        (forall j, region pc None j -> (L.join ki ka) <= (se j)) -> 
        (forall j, region pc None j -> (newArT p mpc) <= (se j)) -> 

        NormalStep_vastore k m sgn 
        (pc,(h,(val::(Num (I i))::(Ref loc)::s),l)) (kv::L.Simple ki::L.Array ka (newArT p mpc)::st) b
        (pc',(Heap.update h (Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val t),s,l)) (elift m pc (newArT p mpc) st) b.

      Inductive NormalStep_vload (k:ValKind) (x:Var) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | vload : forall h pc pc' s l val st b,

        instructionAt m pc = Some (Vload k x) ->
        next m pc = Some pc' ->
        METHOD.valid_var m x ->
        LocalVar.get l x = Some val ->
        compat_ValKind_value k val -> 

        NormalStep_vload k x m sgn 
        (pc,(h,s,l)) st b
        (pc',(h,(val::s),l)) (L.join' (se pc) (sgn.(lvt) x)::st) b.
      
      Inductive NormalStep_vstore (k:ValKind) (x:Var) (m:Method) (sgn:sign)  :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | vstore : forall h pc pc' s l l' v kv st b,

        next m pc = Some pc' ->
        METHOD.valid_var m x ->
        l' = LocalVar.update l x v ->
        compat_ValKind_value k v ->
        (se pc) <= (sgn.(lvt) x) -> 
        L.leql' kv (sgn.(lvt) x) ->      

        NormalStep_vstore k x m sgn 
        (pc,(h,(v::s),l)) (kv::st) b
        (pc',(h,s,l')) st b.


      Definition NormalStep 
        (m:Method) (sgn:sign) (i:Instruction) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
        match i with
          | Aconst_null => NormalStep_aconst_null m sgn 
          | Arraylength  => NormalStep_arraylength m sgn
          | Athrow => fun _ _ _ _ _ _ => False
          | Checkcast t => NormalStep_checkcast1 t m sgn
          | Const t z => NormalStep_const t z m sgn
          | Dup => NormalStep_dup m sgn
          | Dup_x1 => NormalStep_dup_x1 m sgn
          | Dup_x2 => NormalStep_dup_x2 m sgn
          | Dup2 => NormalStep_dup2 m sgn
          | Dup2_x1 => NormalStep_dup2_x1 m sgn
          | Dup2_x2 => NormalStep_dup2_x2 m sgn
          | Getfield f => NormalStep_getfield f m sgn
          | Goto o => NormalStep_goto o m sgn
          | I2b => NormalStep_i2b m sgn
          | I2s => NormalStep_i2s m sgn
          | Ibinop op => NormalStep_ibinop m sgn op
          | If_acmp cmp o => NormalStep_if_acmp cmp o m sgn
          | If_icmp cmp o  => NormalStep_if_icmp cmp o m sgn
          | If0 cmp o => NormalStep_if0 cmp o m sgn
          | Ifnull cmp o => NormalStep_ifnull cmp o m sgn
          | Iinc x z => NormalStep_iinc x z m sgn
          | Ineg  => NormalStep_ineg m sgn
          | Instanceof t  => NormalStep_instanceof t m sgn
          | Invokeinterface mid => fun _ _ _ _ _ _ => False
          | Invokespecial mid => fun _ _ _ _ _ _ => False
          | Invokestatic mid =>  fun _ _ _ _ _ _ => False
          | Invokevirtual mid => fun _ _ _ _ _ _ => False
          | Lookupswitch def listkey  => NormalStep_lookupswitch def listkey m sgn
(*   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) *)
          | New c => NormalStep_new c m sgn
          | Newarray t => NormalStep_newarray t m sgn
          | Nop => NormalStep_nop m sgn
          | Pop => NormalStep_pop m sgn
          | Pop2 => NormalStep_pop2 m sgn
          | Putfield f => NormalStep_putfield f m sgn
          | Return => fun _ _ _ _ _ _ => False
          | Swap  => NormalStep_swap m sgn
          | Tableswitch def low high list_offset => NormalStep_tableswitch def low high list_offset m sgn
          | Vaload k  => NormalStep_vaload k m sgn
          | Vastore k => NormalStep_vastore k m sgn
          | Vload k x => NormalStep_vload k x m sgn
          | Vreturn k => fun _ _ _ _ _ _ => False
          | Vstore k x => NormalStep_vstore k x m sgn
        end.


      Inductive JVMExceptionStep_arraylength  
        (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | arraylength_NullPointerException : forall h pc s l k st,

        JVMExceptionStep_arraylength m sgn
        (pc,(h,(Null::s),l)) (k::st) k NullPointerException.

      Inductive JVMExceptionStep_athrow  
        (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | athrow_NullPointerException : forall h pc s l k st,

        JVMExceptionStep_athrow m sgn
        (pc,(h,(Null::s),l)) (L.Simple k::st) k NullPointerException.
 (* athrow getfield *)

      Inductive JVMExceptionStep_checkcast (m:Method) (sgn:sign) (t:refType):
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | checkcast_ClassCastException : forall h pc s l loc k st,

        ~ assign_compatible p.(prog) h (Ref loc) (ReferenceType t) ->

        JVMExceptionStep_checkcast m sgn t
        (pc,(h,(Ref loc::s),l)) (k::st) k ClassCastException.


      Inductive JVMExceptionStep_getfield
        (m:Method) (sgn:sign) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | getfield_NullPointerException : forall h pc s l k st,

        JVMExceptionStep_getfield m sgn
        (pc,(h,(Null::s),l)) (L.Simple k::st) k NullPointerException.

      Inductive JVMExceptionStep_ibinop (m:Method) (sgn:sign) (op:BinopInt) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | ibinop_ArithmeticException : forall h pc s l i1 i2 k1 k2 st,

        op = DivInt \/ op = RemInt ->
        Int.toZ i2 = 0%Z ->

        JVMExceptionStep_ibinop m sgn op
        (pc,(h,(Num (I i2)::Num (I i1)::s),l)) (L.Simple k1::L.Simple k2::st) k1 ArithmeticException.


      Inductive JVMExceptionStep_invokevirtual (m:Method) (sgn:sign) (mid:MethodSignature) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | invokevirtual_NullPointerException : forall h pc s l args st1 k st2,

        length args = length (METHODSIGNATURE.parameters (snd mid)) ->
        length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->

        JVMExceptionStep_invokevirtual m sgn mid
        (pc,(h,(args++Null::s),l)) (st1++L.Simple k::st2) 
        (L.join k
          (L.join k
            (resExceptionType (virtual_signature p (snd mid) k) np)))
        NullPointerException.

      Inductive JVMExceptionStep_newarray (m:Method) (sgn:sign) (t:type) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | newarray_NegativeArraySizeException : forall h pc s l i k st,

        ~ (0 <= Int.toZ i)%Z ->

        JVMExceptionStep_newarray m sgn t
        (pc,(h,(Num (I i)::s),l)) (L.Simple k::st) k NegativeArraySizeException.

      Inductive JVMExceptionStep_putfield (m:Method) (sgn:sign) (f:FieldSignature) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | putfield_NullPointerException : forall h pc s l v k1 k2 st,

        
        JVMExceptionStep_putfield m sgn f
        (pc,(h,(v::Null::s),l)) (k1::L.Simple k2::st) k2 NullPointerException.

      Inductive JVMExceptionStep_vaload (m:Method) (sgn:sign) (k:ArrayKind) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | vaload_NullPointerException : forall h pc s l i k1 k2 ke st,

        JVMExceptionStep_vaload m sgn k
        (pc,(h,((Num (I i))::Null::s),l)) (L.Simple k1::L.Array k2 ke::st) k2 NullPointerException
      | vaload_ArrayIndexOutOfBoundsException : forall h pc s l loc i length t k1 k2 mpc st,

        Heap.typeof h loc = Some (Heap.LocationArray length t mpc) ->
        compat_ArrayKind_type k t ->
        ~ (0 <= Int.toZ i < Int.toZ length)%Z ->

        JVMExceptionStep_vaload m sgn k
        (pc,(h,((Num (I i))::(Ref loc)::s),l)) (L.Simple k1::L.Array k2 (newArT p mpc)::st) (L.join k1 k2) ArrayIndexOutOfBoundsException.

      Inductive JVMExceptionStep_vastore (m:Method) (sgn:sign) (k:ArrayKind) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
      | vastore_NullPointerException : forall h pc s l val i k1 k2 k3 ke st,

        compat_ArrayKind_value k val ->

        JVMExceptionStep_vastore m sgn k
        (pc,(h,(val::(Num (I i))::Null::s),l)) (k1::L.Simple k2::L.Array k3 ke::st) k3 NullPointerException
      | vastore_ArrayIndexOutOfBoundsException : forall h pc s l loc val i t length k1 k2 k3 mpc st,

        Heap.typeof h loc = Some (Heap.LocationArray length t mpc) ->
        ~ (0 <= Int.toZ i < Int.toZ length)%Z ->
        compat_ArrayKind_type k t ->
        compat_ArrayKind_value k val ->

        JVMExceptionStep_vastore m sgn k
        (pc,(h,(val::(Num (I i))::(Ref loc)::s),l)) (k1::L.Simple k2::L.Array k3 (newArT p mpc)::st) (L.join k2 k3) ArrayIndexOutOfBoundsException
      | vastore_ArrayStoreException : forall h pc s l loc val i t length (k1:L.t') k2 k3 mpc (st:list L.t'),

        Heap.typeof h loc = Some (Heap.LocationArray length t mpc) ->
        ~ assign_compatible p.(prog) h val t ->
        (0 <= Int.toZ i < Int.toZ length)%Z ->
        compat_ArrayKind_type k t ->
        compat_ArrayKind_value k val ->
(*    k1 <=' ke -> k2 <= ke -> k3 <= ke -> *)

        JVMExceptionStep_vastore m sgn k
        (pc,(h,(val::(Num (I i))::(Ref loc)::s),l)) (k1::L.Simple k2::L.Array k3 (newArT p mpc)::st) 
        (L.join k1 (L.join k2 k3)) ArrayStoreException.

      Definition JVMExceptionStep 
        (m:Method) (sgn:sign) (i:Instruction) :
        IntraNormalState -> TypeStack -> L.t -> ShortClassName -> Prop :=
        match i with
          | Aconst_null => fun _ _ _ _ => False
          | Arraylength  => JVMExceptionStep_arraylength m sgn
          | Athrow => JVMExceptionStep_athrow m sgn
          | Checkcast t => JVMExceptionStep_checkcast m sgn t
          | Const t z => fun _ _ _ _ => False
          | Dup => fun _ _ _ _ => False
          | Dup_x1 => fun _ _ _ _ => False
          | Dup_x2 => fun _ _ _ _ => False
          | Dup2 => fun _ _ _ _ => False
          | Dup2_x1 => fun _ _ _ _ => False
          | Dup2_x2 => fun _ _ _ _ => False
          | Getfield f => JVMExceptionStep_athrow m sgn
          | Goto o => fun _ _ _ _ => False
          | I2b => fun _ _ _ _ => False
          | I2s => fun _ _ _ _ => False
          | Ibinop op => JVMExceptionStep_ibinop m sgn op
          | If_acmp cmp o => fun _ _ _ _ => False
          | If_icmp cmp o  => fun _ _ _ _ => False
          | If0 cmp o => fun _ _ _ _ => False
          | Ifnull cmp o => fun _ _ _ _ => False
          | Iinc x z => fun _ _ _ _ => False
          | Ineg  => fun _ _ _ _ => False
          | Instanceof t  => fun _ _ _ _ => False
          | Invokeinterface mid => fun _ _ _ _ => False
          | Invokespecial mid => fun _ _ _ _ => False
          | Invokestatic mid => fun _ _ _ _ => False
          | Invokevirtual mid => JVMExceptionStep_invokevirtual m sgn mid
          | Lookupswitch def listkey  => fun _ _ _ _ => False
(*   | Multianewarray (t:refType) (d:Z) | New (cl:ClassName) *)
          | New c => fun _ _ _ _ => False
          | Newarray t => JVMExceptionStep_newarray m sgn t
          | Nop => fun _ _ _ _ => False
          | Pop => fun _ _ _ _ => False
          | Pop2 => fun _ _ _ _ => False
          | Putfield f => JVMExceptionStep_putfield m sgn f
          | Return => fun _ _ _ _ => False
          | Swap  => fun _ _ _ _ => False
          | Tableswitch def low high list_offset => fun _ _ _ _ => False
          | Vaload k  => JVMExceptionStep_vaload m sgn k
          | Vastore k => JVMExceptionStep_vastore m sgn k
          | Vload k x => fun _ _ _ _ => False
          | Vreturn k => fun _ _ _ _ => False
          | Vstore k x => fun _ _ _ _ => False
        end.


      Inductive ExceptionStep (m:Method) (sgn:sign): Instruction ->
        IntraNormalState -> TypeStack -> FFun.t Location -> 
        IntraExceptionState -> L.t -> FFun.t Location -> ClassName -> Prop :=
      | athrow : forall h pc s l loc cn k st b,

        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        subclass_name p.(prog) cn javaLangThrowable ->

        ExceptionStep m sgn Athrow
        (pc,(h,(Ref loc::s),l)) (L.Simple k::st) b
        (h,loc) k b cn
      | jvm_exception : forall h pc s l h' loc (e:ShortClassName) st k b i,

        JVMExceptionStep m sgn i (pc,(h,s,l)) st k e ->
        Heap.new h p.(prog) (Heap.LocationObject (javaLang,e)) = Some (loc,h') ->

        ExceptionStep m sgn i
        (pc,(h,s,l)) st b
        (h',loc) k (newb k b loc) (javaLang,e).

      Inductive ReturnStep (m:Method) (sgn:sign) : Instruction ->
        IntraNormalState -> TypeStack -> ReturnState -> Prop :=
      | void_return : forall h pc s l st,

        METHODSIGNATURE.result (METHOD.signature m) = None ->
        sgn.(resType) = None ->

        ReturnStep m sgn Return
        (pc,(h,s,l)) st (h, Normal None)
      | vreturn : forall h pc s l val t k k1 st kr,

        METHODSIGNATURE.result (METHOD.signature m) = Some t ->
        assign_compatible p.(prog) h val t ->
        compat_ValKind_value k val ->
        sgn.(resType) = Some kr ->
        L.leql' k1 kr ->

        ReturnStep m sgn (Vreturn k)
        (pc,(h,(val::s),l)) (k1::st) (h,Normal (Some val)).

      Definition chooseb (k:L.t) (b1 b2:FFun.t Location) : FFun.t Location :=
        if L.leql_dec k kobs then b1 else b2.

      Inductive CallStep (m:Method) (sgn:sign) : Instruction -> 
        IntraNormalState -> TypeStack -> 
        InitCallState -> sign -> TypeStack -> 
        option L.t -> L.t ->
        FFun.t Location -> FFun.t Location -> FFun.t Location -> Prop :=
      | invokestatic : forall h pc s l mid M args bM st1 st2 b1 b2,

        findMethod p.(prog) mid = Some M ->
        METHOD.isNative M = false ->
        length args = length (METHODSIGNATURE.parameters (snd mid)) ->
        METHOD.body M = Some bM ->
        length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
        compat_type_st_lvt (static_signature p (snd mid)) (st1++st2) (length st1) ->
        (se pc) <= (static_signature p (snd mid)).(heapEffect) -> 
        METHOD.isStatic M = true ->
        
        CallStep m sgn (Invokestatic mid)
        (pc,(h,(args++s),l)) (st1++st2) 
        (M,(s,(stack2localvar (args++s) (length args)))) (static_signature p (snd mid)) st2 None
        (se pc)
        b1 b2 (chooseb (se pc) b2 b1)

      | invokevirtual : forall h pc s l (mid:MethodSignature) cn M args loc cl bM st1 (k1:L.t) st2 b1 b2,

        lookup p.(prog) cn (snd mid) (pair cl M) ->
        Heap.typeof h loc = Some (Heap.LocationObject cn) ->
        length args = length (METHODSIGNATURE.parameters (snd mid)) ->
        METHOD.body M = Some bM ->
        length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
        compat_type_st_lvt (virtual_signature p (snd mid) k1) (st1++L.Simple k1::st2) (1+(length st1)) ->
        k1 <= (virtual_signature p (snd mid) k1).(heapEffect) -> 
        METHOD.isStatic M = false ->
        
        CallStep m sgn (Invokevirtual mid)
        (pc,(h,(args++(Ref loc)::s),l)) (st1++L.Simple k1::st2) 
        (M,(s,stack2localvar (args++(Ref loc)::s) (1+(length args))))
        (virtual_signature p (snd mid) k1) st2 (Some k1)
        k1
        b1 b2 (chooseb k1 b2 b1).

      Inductive CalledSignature : Instruction -> TypeStack -> sign -> Prop :=
      | invokestatic_callsign : forall mid st1 st2,
        length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
        CalledSignature (Invokestatic mid) (st1++st2) (static_signature p (snd mid))
      | invokevirtual_callsign : forall mid st1 k1 st2,
        length st1 = length (METHODSIGNATURE.parameters (snd mid)) ->
        CalledSignature (Invokevirtual mid) (st1++L.Simple k1::st2) (virtual_signature p (snd mid) k1).

      Inductive exec_call (m:Method) (sgn:sign) (i:Instruction) :
        IntraNormalState -> TypeStack -> FFun.t Location ->
        ReturnState -> FFun.t Location ->
        Method -> sign -> 
        IntraNormalState -> TypeStack -> FFun.t Location ->
        (IntraNormalState*TypeStack) + ReturnState -> FFun.t Location -> 
        option ClassName -> Prop :=
      | exec_call_normal : forall m2 pc1 pc1' h1 s1 l1 os l2 h2 bm2 ov st st' b b' b'' sgn' ok k,
        CallStep m sgn i (pc1,(h1,s1,l1 )) st (m2,(os,l2)) sgn' st' ok k b b' b'' ->
        METHOD.body m2 = Some bm2 ->
        next m pc1 = Some pc1' ->
        k <= sgn'.(heapEffect) -> 
        compat_op sgn'.(resType) ov ->
        (forall j, region pc1 None j -> 
          (join_op' (join_list sgn'.(resExceptionType) (throwableBy p (METHOD.signature m2))) ok) <= (se j)) -> 
        sgn.(heapEffect) <= sgn'.(heapEffect) -> 
        exec_call m sgn i
        (pc1,(h1,s1,l1)) st b
        (h2,Normal ov) b'
        m2 sgn'
        (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2)) nil b
        (inl _ ((pc1',(h2,cons_option ov os,l1)),
          olift ok
          (lift (join_list sgn'.(resExceptionType) (throwableBy p (METHOD.signature m2))) 
            (cons_option (join_op k sgn'.(resType)) st'))))
        b'' None

      | exec_call_caught : forall m2 pc1 pc1' h1 s1 l1 os l2 h2 loc bm2 st st' b b' b'' sgn' cn ok k,
        CallStep m sgn i (pc1,(h1,s1,l1 )) st (m2,(os,l2)) sgn' st' ok k b b' b'' ->
        METHOD.body m2 = Some bm2 ->
        CaughtException p.(prog) m (pc1, h2, loc) pc1' ->
        Heap.typeof h2 loc = Some (Heap.LocationObject cn) ->
        In cn (throwableBy p (METHOD.signature m2)) ->
        k <= sgn'.(heapEffect) -> 
        (forall j, region pc1 (Some cn) j -> 
          (join_op' (sgn'.(resExceptionType) cn) ok) <= (se j)) -> 
        sgn.(heapEffect) <= sgn'.(heapEffect) -> 
        exec_call m sgn i
        (pc1,(h1,s1,l1)) st b
        (h2,Exception loc) b'
        m2 sgn'
        (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2)) nil b
        (inl _((pc1',(h2,Ref loc::nil,l1)),
          olift ok
          (L.Simple (L.join k (sgn'.(resExceptionType) cn))::nil)))
        b'' (Some cn)

      | exec_call_uncaught : forall m2 pc1 h1 s1 l1 os l2 h2 loc bm2 st st' b b' b'' sgn' cn ok k,
        CallStep m sgn i (pc1,(h1,s1,l1 )) st (m2,(os,l2)) sgn' st' ok k b b' b'' ->
        METHOD.body m2 = Some bm2 ->
        UnCaughtException p.(prog) m (pc1, h2, loc)  ->
        Heap.typeof h2 loc = Some (Heap.LocationObject cn) ->
        In cn (throwableBy p (METHOD.signature m2)) ->
        k <= sgn'.(heapEffect) -> 
        k <= (sgn.(resExceptionType) cn) -> 
        (sgn'.(resExceptionType) cn) <= (sgn.(resExceptionType) cn) -> 
        (forall j, region pc1 (Some cn) j -> 
          (join_op' (sgn'.(resExceptionType) cn) ok) <= (se j)) -> 
        sgn.(heapEffect) <= sgn'.(heapEffect) -> 
        exec_call m sgn i
        (pc1,(h1,s1,l1)) st b
        (h2,Exception loc) b'
        m2 sgn'
        (BYTECODEMETHOD.firstAddress bm2,(h1,OperandStack.empty,l2)) nil b
        (inr _ (h2,Exception loc))
        b'' (Some cn).

      Inductive exec_intra (m:Method) (sgn:sign) (i:Instruction) :
        option ClassName ->
        IntraNormalState -> TypeStack -> FFun.t Location ->
        IntraNormalState -> TypeStack -> FFun.t Location -> Prop :=
      | exec_intra_normal : forall s1 s2 st1 st2 b1 b2,
        NormalStep m sgn i s1 st1 b1 s2 st2 b2 ->
        exec_intra m sgn i None s1 st1 b1 s2 st2 b2
      | exec_exception : forall pc1 h1 h2 loc2 s1 l1 pc' st b1 k b2 e,
        ExceptionStep m sgn i (pc1,(h1,s1,l1)) st b1 (h2,loc2) k b2 e ->
        CaughtException p.(prog) m (pc1,h2,loc2) pc' ->
        (forall j, region pc1 (Some e) j -> k <= (se j)) -> 
        In e (Dom.Prog.throwableAt m pc1) ->
        exec_intra m sgn i (Some e) 
        (pc1,(h1,s1,l1)) st b1
        (pc',(h2,Ref loc2::OperandStack.empty,l1)) (L.Simple k::nil) b2.

      Inductive exec_return (m:Method) (sgn:sign) (i:Instruction) :
        option ClassName ->
        IntraNormalState -> TypeStack -> FFun.t Location ->
        ReturnState -> FFun.t Location -> Prop :=
      | exec_return_normal : forall s h ov st b,
        ReturnStep m sgn i s st (h,Normal ov) ->
        exec_return m sgn i None s st b (h,Normal ov) b
      | exec_return_exception : forall pc1 h1 h2 loc2 s1 l1 st b1 k b2 e,
        ExceptionStep m sgn i (pc1,(h1,s1,l1)) st b1 (h2,loc2) k b2 e ->
        UnCaughtException p.(prog) m (pc1,h2,loc2) ->
        (forall j, region pc1 (Some e) j -> k <= (se j)) -> 
        In e (Dom.Prog.throwableAt m pc1) ->
        L.leql k (sgn.(resExceptionType) e) ->
        exec_return m sgn i (Some e) (pc1,(h1,s1,l1)) st b1 (h2,Exception loc2) b2.

      Inductive exec (m:Method) (sgn:sign) (i:Instruction) (kd:option ClassName) : state -> state -> Prop :=
      | exec_intra_case : forall s1 st1 b1 s2 st2 b2,
        exec_intra m sgn i kd s1 st1 b1 s2 st2 b2 ->
        exec m sgn i kd (intra s1 st1 b1) (intra s2 st2 b2)
      | exec_return_case : forall pc1 h1 s1 l1 st1 b1 h2 v2 b2,
        exec_return m sgn i kd (pc1,(h1,s1,l1)) st1 b1 (h2,v2) b2 ->
        exec m sgn i kd (intra (pc1,(h1,s1,l1)) st1 b1) (ret h2 v2 b2).

    End annot.
  End p.

End BigStepWithTypes.

Import BigStep.BigStep Dom Prog.


Section p.
  Variable p : ExtendedProgram.

  Lemma NormalStep_instructionAt : forall m s1 s2,
    NormalStep p m s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_clear H; simpl; eauto.
  Qed.

  Lemma ExceptionStep_instructionAt : forall m s1 s2,
    BigStepAnnot.ExceptionStep throwableAt p m s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_clear H; simpl.
    eauto.
    inversion_clear H0; eauto.
  Qed.

  Lemma exec_intra_instructionAt : forall m kd s1 s2,
    BigStepAnnot.exec_intra throwableAt p m kd s1 s2 ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_mine H.
    eapply NormalStep_instructionAt; eauto.
    eapply ExceptionStep_instructionAt; eauto.
  Qed.

  Lemma exec_return_instructionAt : forall m kd s r,
    @BigStepAnnot.exec_return throwableAt p m kd s r ->
    exists i, instructionAt m (fst s) = Some i.
  Proof.
    intros.
    inversion_mine H.
    inversion_mine H0; simpl; eauto.
    eapply ExceptionStep_instructionAt; eauto.
  Qed.

  Lemma CallStep_instructionAt : forall m s1 msl,
    CallStep p m s1 msl ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_mine H; simpl; eauto.
  Qed.

  Lemma exec_call_instructionAt : forall m s1 ret' m' s' r tau,
    @BigStepAnnot.exec_call (throwableBy p) p m tau s1 ret' m' s' r ->
    exists i, instructionAt m (fst s1) = Some i.
  Proof.
    intros.
    inversion_mine H;
    eapply CallStep_instructionAt; eauto.
  Qed.

  Definition typeof_stable (h1 h2:Heap.t) : Prop :=
    forall loc,
      Heap.typeof h1 loc <> None ->
      Heap.typeof h1 loc = Heap.typeof h2 loc.

  Opaque Heap.update.

  Lemma typeof_stable_exec_intra : forall m tau s1 s2,
    BigStepAnnot.exec_intra throwableAt p m tau s1 s2 ->
    typeof_stable (fst (fst (snd s1))) (fst (fst (snd s2))).
  Proof.
    unfold typeof_stable; intros.
    inversion_mine H.
    inversion_mine H1; simpl in H0; simpl; try reflexivity.
    destruct (eq_excluded_middle _ loc loc0); subst.
    rewrite (@Heap.new_fresh_location _ _ _ _ _ H3) in H0; intuition.
    symmetry; eapply Heap.new_typeof_old; eauto.
    destruct (eq_excluded_middle _ loc loc0); subst.
    rewrite (@Heap.new_fresh_location _ _ _ _ _ H4) in H0; intuition.
    symmetry; eapply Heap.new_typeof_old; eauto.
    rewrite Heap.typeof_update_same; auto.
    rewrite Heap.typeof_update_same; auto.
    inversion_mine H1; simpl in H0; simpl; try reflexivity.
    inversion_mine H7; try reflexivity;
      (destruct (eq_excluded_middle _ loc loc2); subst;
        [rewrite (@Heap.new_fresh_location _ _ _ _ _ H11) in H0; intuition
          |symmetry; eapply Heap.new_typeof_old; eauto]).
  Qed.
  
  Lemma typeof_stable_exec_return : forall m tau s1 r,
    BigStepAnnot.exec_return throwableAt p m tau s1 r ->
    typeof_stable (fst (fst (snd s1))) (fst r).
  Proof.
    unfold typeof_stable; intros.
    inversion_mine H.
    inversion_mine H1; simpl in H0; simpl; try reflexivity.
    inversion_mine H1; simpl in H0; simpl; try reflexivity.
    inversion_mine H7; try reflexivity;
      (destruct (eq_excluded_middle _ loc loc2); subst;
        [rewrite (@Heap.new_fresh_location _ _ _ _ _ H11) in H0; intuition
          |symmetry; eapply Heap.new_typeof_old; eauto]).
  Qed.

  Lemma typeof_stable_exec_call_inl : forall m s1 ret' m' s' s2 tau,
    @BigStepAnnot.exec_call (throwableBy p) p m tau s1 ret' m' s' (inl _ s2) ->
    typeof_stable (fst (fst (snd s'))) (fst ret') ->    
    typeof_stable (fst (fst (snd s1))) (fst (fst (snd s2))).
  Proof.
    intros.
    inversion_mine H; inversion_mine H2; simpl in *; auto.
  Qed.

  Lemma typeof_stable_exec_call_inr : forall m s1 ret' m' s' r tau,
    @BigStepAnnot.exec_call (throwableBy p) p m tau s1 ret' m' s' (inr _ r) ->
    typeof_stable (fst (fst (snd s'))) (fst ret') ->    
    typeof_stable (fst (fst (snd s1))) (fst r).
  Proof.
    intros.
    inversion_mine H; inversion_mine H2; simpl in *; auto.
  Qed.

End p.


