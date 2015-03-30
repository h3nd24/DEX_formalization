(* <Insert License Here>

    $Id: SmallStep.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

  Import Dom Prog.

  (** Small step semantics for the instruction set of the JVM *)
  Inductive step (p:Program) : State.t -> State.t -> Prop :=
 (** The current exception is caught in the current method *)
  | exception_caught : forall h m pc loc l sf pc',

    CaughtException p m (pc,h,loc) pc' ->

    step p (StE h (FrE m pc loc l) sf)
           (St h (Fr m pc' (Ref loc::nil) l) sf)

 (** The current exception is uncaught *)
  | exception_uncaught : forall h m pc loc l m' pc' s' l' sf,

    UnCaughtException p m (pc,h,loc) ->

    step p (StE h (FrE m pc loc l) ((Fr m' pc' s' l')::sf))
           (StE h (FrE m' pc' loc l') sf)

 (** <addlink>aconst_null</addlink>: Push [null] *)
  | aconst_null_step_ok : forall h m pc pc' s l sf,

    instructionAt m pc = Some Aconst_null ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc s l) sf) (St h (Fr m pc' (Null::s) l) sf)

 (** <addlink>arraylength</addlink>: Get length of array *)
  | arraylength_step_ok : forall h m pc pc' s l sf loc length tp a,

    instructionAt m pc = Some Arraylength ->
    next m pc = Some pc' ->
    Heap.typeof  h loc = Some (Heap.LocationArray length tp a) ->

    step p (St h (Fr m pc (Ref loc::s) l) sf) (St h (Fr m pc' (Num (I length)::s) l) sf)

  | arraylength_step_NullPointerException : forall h m pc s l sf h' loc',

    instructionAt m pc = Some Arraylength ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** <addlink>athrow</addlink>: Throw exception or error *)
  | athrow_step : forall h m pc s l sf loc cn,

    instructionAt m pc = Some Athrow ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    subclass_name p cn javaLangThrowable ->

    step p (St h (Fr m pc (Ref loc::s) l) sf)
           (StE h (FrE m pc loc l) sf)

  | athrow_step_NullPointerException : forall h m pc s l sf  h' loc',

    instructionAt m pc = Some Athrow ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** <addlink>checkcast</addlink>: Check whether object is of given type *)
  | checkcast_step_ok1 : forall h m pc pc' s l sf val t,

    instructionAt m pc = Some (Checkcast t) ->
    next m pc = Some pc' ->
    assign_compatible p h val (ReferenceType t) ->

    step p (St h (Fr m pc (val::s) l) sf) (St h (Fr m pc' (val::s) l) sf)

  | checkcast_step_ClassCastException : forall h m pc s l sf loc t h' loc',

    instructionAt m pc = Some (Checkcast t) ->
    ~ assign_compatible p h (Ref loc) (ReferenceType t) ->
    Heap.new h p (Heap.LocationObject (javaLang,ClassCastException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Ref loc::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** const : Push numeric constant (<addlink>bipush</addlink>, <addlink>iconst</addlink>, <addlink>ldc</addlink>(no string constant supported), <addlink>sipush</addlink>) *)
  | const_step_ok : forall h m pc pc' s l sf t z,

    instructionAt m pc = Some (Const t z) ->
    next m pc = Some pc' ->
    (   (t=BYTE /\ -2^7 <= z < 2^7)
     \/ (t=SHORT /\ -2^15 <= z < 2^15)
     \/ (t=INT /\ -2^31 <= z < 2^31)   ) ->
    
    step p (St h (Fr m pc s l) sf) (St h (Fr m pc' (Num (I (Int.const z))::s) l) sf)
 (** <addlink>dup</addlink>: Duplicate the top operand stack value *)
  | dup_step_ok : forall h m pc pc' s l sf v,

    instructionAt m pc = Some Dup ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v::s) l) sf) (St h (Fr m pc' (v::v::s) l) sf)
 (** <addlink>dup_x1</addlink>: Duplicate the top operand stack value and insert two values down *)
  | dup_x1_step_ok : forall h m pc pc' s l sf v1 v2,

    instructionAt m pc = Some Dup_x1 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::s) l) sf) (St h (Fr m pc' (v1::v2::v1::s) l) sf)
 (** <addlink>dup_x2</addlink>: Duplicate the top operand stack value and insert two or three values down *)
  | dup_x2_step_ok : forall h m pc pc' s l sf v1 v2 v3,

    instructionAt m pc = Some Dup_x2 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::v3::s) l) sf) (St h (Fr m pc' (v1::v2::v3::v1::s) l) sf)
 (** <addlink>dup2</addlink>: Duplicate the top one or two operand stack values *)
  | dup2_step_ok : forall h m pc pc' s l sf v1 v2,

    instructionAt m pc = Some Dup2 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::s) l) sf) (St h (Fr m pc' (v1::v2::v1::v2::s) l) sf)
 (** <addlink>dup2_x1</addlink>: Duplicate the top one or two operand stack values and insert two or three values down *)
  | dup2_x1_step_ok : forall h m pc pc' s l sf v1 v2 v3,

    instructionAt m pc = Some Dup2_x1 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::v3::s) l) sf) (St h (Fr m pc' (v1::v2::v3::v1::v2::s) l) sf)
 (** <addlink>dup2_x2</addlink>: Duplicate the top one or two operand stack values and insert two, three, or four values down *)
  | dup2_x2_step_ok : forall h m pc pc' s l sf v1 v2 v3 v4,

    instructionAt m pc = Some Dup2_x2 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::v3::v4::s) l) sf) 
                                                 (St h (Fr m pc' (v1::v2::v3::v4::v1::v2::s) l) sf)
 (** <addlink>getfield</addlink>: Fetch field from object *)
  | getfield_step_ok : forall h m pc pc' s l sf loc f v cn,

    instructionAt m pc = Some (Getfield f) ->
    next m pc = Some pc' ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Heap.get h (Heap.DynamicField loc f) = Some v ->    

    step p (St h (Fr m pc (Ref loc::s) l) sf) (St h (Fr m pc' (v::s) l) sf)

  | getfield_step_NullPointerException : forall h m pc s l sf f h' loc',

    instructionAt m pc = Some (Getfield f) ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** <addlink>getstatic</addlink>: Get [static] field from class *)
  (* REMOVED *)

 (** <addlink>goto</addlink>: Branch always *)
  | goto_step_ok : forall h m pc s l sf o,

    instructionAt m pc = Some (Goto o) ->

    step p (St h (Fr m pc s l) sf) (St h (Fr m (OFFSET.jump pc o) s l) sf)

 (** <addlink>i2b</addlink>: Convert [int] to [byte] *)
  | i2b_step_ok : forall h m pc pc' s l sf i,

    instructionAt m pc = Some I2b ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m pc' (Num (I (b2i (i2b i)))::s) l) sf)

 (** <addlink>i2s</addlink>: Convert [int] to [short] *)
  | i2s_step_ok : forall h m pc pc' s l sf i,

    instructionAt m pc = Some I2s ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m pc' (Num (I (s2i (i2s i)))::s) l) sf)

 (** ibinop (<addlink>iadd</addlink>, <addlink>iand</addlink>, <addlink>idiv</addlink>, <addlink>imul</addlink>, <addlink>ior</addlink>, <addlink>irem</addlink>, <addlink>ishl</addlink>, <addlink>ishr</addlink>, <addlink>isub</addlink>, <addlink>iushr</addlink>, <addlink>ixor</addlink>): Binary operations on [int] *)
  | ibinop_step_ok : forall h m pc pc' s l sf op i1 i2,

    instructionAt m pc = Some (Ibinop op) ->
    next m pc = Some pc' ->
    (op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> 

    step p (St h (Fr m pc (Num (I i2)::Num (I i1)::s) l) sf) 
                                        (St h (Fr m pc' (Num (I (SemBinopInt op i1 i2))::s) l) sf)

  | ibinop_ArithmeticException : forall h m pc s l sf op i1 i2 h' loc',

    instructionAt m pc = Some (Ibinop op) ->
    op = DivInt \/ op = RemInt ->
    Int.toZ i2 = 0 ->
    Heap.new h p (Heap.LocationObject (javaLang,ArithmeticException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Num (I i2)::Num (I i1)::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (*********  comparison instructions  ************)
 (** if_acmp (<addlink>if_acmpeq</addlink>, <addlink>if_acmpne</addlink>): Branch if reference comparison succeeds *)
  | if_acmp_step_jump : forall h m pc s l sf val2 val1 o cmp,
      instructionAt m pc = Some (If_acmp cmp o) ->
      SemCompRef cmp val1 val2 ->
    step p (St h (Fr m pc (val2::val1::s) l) sf)
           (St h (Fr m (OFFSET.jump pc o) s l) sf)
  (** Continue if reference comparison fails *)
  | if_acmp_step_continue : forall h m pc pc' s l sf val2 val1 o cmp,
      instructionAt m pc = Some (If_acmp cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompRef cmp val1 val2 ->
  (******************************************************************)
    step p (St h (Fr m pc (val2::val1::s) l) sf) (St h (Fr m pc' s l) sf)

 (** <addlink>if_icmp</addlink>: Branch if int comparison succeeds *)
  | if_icmp_step_jump : forall h m pc s l sf cmp i2 i1 o,
      instructionAt m pc = Some (If_icmp cmp o) ->
      SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
  (******************************************************************)
    step p (St h (Fr m pc (Num(I i2)::Num(I i1)::s) l) sf) 
           (St h (Fr m (OFFSET.jump pc o) s l) sf)
 (** <addlink>if_icmp</addlink>: Continue if int comparison fails *)
  | if_icmpeq_step_continue : forall h m pc pc' s l sf cmp i2 i1 o,
      instructionAt m pc = Some (If_icmp cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompInt cmp (Int.toZ i1) (Int.toZ i2) ->
  (******************************************************************)
    step p (St h (Fr m pc (Num(I i2)::Num(I i1)::s) l) sf)
           (St h (Fr m pc' s l) sf)

 (** if0 (<addlink>ifcond</addlink>): Branch if comparison with zero succeeds *)
  | ifeq_step_jump : forall h m pc s l sf cmp i o,
      instructionAt m pc = Some (If0 cmp o) ->
      SemCompInt cmp (Int.toZ i) 0 ->
  (******************************************************************)
    step p (St h (Fr m pc (Num (I i)::s) l) sf) 
           (St h (Fr m (OFFSET.jump pc o) s l) sf)
 (** if0 (<addlink>ifcond</addlink>): Continue if comparison with zero fails *)
  | ifeq_step_continue : forall h m pc pc' s l sf cmp i o,
      instructionAt m pc = Some (If0 cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompInt cmp (Int.toZ i) 0 ->
  (******************************************************************)
    step p (St h (Fr m pc (Num(I i)::s) l) sf) (St h (Fr m pc' s l) sf)

 (** <addlink>ifnull</addlink>: Branch if ref comparison with null succeeds *)
  | ifnull_step_jump : forall h m pc s l sf loc o cmp,
     instructionAt m pc = Some (Ifnull cmp o) ->
     SemCompRef cmp loc Null ->
  (******************************************************************)
    step p (St h (Fr m pc (loc::s) l) sf)
           (St h (Fr m (OFFSET.jump pc o) s l) sf)
 (** <addlink>ifnull</addlink>: Continue if ref comparison with null fails *) 
  | ifnull_step_continue : forall h m pc pc' s l sf o loc cmp,
      instructionAt m pc = Some (Ifnull cmp o) ->
      next m pc = Some pc' ->
      ~ SemCompRef cmp loc Null ->
  (******************************************************************)
    step p (St h (Fr m pc (loc::s) l) sf) (St h (Fr m pc' s l) sf)


 (** <addlink>iinc</addlink>: Increment local variable by constant *) 
  | iinc_step : forall h m pc s l sf pc' x z i,
    instructionAt m pc = Some (Iinc x z) ->

    next m pc = Some pc' ->
    -2^7 <= z < 2^7 ->
    METHOD.valid_var m x ->
    LocalVar.get l x = Some (Num (I i)) ->

    step p (St h (Fr m pc s l) sf) 
           (St h (Fr m pc' s (LocalVar.update l x (Num (I (Int.add i (Int.const z)))))) sf)

 (** <addlink>ineg</addlink>: Negate [int] *)
  | ineg_step : forall h m pc s l sf pc' i,

    instructionAt m pc = Some Ineg ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m pc' (Num (I (Int.neg i))::s) l) sf)

 (** <addlink>instanceof</addlink>: Determine if object is of given type *)
  | instanceof_step_ok1 : forall h m pc pc' s l sf loc t,

    instructionAt m pc = Some (Instanceof t) ->
    next m pc = Some pc' ->
    assign_compatible p h (Ref loc) (ReferenceType t) ->

    step p (St h (Fr m pc (Ref loc::s) l) sf) (St h (Fr m pc' (Num (I (Int.const 1))::s) l) sf)
 (** <addlink>instanceof</addlink>: with object == null *)
  | instanceof_step_ok2 : forall h m pc pc' s l sf t v,

    instructionAt m pc = Some (Instanceof t) ->
    next m pc = Some pc' ->
    isReference v ->
    (~ assign_compatible p h v (ReferenceType t) \/ v=Null) ->

    step p (St h (Fr m pc (v::s) l) sf) (St h (Fr m pc' (Num (I (Int.const 0))::s) l) sf)

 (** <addlink>invokestatic</addlink>: Invoke a class ([static]) method *)
  | invokestatic_step_ok : forall h m pc s l sf mid M args bM fnew,

    instructionAt m pc = Some (Invokestatic mid) ->
    findMethod p mid = Some M ->
    METHOD.isNative M = false ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    METHOD.body M = Some bM ->
    fnew = (Fr M
               (BYTECODEMETHOD.firstAddress bM)
                OperandStack.empty
               (stack2localvar (args++s)  (length args))) ->
 
    step p (St h (Fr m pc (args++s) l) sf) (St h fnew ((Fr m pc s l)::sf))


 (** <addlink>invokeinterface</addlink>: Invoke interface method *)
 (** <addlink>invokespecial</addlink>: Invoke instance method; 
             special handling for superclass, private, and instance initialization method invocations *)
 (** <addlink>invokevirtual</addlink>: Invoke instance method; dispatch based on class *)
  | invokevirtual_step_ok : forall h m pc s l sf mid cn M args loc cl bM fnew,

    instructionAt m pc = Some (Invokevirtual (cn,mid)) ->
    lookup p cn mid (pair cl M) ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) ->
    length args = length (METHODSIGNATURE.parameters mid) ->
    METHOD.body M = Some bM ->
    fnew = (Fr M
               (BYTECODEMETHOD.firstAddress bM)
                OperandStack.empty
               (stack2localvar (args++(Ref loc)::s)  (1+(length args)))) ->
 
    step p (St h (Fr m pc (args++(Ref loc)::s) l) sf) (St h fnew ((Fr m pc s l)::sf))

  | invokevirtual_step_NullPointerException : forall h m pc s l sf mid args h' loc',

    instructionAt m pc = Some (Invokevirtual mid) ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->

    step p (St h (Fr m pc (args++Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** <addlink>lookupswitch</addlink>: Access jump table by key match and jump *)
  | lookupswitch_step_ok1 : forall h m pc s l sf def listkey i i' o',

    instructionAt m pc = Some (Lookupswitch def listkey) ->

    List.In (pair i' o')listkey ->
    i' = Int.toZ i ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m (OFFSET.jump pc o') s l) sf)

  | lookupswitch_step_ok2 : forall h m pc s l sf def listkey i,

    instructionAt m pc = Some (Lookupswitch def listkey) ->
    (forall i' o', List.In (pair i' o')listkey ->  i' <> Int.toZ i) ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m (OFFSET.jump pc def) s l) sf)
  (** <addlink>multianewarray</addlink>: Create new multidimensional array *)
  (** <addlink>new</addlink>: Create new object *)
  | new_step_ok : forall h m pc pc' s l sf c loc h',

    instructionAt m pc = Some (New c) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc h') ->

    step p (St h (Fr m pc s l) sf) 
           (St h' (Fr m pc' (Ref loc::s) l) sf)

 (** Create new array (<addlink>anewarray</addlink>, <addlink>newarray</addlink>) *)
 (** OutOfMemory is not considered in Bicolano *)
  | newarray_step_ok : forall h m pc pc' s l sf i t loc h_new,

    instructionAt m pc = Some (Newarray t) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationArray i t (m,pc)) = Some (pair loc h_new) ->
    0 <= Int.toZ i ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf)
           (St h_new (Fr m pc' ((Ref loc)::s) l) sf)

  | newarray_step_NegativeArraySizeException : forall h m pc s l sf i t h' loc',

    instructionAt m pc = Some (Newarray t) ->
    ~ 0 <= Int.toZ i ->
    Heap.new h p (Heap.LocationObject (javaLang,NegativeArraySizeException)) = Some (loc',h') ->

    step p (St h (Fr m pc (Num (I i)::s) l) sf)
           (StE h' (FrE m pc loc' l) sf)

 (** <addlink>nop</addlink>: Do nothing *)
  | nop_step_ok : forall h m pc pc' s l sf,

    instructionAt m pc = Some Nop ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc s l) sf) (St h (Fr m pc' s l) sf)
  (** <addlink>pop</addlink>: Pop the top operand stack value *)
  | pop_step_ok : forall h m pc pc' s l sf v,

    instructionAt m pc = Some Pop ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v::s) l) sf) (St h (Fr m pc' s l) sf)
  (** <addlink>pop2</addlink>: Pop the top one or two operand stack values *)
  | pop2_step_ok : forall h m pc pc' s l sf v1 v2,

    instructionAt m pc = Some Pop2 ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::s) l) sf) (St h (Fr m pc' s l) sf)
  (** <addlink>putfield</addlink>: Set field in object *)
  | putfield_step_ok : forall h m pc pc' s l sf f loc cn v,

    instructionAt m pc = Some (Putfield f) ->
    next m pc = Some pc' ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    assign_compatible p h v (FIELDSIGNATURE.type (snd f)) ->

    step p (St h (Fr m pc (v::(Ref loc)::s) l) sf)
           (St (Heap.update h (Heap.DynamicField loc f) v) (Fr m pc' s l) sf)

  | putfield_step_NullPointerException : forall h m pc s l sf f v h' loc',

    instructionAt m pc = Some (Putfield f) ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->

    step p (St h (Fr m pc (v::Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

  (** <addlink>putstatic</addlink>: Set [static] field in class *)
  (* REMOVED *)

  (** <addlink>return</addlink>: Return [void] from method *)
  | return_step_ok : forall h m pc s l sf  m' pc' pc'' l' s',

    instructionAt m pc = Some Return ->
    next m' pc' = Some pc'' -> 
    METHODSIGNATURE.result (METHOD.signature m) = None ->

    step p (St h (Fr m pc s l) ((Fr m' pc' s' l')::sf))
           (St h (Fr m' pc'' s' l') sf)

 (** <addlink>swap</addlink>: Swap the top two operand stack values *)
  | swap_step_ok : forall h m pc pc' s l sf v1 v2,

    instructionAt m pc = Some Swap ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc (v1::v2::s) l) sf) (St h (Fr m pc' (v2::v1::s) l) sf)

  (** <addlink>tableswitch</addlink>: Access jump table by index and jump *)
  | tableswitch_step_ok1 : forall h m pc s l sf i def low high list_offset,

    instructionAt m pc = Some (Tableswitch def low high list_offset) ->
    Z_of_nat (length list_offset) = (high - low + 1)%Z ->
    Int.toZ i < low \/ high < Int.toZ i ->
   
    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m (OFFSET.jump pc def) s l) sf)

  | tableswitch_step_ok2 : forall h m pc s l sf n o i def low high list_offset,

    instructionAt m pc = Some (Tableswitch def low high list_offset) ->
    Z_of_nat (length list_offset) = (high - low + 1)%Z ->
    low <= Int.toZ i <= high ->
    Z_of_nat n = (Int.toZ i) - low ->
    nth_error list_offset n = Some o ->
   
    step p (St h (Fr m pc (Num (I i)::s) l) sf) (St h (Fr m (OFFSET.jump pc o) s l) sf)

 (** Load value from array (<addlink>aaload</addlink>, <addlink>baload</addlink>, 
      <addlink>iaload</addlink>, <addlink>saload</addlink> *)
  | vaload_step_ok : forall h m pc pc' s l sf loc val i length t a k,

    instructionAt m pc = Some (Vaload k) ->
    next m pc = Some pc' ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    0 <= Int.toZ i < Int.toZ length ->
    Heap.get h (Heap.ArrayElement loc (Int.toZ i)) = Some val ->
    compat_ArrayKind_type k t ->
    compat_ArrayKind_value k val ->

    step p (St h (Fr m pc ((Num (I i))::(Ref loc)::s) l) sf) (St h (Fr m pc' (conv_for_stack val::s) l) sf)

  | vaload_step_NullPointerException : forall h m pc s l sf i h' loc k,

    instructionAt m pc = Some (Vaload k) ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc,h') ->

    step p (St h (Fr m pc ((Num (I i))::Null::s) l) sf) 
           (StE h' (FrE m pc loc l) sf)

  | vaload_step_ArrayIndexOutOfBoundsException : forall h m pc s l sf loc i length t a h' loc' k,

    instructionAt m pc = Some (Vaload k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    ~ 0 <= Int.toZ i < Int.toZ length ->
    Heap.new h p (Heap.LocationObject (javaLang,ArrayIndexOutOfBoundsException)) = Some (loc',h') ->

    step p (St h (Fr m pc ((Num (I i))::(Ref loc)::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** Store into array (<addlink>aastore</addlink>, <addlink>bastore</addlink>, 
                       <addlink>iastore</addlink>, <addlink>sastore</addlink> *)
  | vastore_step_ok : forall h m pc pc' s l sf loc val i length tp k a, 

    instructionAt m pc = Some (Vastore k) ->
    next m pc = Some pc' ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    assign_compatible p h val tp ->
    0 <= Int.toZ i < Int.toZ length ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->

    step p (St h (Fr m pc (val::(Num (I i))::(Ref loc)::s) l) sf) 
                                    (St (Heap.update h (Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val tp)) (Fr m pc' s l) sf)

  | vastore_step_NullPointerException : forall h m pc s l sf val i h' loc' k,

    instructionAt m pc = Some (Vastore k) ->
    Heap.new h p (Heap.LocationObject (javaLang,NullPointerException)) = Some (loc',h') ->
    compat_ArrayKind_value k val ->

    step p (St h (Fr m pc (val::(Num (I i))::Null::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

  | vastore_step_ArrayIndexOutOfBoundsException : forall h m pc s l sf loc val i tp a length h' loc' k,

    instructionAt m pc = Some (Vastore k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    ~ 0 <= Int.toZ i < Int.toZ length ->
    Heap.new h p (Heap.LocationObject (javaLang,ArrayIndexOutOfBoundsException)) = Some (loc',h') ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->

    step p (St h (Fr m pc (val::(Num (I i))::(Ref loc)::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

  | vastore_step_ArrayStoreException : forall h m pc s l sf loc val i tp length loc' h' k a,

    instructionAt m pc = Some (Vastore k) ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    ~ assign_compatible p h val tp ->
    0 <= Int.toZ i < Int.toZ length ->
    Heap.new h p (Heap.LocationObject (javaLang,ArrayStoreException)) = Some (loc',h') ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->

    step p (St h (Fr m pc (val::(Num (I i))::(Ref loc)::s) l) sf) 
           (StE h' (FrE m pc loc' l) sf)

 (** Load reference from local variable
         (<addlink>aload</addlink>, <addlink>aload_n</addlink>,
          <addlink>iload</addlink>, <addlink>iload_n</addlink>) *)
  | vload_step_ok : forall h m pc pc' s l sf x val k,

    instructionAt m pc = Some (Vload k x) ->
    next m pc = Some pc' ->
    METHOD.valid_var m x ->
    LocalVar.get l x = Some val ->
    compat_ValKind_value k val -> 

    step p (St h (Fr m pc s l) sf) (St h (Fr m pc' (val::s) l) sf)

 (** Return from method (<addlink>areturn</addlink>, <addlink>ireturn</addlink>) *)
  | vreturn_step_ok : forall h m pc s l sf val t m' pc' pc'' l' s' k,

    instructionAt m pc = Some (Vreturn k) ->
    next m' pc' = Some pc'' -> 
    METHODSIGNATURE.result (METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->

    step p (St h (Fr m pc (val::s) l) ((Fr m' pc' s' l')::sf))
                                                       (St h (Fr m' pc'' (val::s') l') sf)

 (** Store into local variable
     (<addlink>astore</addlink>, <addlink>astore_n</addlink>,
      <addlink>istore</addlink>, <addlink>istore_n</addlink>) *)
  | vstore_step_ok : forall h m pc pc' s l l' sf x v k,

    instructionAt m pc = Some (Vstore k x) ->
    next m pc = Some pc' ->
    METHOD.valid_var m x ->
    l' = LocalVar.update l x v ->
    compat_ValKind_value k v ->

    step p (St h (Fr m pc (v::s) l) sf) (St h (Fr m pc' s l') sf)
.

Inductive step_closure_prefix_sf  (p:Program) : State.t -> State.t -> Prop :=
 | step_closure_prefix_sf_refl : forall st,
    step_closure_prefix_sf p st st
 | step_closure_prefix_sf_step : forall st1 st2 st3,
    step_closure_prefix_sf p st1 st2 -> 
    (exists sf, State.get_sf st3 = List.app sf (State.get_sf st1)) ->
    step p st2 st3 -> 
    step_closure_prefix_sf p st1 st3.

