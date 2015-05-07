(* <Insert License Here>

    $Id: SmallStep.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

  Import Dom Prog.

  (** Small step semantics for the instruction set of the JVM *)
  Inductive step (p:Program) : State.t -> State.t -> Prop :=
  | nop_step_ok : forall h m pc pc' l sf,

    instructionAt m pc = Some Nop ->
    next m pc = Some pc' ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l) sf)

  | const_step_ok : forall h m pc pc' l l' sf k rt v,

    instructionAt m pc = Some (Const k rt v) ->
    next m pc = Some pc' ->
    -2^31 <= v < 2^31 ->
    METHOD.valid_var m rt ->
    l' = LocalVar.update l rt (Some (Num (I (Int.const v)))) ->
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)
  
  | move_step_ok : forall h m pc pc' l l' sf k rt rs v,

    instructionAt m pc = Some (Move k rt rs) ->
    next m pc = Some pc' ->
    v = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt v ->
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)
  
  | moveresult_step_ok : forall h m pc pc' l l' sf k rt v,

    instructionAt m pc = Some (MoveResult k rt) ->
    next m pc = Some pc' ->
    METHOD.valid_var m rt ->
    v = LocalVar.get l LocalVar.ret ->
    l' = LocalVar.update l rt v ->
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  | return_step_ok : forall h m pc l sf  m' pc' pc'' l',

    instructionAt m pc = Some Return ->
    next m' pc' = Some pc'' -> 
    METHODSIGNATURE.result (METHOD.signature m) = None ->

    step p (St h (Fr m pc l) ((Fr m' pc' l')::sf))
           (St h (Fr m' pc'' l') sf)

  | vreturn_step_ok : forall h m pc l sf val t m' pc' pc'' l' k rs l'',
    (* Implicit in the assumption is that the register has a value in it *)
    instructionAt m pc = Some (VReturn k rs) ->
    next m' pc' = Some pc'' -> 
    METHODSIGNATURE.result (METHOD.signature m) = Some t ->
    assign_compatible p h val t ->
    compat_ValKind_value k val ->
    Some val = LocalVar.get l rs ->
    METHOD.valid_var m rs ->
    l'' = LocalVar.update l' LocalVar.ret (Some val) ->

    step p (St h (Fr m pc l) ((Fr m' pc' l')::sf))
           (St h (Fr m' pc'' l'') sf)

 (** <addlink>instanceof</addlink>: Determine if object is of given type *)
  | instanceof_step_ok1 : forall h m pc pc' l sf loc rt r t l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l r ->
    assign_compatible p h (Ref loc) (ReferenceType t) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l' rt (Some (Num (I (Int.const 1)))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)
 (** <addlink>instanceof</addlink>: with object == null *)
  | instanceof_step_ok2 : forall h m pc pc' l sf rt r t v l',

    instructionAt m pc = Some (InstanceOf rt r t) ->
    next m pc = Some pc' ->
    Some v = LocalVar.get l r ->
    isReference v ->
    (~ assign_compatible p h v (ReferenceType t) \/ v=Null) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l' rt (Some (Num (I (Int.const 0)))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf) 
  
  (** <addlink>arraylength</addlink>: Get length of array *)
  | arraylength_step_ok : forall h m pc pc' l l' sf loc length tp a rt rs,

    instructionAt m pc = Some (ArrayLength rt rs)->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l rs ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Some (Num (I length))) ->
    
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  (** <addlink>new</addlink>: Create new object *)
  | new_step_ok : forall h m pc pc' l l' sf c loc h' rt,

    instructionAt m pc = Some (New rt (ClassType c)) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationObject c) = Some (pair loc h') ->
    METHOD.valid_var m rt ->
    l' = LocalVar.update l rt (Some (Ref loc)) ->

    step p (St h (Fr m pc l) sf) (St h' (Fr m pc' l) sf)

 (** Create new array (<addlink>anewarray</addlink>, <addlink>newarray</addlink>) *)
 (** OutOfMemory is not considered in Bicolano *)
  | newarray_step_ok : forall h m pc pc' l l' sf i t loc h_new rt rl,

    instructionAt m pc = Some (NewArray rt rl t) ->
    next m pc = Some pc' ->
    Heap.new h p (Heap.LocationArray i t (m,pc)) = Some (pair loc h_new) ->
    Some (Num (I i)) = LocalVar.get l rl ->
    0 <= Int.toZ i ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rl ->
    l' = LocalVar.update l rt (Some (Ref loc)) ->

    step p (St h (Fr m pc l) sf) (St h_new (Fr m pc' l) sf)

  | goto_step_ok : forall h m pc l sf o,

    instructionAt m pc = Some (Goto o) ->
    step p (St h (Fr m pc l) sf) (St h (Fr m (OFFSET.jump pc o) l) sf)
  
  | packedswitch_step_ok1 : forall h m pc l sf v r firstKey size list_offset n o,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = LocalVar.get l r ->
    firstKey <= Int.toZ v < firstKey + size ->
    Z_of_nat (length list_offset) = size ->
    Z_of_nat n = (Int.toZ v) - firstKey ->
    nth_error list_offset n = Some o ->
    METHOD.valid_var m r ->    

    step p (St h (Fr m pc l) sf) (St h (Fr m (OFFSET.jump pc o) l) sf)

  | packedswitch_step_ok2 : forall h m pc pc' l sf v r firstKey size list_offset,
    
    instructionAt m pc = Some (PackedSwitch r firstKey size list_offset) ->
    Some (Num (I v)) = LocalVar.get l r ->
    Z_of_nat (length list_offset) = size ->
    Int.toZ v < firstKey \/ firstKey + size <= Int.toZ v ->
    next m pc = Some pc' ->
    METHOD.valid_var m r ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l) sf)
  
  | sparseswitch_step_ok1 : forall h m pc l sf v v' o r size listkey,
    
    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = LocalVar.get l r ->
    List.In (pair v' o) listkey ->
    v' = Int.toZ v ->
    METHOD.valid_var m r ->
    
    step p (St h (Fr m pc l) sf) (St h (Fr m (OFFSET.jump pc o) l) sf)

  | sparseswitch_step_ok2 : forall h m pc pc' l sf v r size listkey,

    instructionAt m pc = Some (SparseSwitch r size listkey) ->
    Z_of_nat (length listkey) = size ->
    Some (Num (I v)) = LocalVar.get l r ->
    (forall v' o, List.In (pair v' o) listkey ->  v' <> Int.toZ v) ->
    next m pc = Some pc' ->
    METHOD.valid_var m r ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l) sf) 

  | ifcmp_step_jump : forall h m pc l sf va vb cmp ra rb o,

    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->    

    step p (St h (Fr m pc l) sf) (St h (Fr m (OFFSET.jump pc o) l) sf)

  | ifcmp_step_continue : forall h m pc pc' l sf va vb cmp ra rb o,
    
    instructionAt m pc = Some (Ifcmp cmp ra rb o) ->
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    ~SemCompInt cmp (Int.toZ va) (Int.toZ vb) ->
    next m pc = Some pc' ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l) sf)

  | ifz_step_jump : forall h m pc l sf v cmp r o,

    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = LocalVar.get l r ->
    SemCompInt cmp (Int.toZ v) (0) ->
    METHOD.valid_var m r ->    

    step p (St h (Fr m pc l) sf) (St h (Fr m (OFFSET.jump pc o) l) sf)

  | ifz_step_continue : forall h m pc pc' l sf v cmp r o,
    
    instructionAt m pc = Some (Ifz cmp r o) ->
    Some (Num (I v)) = LocalVar.get l r ->
    ~SemCompInt cmp (Int.toZ v) (0) ->
    next m pc = Some pc' ->
    METHOD.valid_var m r ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l) sf)
   (** Load value from array *)
  | aget_step_ok : forall h m pc pc' l l' sf loc val i length t a k rt ra ri,

    instructionAt m pc = Some (Aget k rt ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ra ->
    Heap.typeof h loc = Some (Heap.LocationArray length t a) ->
    compat_ArrayKind_type k t ->
    Some (Num (I i)) = LocalVar.get l ri ->
    0 <= Int.toZ i < Int.toZ length ->
    Heap.get h (Heap.ArrayElement loc (Int.toZ i)) = Some val ->
    compat_ArrayKind_value k val ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m ri ->
    l' = LocalVar.update l rt (Some (conv_for_stack val)) -> 

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  (** Store into array *)
  | aput_step_ok : forall h m pc pc' l sf loc val i length tp k a rs ra ri, 

    instructionAt m pc = Some (Aput k rs ra ri) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ra ->
    Heap.typeof h loc = Some (Heap.LocationArray length tp a) ->
    Some val = LocalVar.get l rs ->
    assign_compatible p h val tp ->
    Some (Num (I i)) = LocalVar.get l ri ->
    0 <= Int.toZ i < Int.toZ length ->
    compat_ArrayKind_type k tp ->
    compat_ArrayKind_value k val ->
    METHOD.valid_var m rs ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m ri ->

    step p (St h (Fr m pc l) sf) 
           (St (Heap.update h (Heap.ArrayElement loc (Int.toZ i)) (conv_for_array val tp)) (Fr m pc' l) sf)

  (** <addlink>iget</addlink>: Fetch field from object *)
  | iget_step_ok : forall h m pc pc' l l' sf loc f v cn k rt ro,

    instructionAt m pc = Some (Iget k rt ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ro ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Heap.get h (Heap.DynamicField loc f) = Some v ->    
    METHOD.valid_var m rt ->
    METHOD.valid_var m ro ->
    l' = LocalVar.update l rt (Some v) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)
  
  (** <addlink>iput</addlink>: Set field in object *)
  | iput_step_ok : forall h m pc pc' l sf f loc cn v k rs ro,

    instructionAt m pc = Some (Iput k rs ro f) ->
    next m pc = Some pc' ->
    Some (Ref loc) = LocalVar.get l ro ->
    Heap.typeof h loc = Some (Heap.LocationObject cn) -> 
    defined_field p cn f ->
    Some v = LocalVar.get l rs ->
    assign_compatible p h v (FIELDSIGNATURE.type (snd f)) ->
    METHOD.valid_var m rs ->
    METHOD.valid_var m ro ->

    step p (St h (Fr m pc l) sf)
           (St (Heap.update h (Heap.DynamicField loc f) v) (Fr m pc' l) sf)

  (** <addlink>invokestatic</addlink>: Invoke a class ([static]) method *)
  | invokestatic_step_ok : forall h m pc l sf mid n M args bM fnew,

    instructionAt m pc = Some (Invokestatic mid n args) ->
    findMethod p mid = Some M ->
    METHOD.isNative M = false ->
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    METHOD.body M = Some bM ->
    fnew = (Fr M
               (BYTECODEMETHOD.firstAddress bM)
               (listvar2localvar args)) ->
 
    step p (St h (Fr m pc l) sf) (St h fnew ((Fr m pc l)::sf))


  (** <addlink>invokeinterface</addlink>: Invoke interface method *)
  (** <addlink>invokedirect</addlink>: Invoke instance method *)
  (** <addlink>invokesuper</addlink>: special handling for superclass, private, and instance initialization method invocations *)
  (** <addlink>invokevirtual</addlink>: Invoke instance method; dispatch based on class *)
  | invokevirtual_step_ok : forall h m pc l sf n mid M args loc bM fnew,

    instructionAt m pc = Some (Invokevirtual mid n args) ->
    (* lookup p cn mid (pair cl M) -> *)
    findMethod p mid = Some M ->
    Heap.typeof h loc = Some (Heap.LocationObject (fst mid)) -> (* cn is obtained from the method signature *)
    length args = length (METHODSIGNATURE.parameters (snd mid)) ->
    METHOD.body M = Some bM ->
    fnew = (Fr M
               (BYTECODEMETHOD.firstAddress bM)
               (listvar2localvar args)) ->
 
    step p (St h (Fr m pc l) sf) (St h fnew ((Fr m pc l)::sf))
  (* TODO : Invokesuper *)
  (* TODO : Invokedirect *)
  (* TODO : Invokestatic *)
  (* TODO : Invokeinterface *)

  (** <addlink>ineg</addlink>: Negate [int] *)
  | ineg_step : forall h m pc l l' sf pc' rt rs v,

    instructionAt m pc = Some (Ineg rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Some (Num (I (Int.neg v)))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  (** <addlink>ineg</addlink>: Not [int] (one's complement) *)
  | inot_step : forall h m pc l l' sf pc' rt rs v,

    instructionAt m pc = Some (Inot rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Some (Num (I (Int.not v)))) ->
    
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  (** <addlink>i2b</addlink>: Convert [int] to [byte] *)
  | i2b_step_ok : forall h m pc pc' l l' sf rt rs v,

    instructionAt m pc = Some (I2b rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Some (Num (I (b2i (i2b v))))) ->
    
    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

 (** <addlink>i2s</addlink>: Convert [int] to [short] *)
  | i2s_step_ok : forall h m pc pc' l l' sf rt rs v,

    instructionAt m pc = Some (I2s rt rs) ->
    next m pc = Some pc' ->
    Some (Num (I v)) = LocalVar.get l rs ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m rs ->
    l' = LocalVar.update l rt (Some (Num (I (s2i (i2s v))))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf)

  | ibinop_step_ok : forall h m pc pc' l l' sf op rt ra rb va vb,

    instructionAt m pc = Some (Ibinop op rt ra rb) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = LocalVar.get l ra ->
    Some (Num (I vb)) = LocalVar.get l rb ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m ra ->
    METHOD.valid_var m rb ->
    l' = LocalVar.update l rt (Some (Num (I (SemBinopInt op va vb)))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf) 

  | ibinopconst_step_ok : forall h m pc pc' l l' sf op rt r va v,

    instructionAt m pc = Some (IbinopConst op rt r v) ->
    next m pc = Some pc' ->
    (*(op = DivInt \/ op = RemInt -> ~ Int.toZ i2 = 0) -> at this moment there is no exception*)
    Some (Num (I va)) = LocalVar.get l r ->
    METHOD.valid_var m rt ->
    METHOD.valid_var m r ->
    l' = LocalVar.update l rt (Some (Num (I (SemBinopInt op va (Int.const v))))) ->

    step p (St h (Fr m pc l) sf) (St h (Fr m pc' l') sf) 
.

Inductive step_closure_prefix_sf  (p:Program) : State.t -> State.t -> Prop :=
 | step_closure_prefix_sf_refl : forall st,
    step_closure_prefix_sf p st st
 | step_closure_prefix_sf_step : forall st1 st2 st3,
    step_closure_prefix_sf p st1 st2 -> 
    (exists sf, State.get_sf st3 = List.app sf (State.get_sf st1)) ->
    step p st2 st3 -> 
    step_closure_prefix_sf p st1 st3.
