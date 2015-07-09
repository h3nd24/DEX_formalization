Require Export JVM_Final.
Require Export DEX_Final.
Require Export DX_Translator.

Import DX_TRANSLATOR JVM_Dom JVM_Prog DEX_Dom DEX_Prog.

Fixpoint create_insnList_rec (bm:JVM_BytecodeMethod) 
 (ls:list (JVM_PC*(JVM_Instruction*(option JVM_PC*list JVM_ClassName))))
 (l:list (JVM_PC*(option JVM_PC*JVM_Instruction))) 
 : list (JVM_PC*(option JVM_PC*JVM_Instruction)) :=
   match ls with
     | nil => l
     | (pc, (ins,(pc',_))) :: ts => create_insnList_rec (bm) (ts) ((pc,(pc',ins))::l)
   end.

Definition create_insnList (bm:JVM_BytecodeMethod) : list (JVM_PC * (option JVM_PC*JVM_Instruction)) :=
  let pc := JVM_BYTECODEMETHOD.firstAddress bm in
      create_insnList_rec (bm) 
  (MapPC.elements _ (JVM_BYTECODEMETHOD.instr bm)) (nil)
.

Definition translate_se (jvm_se:JVM_PC -> L.t) (translate_pc':(N*N)->JVM_PC) 
  : (N*N) -> L.t :=
  fun address => jvm_se (translate_pc' address).

Definition pc_jvm_int : (MapN.t (list (N*N))) -> JVM_PC -> list (N*N) :=
  (fun map source => match MapN.get _ map source with
                | None => nil
                | Some v => v
              end).

Definition create_int_jvm_map (map:MapN.t (list (N*N))) : MapAddress.t JVM_PC :=
  MapN.fold _ _ 
    (fun key l m => fold_left 
       (fun m' address => MapAddress.update _ m' address key) l m) 
    map (MapAddress.empty JVM_PC).

Definition pc_int_jvm : (MapAddress.t JVM_PC) -> (N*N) -> JVM_PC :=
  (fun map source => match MapAddress.get _ map source with
                | None => (0)%N
                | Some v => v
              end).

Definition static_sign (source:JVM_sign) : DEX_sign :=
  make_DEX_sign (source.(JVM_lvt)) (source.(JVM_resType)) (source.(JVM_heapEffect)).

Definition virtual_sign (source:L.t -> JVM_sign) : L.t -> DEX_sign :=
  (fun k =>
    make_DEX_sign (fun reg => L.Simple L.Low) (Some (L.Simple L.Low)) (L.Low)
  ).

Fixpoint create_locR (max_locals:nat) : list DEX_Reg :=
  match max_locals with
    | O => nil
    | S n => (N_toReg n) :: create_locR (n)
  end.

Definition translate_region (pc_trans:JVM_PC->list (N*N)) : CheckCdr.M.t (MapN.t bool) 
  -> CheckCdr_int.M.t (MapAddress.t bool) :=
  fun sourceMap => CheckCdr.M.fold _ _ 
    (fun key subM newM => 
       CheckCdr_int.M.update _ newM (last (pc_trans (fst key)) (0,0)%N , snd key) 
       (MapN.fold _ _
       (fun subKey b newSubM => 
          fold_left (fun m' key =>
            MapAddress.update _ m' key b)
          (pc_trans subKey) newSubM)
       subM (MapAddress.empty bool))
    )
  sourceMap (CheckCdr_int.M.empty (MapAddress.t bool)).

Fixpoint append_instruction_blocks 
  (m:MapAddress.t (DEX_Instruction * (option (N*N) * list DEX_ClassName)))
  (l:list DEX_Instruction) (address_list:list (N*N))
  : MapAddress.t (DEX_Instruction * (option (N*N) * list DEX_ClassName)) :=
  match l, address_list with 
    | nil, nil => m
    | h :: nil, h' :: nil => MapAddress.update _ m h' (h, (None, nil))
    | h :: t, h' :: t' => let newM := MapAddress.update _ m h' (h, (Some (hd (0,0)%N t'), nil)) in  
                          append_instruction_blocks (newM) (t) (t')
    | _, _ => m (* an impossible case, if the proof ever reach here probably something goes wrong *)
  end.

(* ignore return block for now *)
Definition codes_to_map (compiled_codes:(BlockMap*Block)) (trans_jvm_int:JVM_PC -> list (N*N))
  : codes_int:=
  MapPC.fold _ _ 
    (fun key block newM =>
       append_instruction_blocks newM (BLOCK.dex_instructions block) (trans_jvm_int key)
    )
  (fst compiled_codes) 
  (MapAddress.empty (DEX_Instruction*(option (N*N)*list DEX_ClassName))).

Definition create_RT (m:MapAddress.t TypeRegisters) : (N*N) -> TypeRegisters :=
  (fun key => match MapAddress.get _ m key with
                | None => MapN.empty L.t'
                | Some rt => rt
              end). 

Lemma translation_soundness : forall p m bm insnList
  jvm_static_sign jvm_virtual_sign compiled_program type_result
  jvm_se jvm_S jvm_reg trans_jvm_int trans_int_jvm RT, 
  check p (jvm_se) (jvm_S) (jvm_reg) m = true 
  -> jvm_static_sign = JVM_static_signature p (JVM_METHOD.signature m)
  -> jvm_virtual_sign = JVM_virtual_signature p (JVM_METHOD.signature m)
  -> Some bm = JVM_METHOD.body m
  -> insnList = create_insnList (bm)
  -> (compiled_program, type_result) = translate_instructions (insnList) 
     (trace_parent_child insnList
     (start_block insnList)) (jvm_S)
  -> trans_int_jvm = pc_int_jvm (create_int_jvm_map (snd type_result))
  -> trans_jvm_int = pc_jvm_int (snd type_result)
  -> RT = create_RT (fst type_result)
  -> check_int (translate_se (jvm_se) (trans_int_jvm)) (RT) 
       (JVM_METHOD.isStatic m) (static_sign jvm_static_sign) 
       (virtual_sign jvm_virtual_sign) (create_locR (JVM_BYTECODEMETHOD.max_locals bm)) 
       (translate_region (trans_jvm_int) jvm_reg) (codes_to_map compiled_program trans_jvm_int)
       = true.
  Proof.
    intros. unfold check_int. unfold check in H.
    destruct (JVM_METHOD.isStatic m) eqn:method_static.
    (* The method is static *)
      unfold check_codes_int.
      apply for_all_steps_codes_true2.
      intros. 
      unfold Step_int.for_all_steps_codes.
      unfold MapAddress.for_all.
      unfold MapAddress'.fold. unfold MapN.fold. unfold BinNatMap_Base.fold.
      destruct (codes_to_map compiled_codes trans_jvm_int) as (v,m0) eqn:Hcodes.
      destruct v eqn:Hv.
      destruct t eqn:Ht.
      destruct o eqn:Ho.
      apply andb_true_intro. split. 
      (* 1st branch *)
        destruct p0 as (ins, next0) eqn:Hp0.
        unfold for_all. 
        unfold fold_right.
        unfold Step_int.get_steps.
        apply for_all_steps_m_true in H.
        
        destruct ins eqn:Hins.
        apply andb_true_intro. split. 
          
          admit. reflexivity.
        destruct (Step_int.get_steps jump_address (0%N, 0%N) ins (fst next0)).
        
        
      
      apply Step_int.for_all_steps_codes_true with (codes := codes_to_map compiled_codes trans_jvm_int)
      (jump_label := jump_address) (test :=(fun (i : Step_int.address)
     (ins : DEX_BigStep.DEX_Dom.DEX_Prog.DEX_Instruction) (_ : DEX_tag)
     (_ : option Step_int.address) =>
   Typing_int.DEX_tcheck (codes_to_map compiled_codes trans_jvm_int)
     jump_address (create_locR (JVM_BYTECODEMETHOD.max_locals bm0))
     (static_sign jvm_static_sign) (translate_se jvm_se trans_int_jvm)
     (selift_int (translate_se jvm_se trans_int_jvm)
        (translate_region trans_jvm_int jvm_reg)) RT i ins)).
  Qed.