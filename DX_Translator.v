Require Export LoadBicolano.
Require Export EquivDec.
Require Export Annotated.

Import JVM_Dom.JVM_Prog DEX_Dom.DEX_Prog.

Module MapPC <: MAP with Definition key := JVM_PC := BinNatMap.

Module Type DX_TRANSLATOR_TYPE.

  Parameter Block : Type.
  Parameter SBMap : Type.
  Parameter BlockMap : Type.
  Parameter TSMap : Type.
  Parameter BPMap : Type.
(*  Parameter bm : JVM_BytecodeMethod.
  Parameter insnList : list (JVM_PC * (option JVM_PC*JVM_Instruction)). *)
  (* Parameter translate : JVM_Program -> DEX_Program. *)
  
  (* We zoom in on bytecode translation *)
(*
  Parameter bytecode_translate : list (JVM_PC * (option JVM_PC*JVM_Instruction)) -> DEX_BytecodeMethod.
*)
  Parameter start_block : list (JVM_PC * (option JVM_PC*JVM_Instruction)) -> (BlockMap * SBMap).
  Parameter trace_parent_child : list (JVM_PC * (option JVM_PC*JVM_Instruction)) -> (BlockMap * SBMap) 
                                 -> (BlockMap * (BPMap * (TSMap * Block))).
  Parameter translate_instructions : list (JVM_PC * (option JVM_PC*JVM_Instruction)) 
                                     -> (BlockMap * (BPMap * (TSMap * Block))) 
                                     -> (JVM_PC -> TypeStack)
                                     -> ((BlockMap * Block) * (MapAddress.t TypeRegisters * MapN.t (list (N*N)))).
(*
  Parameter pick_order : (BlockMap * Block) -> (list JVM_PC * (BlockMap * Block)).
  Parameter consolidate_blocks : (list JVM_PC * (BlockMap * Block)) -> list (DEX_Instruction*(DEX_PC*DEX_PC)).
  Parameter construct_bytecodemethod : list (DEX_Instruction*(DEX_PC*DEX_PC))
                                       -> MapPC.t (DEX_Instruction*(option DEX_PC * list DEX_ClassName))
                                       -> DEX_BytecodeMethod.
*)

End DX_TRANSLATOR_TYPE.

Module DX_TRANSLATOR <: DX_TRANSLATOR_TYPE.
  Module BLOCK.
    Record t : Type := mkBlock {
      jvm_instructions : list JVM_Instruction;
      parents : list JVM_PC;
      succs : list JVM_PC;
      pSucc : option JVM_PC;
      order : option nat;
      dex_instructions : list DEX_Instruction;
      dex_label : option DEX_PC
    }.
    Definition empty : t :=
      mkBlock (nil) (nil) (nil) (None) (None) (nil) (None).

    Definition append_source_instructions (source:t) (l:list JVM_Instruction) : t :=
      mkBlock (l++source.(jvm_instructions)) (source.(parents)) (source.(succs)) 
        (source.(pSucc)) (source.(order)) (source.(dex_instructions)) (source.(dex_label)).

    Definition append_dex_instructions (source:t) (l:list DEX_Instruction) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) (source.(succs)) 
        (source.(pSucc)) (source.(order)) (l++source.(dex_instructions)) (source.(dex_label)).

   Lemma PC_eq_dec : forall x y : JVM_PC, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

    Fixpoint append_no_duplicate (l source:list JVM_PC) : list JVM_PC :=
      match l with
        | nil => (source)
        | h :: t => if in_dec PC_eq_dec (h) (source) then
                      append_no_duplicate (t) (source)
                    else 
                      append_no_duplicate (t) (h :: source)
      end.

    Definition append_parents (source:t) (l:list JVM_PC) : t :=
      let newParents := append_no_duplicate (l) (source.(parents)) in
      mkBlock (source.(jvm_instructions)) (newParents) (source.(succs)) 
        (source.(pSucc)) (source.(order)) (source.(dex_instructions)) (source.(dex_label)).

    Definition append_succs (source:t) (l:list JVM_PC) : t :=
      let newSuccs := append_no_duplicate (l) (source.(succs)) in
      mkBlock (source.(jvm_instructions)) (source.(parents)) (newSuccs) 
        (source.(pSucc)) (source.(order)) (source.(dex_instructions)) (source.(dex_label)).

    Definition update_pSucc (source:t) (pSucc:JVM_PC) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) (source.(succs)) 
        (Some pSucc) (source.(order)) (source.(dex_instructions)) (source.(dex_label)).

    Definition update_order (source:t) (newOrder:nat) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) (source.(succs)) 
        (source.(pSucc)) (Some newOrder) (source.(dex_instructions)) (source.(dex_label)).

    Definition update_dex_label (source:t) (newLabel:DEX_PC) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) (source.(succs)) 
        (source.(pSucc)) (source.(order)) (source.(dex_instructions)) (Some newLabel).

   (* 2's complement of -2 *)
   Definition retLabel := Npos (xI (xO (xI (xI (xI (xI (xI (xI 
     (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI 
     (xI (xI (xI (xI (xI (xI (xI xH)
     )))))))))))))))))))))))))))))).
(*   Definition ex := Npos (xI (xO (xO (xO (xO (xO (xO (xO 
     (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))).  *)
  End BLOCK.
  Definition Block := BLOCK.t.

  Section BytecodeMethod_Translator.
  Parameter bm : JVM_BytecodeMethod.
  Definition max_locals := JVM_BYTECODEMETHOD.max_locals bm.
  Parameter sgn : JVM_sign. 

(*
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
      (MapPC.elements _ (JVM_BYTECODEMETHOD.instr bm)) (nil).
*)
  Variable insnList : list (JVM_PC * (option JVM_PC*JVM_Instruction)).
  
(*  Definition insnList := create_insnList (bm). *)

  Definition SBMap := MapPC.t bool.
  Definition BlockMap := MapPC.t Block.
  Definition TSMap := MapPC.t nat.
  Definition BPMap := MapPC.t JVM_PC.

  Definition start_block_true (pc:option JVM_PC) (maps:(BlockMap*SBMap)) : (BlockMap*SBMap) :=
    match pc with
      | None => maps
      | Some pc' =>
          let newM := BinNatMap.update _ (fst (maps)) (pc') BLOCK.empty in
          let newSb := BinNatMap.update _ (snd (maps)) (pc') (true) in
            (newM, newSb)
    end.

  Definition start_block_false (pc:option JVM_PC) (maps:(BlockMap*SBMap)) : (BlockMap*SBMap) :=
    match pc with
      | None => maps
      | Some pc' =>
          let newSb := BinNatMap.update _ (snd (maps)) (pc') (false) in
            (fst (maps), newSb)
    end.

  Fixpoint start_block_true_offset_list (l:list JVM_OFFSET.t) (pc:JVM_PC) (maps:(BlockMap*SBMap)) : (BlockMap*SBMap) :=
    match l with
      | nil => maps
      | o :: t =>
          let newM := BinNatMap.update _ (fst (maps)) (JVM_OFFSET.jump pc o) BLOCK.empty in
          let newSb := BinNatMap.update _ (snd (maps)) (JVM_OFFSET.jump pc o) (true) in
            start_block_true_offset_list (t) (pc) (newM, newSb)
    end.

(* Assumption :
  1. There is no dead code, so the instruction after a goto or a return
     will be pointed to by some other instruction 
*)
  Fixpoint start_block_rec (l:list (JVM_PC*(option JVM_PC*JVM_Instruction))) (maps:(BlockMap * SBMap))
      : (BlockMap * SBMap) :=
    match l with
      | nil => maps
      | (pc, (pc',ins)) :: t => 
      match ins with
(*
        | JVM_Aconst_null => start_block_rec (t) (maps) 
        | JVM_Arraylength => start_block_rec (t) (update_start_block (pc') (maps)) 
*)
        | JVM_Const _ _ => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup_x1 => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup_x2 => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup2 => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup2_x1 => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Dup2_x2 => start_block_rec (t) (start_block_false (pc') (maps))
(*
        | JVM_Getfield _ => start_block_rec (t) (start_block_true (pc') (maps)) 
*)
        | JVM_Goto o => start_block_rec (t) (start_block_true (Some (JVM_OFFSET.jump pc o)) (maps))
        | JVM_I2b => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_I2s => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Ibinop _ => start_block_rec (t) (start_block_false (pc') (maps))
(*
        | JVM_If_acmp _ o => start_block_rec (t) 
             (update_start_block (Some (JVM_OFFSET.jump pc o))
              (update_start_block (pc') (maps)) )
*)
        | JVM_If_icmp _ o => start_block_rec (t) 
             (start_block_true (Some (JVM_OFFSET.jump pc o))
              (start_block_true (pc') (maps)) )
        | JVM_If0 _ o => start_block_rec (t) 
             (start_block_true (Some (JVM_OFFSET.jump pc o))
              (start_block_true (pc') (maps)) )
(*
        | JVM_Ifnull _ o => start_block_rec (t) 
             (update_start_block (Some (JVM_OFFSET.jump pc o))
              (update_start_block (pc') (maps)) )
*)
        | JVM_Iinc _ _ => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Ineg => start_block_rec (t) (start_block_false (pc') (maps))
(*
        | JVM_Instanceof _ => start_block_rec (t) (maps)
        | JVM_Invokeinterface _ => start_block_rec (t) (update_start_block (pc') (maps))
        | JVM_Invokespecial _ => start_block_rec (t) (update_start_block (pc') (maps))
        | JVM_Invokestatic _ => start_block_rec (t) (update_start_block (pc') (maps))
        | JVM_Invokevirtual _ => start_block_rec (t) (update_start_block (pc') (maps))
*)
        | JVM_Lookupswitch d l => start_block_rec (t)
              (start_block_true (Some (JVM_OFFSET.jump pc d))
               (start_block_true_offset_list 
               (map (fun a => snd a) l) (pc) (maps)) )
(*
        | JVM_New _ => start_block_rec (t) (update_start_block (pc') (maps))
        | JVM_Newarray _ => start_block_rec (t) (update_start_block (pc') (maps))
*)
        | JVM_Nop => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Pop => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Pop2 => start_block_rec (t) (start_block_false (pc') (maps))
(*
        | JVM_Putfield _ => start_block_rec (t) (update_start_block (pc') (maps))
*)
        | JVM_Return => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Swap => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Tableswitch d _ _ l => start_block_rec (t)
              (start_block_true (Some (JVM_OFFSET.jump pc d))
               (start_block_true_offset_list (l) (pc) (maps)))
(*
        | JVM_Vaload _ => start_block_rec (t) (update_start_block (pc') (maps))
        | JVM_Vastore _ => start_block_rec (t) (update_start_block (pc') (maps))
*)
        | JVM_Vload _ _ => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Vreturn _ => start_block_rec (t) (start_block_false (pc') (maps))
        | JVM_Vstore _ _ => start_block_rec (t) (start_block_false (pc') (maps))

(*
        | _ => start_block_rec (t) (start_block_false (pc') (maps)) (* Default for 
          not yet implemented instructions *)
*)
      end
    end.

  Definition start_block : (BlockMap * SBMap) :=
    start_block_rec (insnList) (MapPC.empty Block, MapPC.empty bool).
 
  Definition opval (A: Type) (v:option A) (default:A) : A :=
    match v with
      | None => default
      | Some val => val
    end.
  Implicit Arguments opval.
(* Implicit in the assumption that one step instruction will always has a successor *)
  Definition one_step_instructions (pc:JVM_PC) (pc':option JVM_PC) (sb:SBMap) (m:BlockMap) (bp:BPMap) (ts:TSMap) 
      (ret:Block) (tsValue:nat) :=
    let succPC := opval (pc') (pc) in
    let blockIndex := if opval (MapPC.get _ sb pc) (false) then
      pc else opval (MapPC.get _ bp pc) (pc) in
    let newTS := MapPC.update _ ts succPC tsValue in
    if opval (MapPC.get _ sb pc) (false) then
       let cb := opval (MapPC.get _ m pc) (BLOCK.empty) in
       let cb' := BLOCK.update_pSucc (cb) (succPC) in
       let cb'' := BLOCK.append_succs (cb') (succPC::nil) in
       let succb := opval (MapPC.get _ m succPC) (BLOCK.empty) in
       let succb' := BLOCK.append_parents (succb) (blockIndex::nil) in
       let newBP := MapPC.update _ bp succPC succPC in
       let newM := MapPC.update _ (MapPC.update _ m blockIndex 
                   cb'') succPC succb' in
       (newM, (newBP, (newTS, ret)))
    else
       let newBP := MapPC.update _ bp succPC blockIndex in
       (m, (newBP, (newTS, ret)))
  .

  Definition jump_instructions (pc:JVM_PC) (l:list JVM_PC) (sb:SBMap) 
      (m:BlockMap) (bp:BPMap) (ts:TSMap) (ret:Block) (tsValue:nat) :=
    match l with 
      | nil => (m, (bp, (ts, ret)))
      | pc' :: t =>
          let blockIndex := if opval (MapPC.get _ sb pc) (false) then
              pc else opval (MapPC.get _ bp pc) (pc) in
          let cb := opval (MapPC.get _ m pc) (BLOCK.empty) in
          let cb' := BLOCK.update_pSucc (cb) (pc') in
          let cb'' := BLOCK.append_succs (cb') (l) in
          let succb := opval (MapPC.get _ m pc') (BLOCK.empty) in
          let succb' := BLOCK.append_parents (succb) (blockIndex::nil) in
          let newBP := MapPC.update _ bp pc' pc' in
          let newM := MapPC.update _ (MapPC.update _ m blockIndex 
                      cb'') pc' succb' in
          (newM, (newBP, (ts, ret)))
     end
  . 

  Definition return_instructions (pc:JVM_PC) (sb:SBMap) (m:BlockMap) (bp:BPMap) (ts:TSMap) (ret:Block) :=
    let blockIndex := if opval (MapPC.get _ sb pc) (false) then
        pc else opval (MapPC.get _ bp pc) (pc) in
    let cb := opval (MapPC.get _ m pc) (BLOCK.empty) in
    let cb' := BLOCK.update_pSucc (cb) (BLOCK.retLabel) in
    let cb'' := BLOCK.append_succs (cb') (BLOCK.retLabel::nil) in
    let newRet := BLOCK.append_parents (ret) (blockIndex::nil) in
    let newM := MapPC.update _ m blockIndex cb'' in
    (newM, (bp, (ts, newRet)))
    . 

  Definition get_tsValue (val:option nat) (ins:JVM_Instruction) : nat :=
    match val with
      | None => (0)%nat (* it shouldn't be the case that the mapping returns a None*)
      | Some n =>
        match ins with
          | JVM_Const _ _ => (n + 1)%nat
          | JVM_Dup => (n+1)%nat
          | JVM_Dup_x1 => (n+1)%nat
          | JVM_Dup_x2 => (n+1)%nat
          | JVM_Dup2 => (n+2)%nat
          | JVM_Dup2_x1 => (n+2)%nat
          | JVM_Dup2_x2 => (n+2)%nat
          | JVM_Goto _ => (n)%nat
          | JVM_I2b => (n)%nat
          | JVM_I2s => (n)%nat
          | JVM_Ibinop _ => (n-1)%nat
          | JVM_If_icmp _ _ => (n-2)%nat
          | JVM_If0 _ _ => (n-1)%nat
          | JVM_Iinc _ _ => (n)%nat
          | JVM_Ineg => (n)%nat
          | JVM_Lookupswitch _ _ => (n-1)%nat
          | JVM_Nop => (n)%nat
          | JVM_Pop => (n-1)%nat
          | JVM_Pop2 => (n-2)%nat
          | JVM_Return => (n)%nat
          | JVM_Swap => (n)%nat
          | JVM_Tableswitch _ _ _ _ => (n-1)%nat
          | JVM_Vload _ _ => (n+1)%nat
          | JVM_Vreturn _ => (n-1)%nat
          | JVM_Vstore _ _ => (n-1)%nat
(*          | _ => (n)%nat *)
        end
    end.


(* adding a default value may break proofs, have to check *)
  Fixpoint parse_insn_rec (l:list (JVM_PC*(option JVM_PC*JVM_Instruction)))
      (sb:SBMap)
      (maps:BlockMap * (BPMap * (TSMap * Block))) :=
    match l with 
      | nil => maps
      | (pc, (pc',ins)) :: t => 
        let m := (fst maps) in
        let bp := (fst (snd maps)) in
        let ts := (fst (snd (snd maps))) in
        let ret := (snd (snd (snd (maps)))) in
        let tsValue := get_tsValue (MapPC.get _ ts pc) (ins) in
      match ins with
        | JVM_Const _ _ => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup_x1 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup_x2 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup2 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup2_x1 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Dup2_x2 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Goto o => parse_insn_rec (t) (sb) (jump_instructions (pc) (JVM_OFFSET.jump pc o::nil)
             (sb) (m) (bp) (ts) (ret) (tsValue))
        | JVM_I2b => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_I2s => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Ibinop _ => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_If_icmp _ o => parse_insn_rec (t) (sb)
             (jump_instructions (pc) (cons_option (pc') (JVM_OFFSET.jump pc o::nil)) (sb) (m) (bp) (ts) (ret) (tsValue))
        | JVM_If0 _ o => parse_insn_rec (t) (sb) 
             (jump_instructions (pc) (cons_option (pc') (JVM_OFFSET.jump pc o::nil)) (sb) (m) (bp) (ts) (ret) (tsValue))
        | JVM_Iinc _ _ => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Ineg => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Lookupswitch d l => parse_insn_rec (t) (sb) 
             (jump_instructions (pc) (JVM_OFFSET.jump pc d::(map (fun a => JVM_OFFSET.jump pc (snd a)) l)) (sb) (m) (bp) (ts) (ret) (tsValue))
        | JVM_Nop => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Pop => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Pop2 => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Return => parse_insn_rec (t) (sb) (return_instructions (pc) (sb)
             (m) (bp) (ts) (ret))
        | JVM_Swap => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Tableswitch d _ _ l => parse_insn_rec (t) (sb) 
             (jump_instructions (pc) (JVM_OFFSET.jump pc d::(map (fun o => JVM_OFFSET.jump pc o) l)) (sb) (m) (bp) (ts) (ret) (tsValue))
        | JVM_Vload _ _ => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
        | JVM_Vreturn _ => parse_insn_rec (t) (sb) (return_instructions (pc) (sb) 
             (m) (bp) (ts) (ret))
        | JVM_Vstore _ _ => parse_insn_rec (t) (sb) (one_step_instructions (pc) (pc') (sb) 
             (m) (bp) (ts) (ret) (tsValue))
(*        | _ => parse_insn_rec (t) (sb) (maps) (* Default for 
          not yet implemented instructions *) *)
      end
    end.

  Definition translate_valKind (k:JVM_ValKind) : DEX_ValKind :=
    match k with
      | JVM_Aval => DEX_Aval
      | JVM_Ival => DEX_Ival
    end.

  Fixpoint create_retBlock (l:list (JVM_PC*(option JVM_PC*JVM_Instruction))) : Block := 
    match l with 
      | nil => BLOCK.empty (* impossible case *)
      | (pc, (pc',ins)) :: t => 
      match ins with
        | JVM_Return => BLOCK.mkBlock (nil) (nil) (nil) (None) (None) (DEX_Return::nil) (None) 
        | JVM_Vreturn k => BLOCK.mkBlock (nil) (nil) (nil) (None) (None) 
                           (DEX_VReturn (translate_valKind (k)) (0)%N ::nil) (None)
        | _ => create_retBlock t
      end
    end.

  Definition trace_parent_child (mSb:BlockMap * SBMap) 
     : BlockMap * (BPMap * (TSMap * Block))
  := let firstPC := JVM_BYTECODEMETHOD.firstAddress bm in
     let initialTS := MapPC.update _ (MapPC.empty nat) (firstPC) (0)%nat in
     let initialBP := MapPC.update _ (MapPC.empty JVM_PC) (firstPC) (firstPC) in
     let retBlock := create_retBlock insnList in
     parse_insn_rec (insnList) (snd (mSb)) (fst (mSb), (initialBP, (initialTS, retBlock))).

  Definition translate_const_type (t0:JVM_primitiveType) : DEX_ValKind :=
    DEX_Ival.

 Definition translate_move_type (t0:JVM_ValKind) : DEX_ValKind :=
    match t0 with JVM_Ival => DEX_Ival | JVM_Aval => DEX_Aval end.

  Definition translate_binop_op (op:JVM_BinopInt) : DEX_BinopInt :=
    match op with
      | JVM_AddInt => DEX_AddInt 
      | JVM_AndInt => DEX_AndInt
      | JVM_DivInt => DEX_DivInt
      | JVM_MulInt => DEX_MulInt
      | JVM_OrInt => DEX_OrInt
      | JVM_RemInt => DEX_RemInt
      | JVM_ShlInt => DEX_ShlInt
      | JVM_ShrInt => DEX_ShrInt
      | JVM_SubInt => DEX_SubInt
      | JVM_UshrInt => DEX_UshrInt
      | JVM_XorInt => DEX_XorInt
    end.

  Definition translate_comp (cmp:JVM_CompInt) : DEX_CompInt :=
    match cmp with
      | JVM_EqInt => DEX_EqInt 
      | JVM_NeInt => DEX_NeInt
      | JVM_LtInt => DEX_LtInt
      | JVM_LeInt => DEX_LeInt
      | JVM_GtInt => DEX_GtInt
      | JVM_GeInt => DEX_GeInt
    end.

  Fixpoint translate_instructions_rec (l:list (JVM_PC*(option JVM_PC*JVM_Instruction)))
     (m:BlockMap) (bp:BPMap) (ts:TSMap) (ret:Block) (S:JVM_PC -> TypeStack) 
     (RT:MapAddress.t TypeRegisters) (pcMapping:MapN.t (list (N*N)))
  : ((BlockMap * Block) * (MapAddress.t TypeRegisters * MapN.t (list (N*N))))
  := match l with 
       | nil => ((m, ret), (RT, pcMapping))
       | (pc, (pc',ins)) :: t => 
        let blockIndex := opval (MapPC.get _ bp pc) (0)%N in
        let cb := opval (MapPC.get _ m blockIndex) (BLOCK.empty) in
        let tsValue := get_tsValue (MapPC.get _ ts pc) (ins) in
      match ins with
        | JVM_Const t0 z => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Const (translate_const_type (t0)) (N_toReg (tsValue)) z)::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Dup => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Dup_x1 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue-1)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
(*
          let ts0 := opval (MapN.get _ rt2 (N_toReg (tsValue))) (L.Simple L.bot) in
          let rt3 := MapN.update _ rt2 (N_toReg (tsValue-2)) (ts0) in
          let RT3 := MapAddress.update _ (RT2) (pc, (j+3)%N) (rt3) in
*)
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) 
            ((pc, j)::(pc,(j+1)%N)::(pc,(j+2)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT2) (pcMapping')

        | JVM_Dup_x2 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue-1)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
          let tsm3 := opval (MapN.get _ rt2 (N_toReg (tsValue-3))) (L.Simple L.bot) in
          let rt3 := MapN.update _ rt2 (N_toReg (tsValue-2)) (tsm3) in
          let RT3 := MapAddress.update _ (RT2) (pc, (j+3)%N) (rt3) in
(*
          let ts0 := opval (MapN.get _ rt2 (N_toReg (tsValue))) (L.Simple L.bot) in
          let rt4 := MapN.update _ rt3 (N_toReg (tsValue-3)) (ts0) in
          let RT4 := MapAddress.update _ (RT3) (pc, (j+4)%N) (rt4) in
*)
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) 
            ((pc, j)::(pc,(j+1)%N)::(pc,(j+2)%N)::(pc,(j+3)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT3) (pcMapping')

        | JVM_Dup2 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue+1)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
(*
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
*)
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::(pc,(j+1)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT1) (pcMapping')

        | JVM_Dup2_x1 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue+1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue+1)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
          let tsm3 := opval (MapN.get _ rt2 (N_toReg (tsValue-3))) (L.Simple L.bot) in
          let rt3 := MapN.update _ rt2 (N_toReg (tsValue-1)) (tsm3) in
          let RT3 := MapAddress.update _ (RT2) (pc, (j+3)%N) (rt3) in
          let tsp1 := opval (MapN.get _ rt2 (N_toReg (tsValue+1))) (L.Simple L.bot) in
          let rt4 := MapN.update _ rt3 (N_toReg (tsValue-2)) (tsp1) in
          let RT4 := MapAddress.update _ (RT3) (pc, (j+4)%N) (rt4) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) 
            ((pc, j)::(pc,(j+1)%N)::(pc,(j+2)%N)::(pc,(j+3)%N)::(pc,(j+4)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT4) (pcMapping')

        | JVM_Dup2_x2 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue-4)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue+1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-4)) (N_toReg (tsValue)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue+1)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
          let tsm3 := opval (MapN.get _ rt2 (N_toReg (tsValue-3))) (L.Simple L.bot) in
          let rt3 := MapN.update _ rt2 (N_toReg (tsValue-1)) (tsm3) in
          let RT3 := MapAddress.update _ (RT2) (pc, (j+3)%N) (rt3) in
          let tsm4 := opval (MapN.get _ rt2 (N_toReg (tsValue-4))) (L.Simple L.bot) in
          let rt4 := MapN.update _ rt3 (N_toReg (tsValue-2)) (tsm4) in
          let RT4 := MapAddress.update _ (RT3) (pc, (j+4)%N) (rt4) in
          let tsp1 := opval (MapN.get _ rt2 (N_toReg (tsValue+1))) (L.Simple L.bot) in
          let rt5 := MapN.update _ rt3 (N_toReg (tsValue-3)) (tsp1) in
          let RT5 := MapAddress.update _ (RT3) (pc, (j+5)%N) (rt5) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) 
            ((pc, j)::(pc,(j+1)%N)::(pc,(j+2)%N)::(pc,(j+3)%N)::(pc,(j+4)%N)::(pc,(j+5)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT5) (pcMapping')

        | JVM_Goto o => translate_instructions_rec (t) (m) (bp) (ts) (ret) (S) (RT) (pcMapping)

        | JVM_I2b =>
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_I2b (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_I2s => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_I2s (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')
 
        | JVM_Ibinop op => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ibinop (translate_binop_op (op)) (N_toReg (tsValue)) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_If_icmp cmp o => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ifcmp (translate_comp (cmp)) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)) 
           (Z_of_N (DEX_OFFSET.jump pc o)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_If0 cmp o => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ifz (translate_comp (cmp)) (N_toReg (tsValue-1)) 
           (Z_of_N (DEX_OFFSET.jump pc o)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Iinc l0 z => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_IbinopConst (DEX_AddInt) (l0) (l0) z)::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Ineg => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ineg (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Lookupswitch d l0 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_SparseSwitch (N_toReg (tsValue-1)) (length l0) 
           (map (fun e => ((fst e), Z_of_N (DEX_OFFSET.jump pc (snd e)))) l0))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Nop => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Nop)::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Pop => translate_instructions_rec (t) (m) (bp) (ts) (ret) (S) (RT) (pcMapping)
        | JVM_Pop2 => translate_instructions_rec (t) (m) (bp) (ts) (ret) (S) (RT) (pcMapping)

        | JVM_Return => translate_instructions_rec (t) (m) (bp) (ts) (ret) (S) (RT) (pcMapping)

        | JVM_Swap => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue+1)))::nil) in
          let tsm1 := opval (MapN.get _ rt (N_toReg (tsValue-1))) (L.Simple L.bot) in
          let rt1 := MapN.update _ rt (N_toReg (tsValue+1)) (tsm1) in
          let RT1 := MapAddress.update _ (RT') (pc, (j+1)%N) (rt1) in
          let tsm2 := opval (MapN.get _ rt1 (N_toReg (tsValue-2))) (L.Simple L.bot) in
          let rt2 := MapN.update _ rt1 (N_toReg (tsValue)) (tsm2) in
          let RT2 := MapAddress.update _ (RT1) (pc, (j+2)%N) (rt2) in
          let ts0 := opval (MapN.get _ rt2 (N_toReg (tsValue))) (L.Simple L.bot) in
          let rt3 := MapN.update _ rt2 (N_toReg (tsValue-1)) (ts0) in
          let RT3 := MapAddress.update _ (RT2) (pc, (j+3)%N) (rt3) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) 
            ((pc, j)::(pc,(j+1)%N)::(pc,(j+2)%N)::(pc,(j+3)%N)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT3) (pcMapping')

        | JVM_Tableswitch d low high l0 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_PackedSwitch (N_toReg (tsValue-1)) (low) (length l0) 
           (map (fun o => Z_of_N (DEX_OFFSET.jump pc o)) l0))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Vload k l0 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (translate_move_type (k)) (N_toReg (tsValue)) (l0))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Vreturn k => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_VReturn (translate_valKind (k)) (0)%N)::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

        | JVM_Vstore k l0 => 
          let j := N.of_nat (length (BLOCK.dex_instructions cb)) in
          let rt := translate_st_rt (S pc) (max_locals) (sgn.(JVM_lvt)) in
          let RT' := MapAddress.update _ (RT) (pc, j) (rt) in
          let newBlock := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (translate_move_type (k)) (l0) (N_toReg (tsValue-1)))::nil) in
          let newM := MapPC.update _ m blockIndex newBlock in
          let pcMapping' := MapN.update _ pcMapping (pc) ((pc, j)::nil) in
          translate_instructions_rec (t) (newM) (bp) (ts) (ret) (S) (RT') (pcMapping')

(* 
        | _ => translate_instructions_rec (t) (m) (bp) (ts) (ret) (* Default for 
          not yet implemented instructions *) *)
      end
    end.

  Definition translate_instructions (arg:BlockMap * (BPMap * (TSMap * Block))) 
  (S:JVM_PC -> TypeStack) 
  : ((BlockMap * Block) * (MapAddress.t TypeRegisters * MapN.t (list (N*N)))) 
  := let m := fst (arg) in
     let bp := fst (snd arg) in
     let ts := fst (snd (snd arg)) in
     let ret := snd (snd (snd arg)) in
     translate_instructions_rec (insnList) (m) (bp) (ts) (ret) (S) 
      (MapAddress.empty TypeRegisters) (MapN.empty (list (N*N))).
(*
   Lemma Label_eq_dec : forall x y : JVM_PC, {x=y} + {x<>y}.
   Proof.
    repeat decide equality.
   Qed.

  Definition beq_order (x y:option nat) : bool :=
    match x with
      | None => match y with None => true | _ => false end
      | Some v => match y with Some v => true | _ => false end
    end.

  Definition beq_pc (x y:option JVM_PC) : bool:=
    match x with
      | None => match y with None => true | _ => false end
      | Some v => match y with Some v => true | _ => false end
    end.

  Fixpoint find_parent (x:JVM_PC) (parents:list JVM_PC) (loop:list JVM_PC) 
    (m:BlockMap) : (JVM_PC * bool) :=
  match parents with
    | nil => (x, false)
    | h :: t =>
        let parentBlock := MapPC.get _ m h in
        if in_dec (Label_eq_dec) (h) (loop) then
          (x, false)
        else 
          if (beq_order (BLOCK.order (opval parentBlock BLOCK.empty)) None) &&
             (beq_pc (BLOCK.pSucc (opval parentBlock BLOCK.empty)) (Some x)) 
          then
              (h, true)
          else
            find_parent (x) (t) (loop) (m)
  end.


  Fixpoint pick_starting_point (x:JVM_PC) (loop:list JVM_PC) (m:BlockMap) (bound:nat) 
    {struct bound} : JVM_PC :=
  match bound with
    | O => x
    | S n => 
        let cb := MapPC.get _ m x in
        let (y, b) := find_parent (x) (BLOCK.parents (opval cb BLOCK.empty)) (loop) (m) in
        if b then
          pick_starting_point (y) (y::loop) (m) (n)
        else
          x
  end.

  Fixpoint find_available_successor (x:JVM_PC) (succs:list JVM_PC) (m:BlockMap) (ret:Block) 
    : (JVM_PC * bool) :=
  match succs with
    | nil => (x, false)
    | h :: t =>
          let isSuccRet := beq_pc (Some h) (Some BLOCK.retLabel) in
          let succ := if isSuccRet then ret else (opval (MapPC.get _ m h) BLOCK.empty) in
          if beq_order (BLOCK.order succ) (None) then
             (h, true)
          else
             find_available_successor (x) (t) (m) (ret) 
  end.

  Definition find_successor (x:JVM_PC) (xb:Block) (succs:list JVM_PC) (m:BlockMap) (ret:Block) : (JVM_PC * bool) :=
    let pSuccLabel := (BLOCK.pSucc xb) in
    if beq_pc (pSuccLabel) (None) then
      find_available_successor (x) (succs) (m) (ret)
    else
      let pSuccBlock := if beq_pc pSuccLabel (Some BLOCK.retLabel) then
                           ret else opval (MapPC.get _ m (opval pSuccLabel (0)%N)) (BLOCK.empty) in
      if beq_order (BLOCK.order pSuccBlock) None then
         ((opval pSuccLabel (0)%N), true)
      else 
         find_available_successor (x) (succs) (m) (ret).
    
  Fixpoint trace_successors (x:JVM_PC) (order:nat) (m:BlockMap) (ret:Block) 
    (sortedPC:list JVM_PC) (bound:nat) : (nat * (list JVM_PC * (BlockMap * Block))) :=
  match bound with
    | O => (order, (sortedPC, (m, ret)))
    | S n =>
        let isReturn := beq_pc (Some x) (Some BLOCK.retLabel) in
        let b := if isReturn then ret else opval (MapPC.get _ m x) (BLOCK.empty) in
        let newM := if isReturn then m else MapPC.update _ m x (BLOCK.update_order b order) in
        let newRet := if isReturn then BLOCK.update_order ret order else ret in
        let newSortedPC := x :: sortedPC in
        let (lbl, found) := find_successor (x) (b) (BLOCK.succs b) (m) (ret) in
          if found then 
            trace_successors (x) (S order) (newM) (newRet) (newSortedPC) (n)
          else (S order, (newSortedPC, (newM, newRet)))
  end.
 
  Fixpoint pick_order_rec (l:list JVM_PC) (order:nat) (arg:BlockMap * Block) 
      (sortedPC:list JVM_PC) : (list JVM_PC * (BlockMap * Block)):=
    match l with
      | nil => (sortedPC, arg)
      | h :: t => 
          let source := pick_starting_point (h) (h::nil) (fst arg) (length l) in
          let (newOrder, newSnd) := trace_successors (source) (order) (fst arg) (snd arg) (sortedPC) (length l) in
          let (newSortedPC, newSnd') := newSnd in
          let (newM, newRet) := newSnd' in
            pick_order_rec (t) (newOrder) (newM, newRet) (newSortedPC)
    end.

(* the correct behavior is when the list is sorted, at the moment
   I don't see how sorted-ness will affect the proof. The crucial 
   part where it should start with block 0 is assumed with all the
   previous step, and further enforced by adding the first address 
   to the head of the list *)
  Definition pick_order (arg:BlockMap * Block) : (list JVM_PC * (BlockMap * Block))
  := 
     (*let block0 := MapPC.get _ (fst arg) (BYTECODEMETHOD.firstAddress bm) in
     let newM := MapPC.update _ (fst arg) (BYTECODEMETHOD.firstAddress bm) 
         (Block.updateOrder (block0) (Some 0)) in*)
     pick_order_rec ((JVM_BYTECODEMETHOD.firstAddress bm)::MapPC.dom _ (fst arg)) (0%nat) (arg) (nil).
   
  Definition opposite_cmp (cmp:DEX_CompInt) : DEX_CompInt :=
    match cmp with
      | DEX_EqInt => DEX_NeInt
      | DEX_NeInt => DEX_EqInt
      | DEX_LtInt => DEX_GeInt
      | DEX_LeInt => DEX_GtInt
      | DEX_GtInt => DEX_LeInt
      | DEX_GeInt => DEX_LtInt
    end.

  Fixpoint add_instructions (lst:list DEX_Instruction) (succs:list DEX_PC) (pSucc:DEX_PC)
  (dex_label:DEX_PC) (needsGoto : bool) (output : list (DEX_PC * DEX_Instruction))
  : list (DEX_PC * DEX_Instruction) :=
    match lst with
      | nil => 
        let gotoIns := if needsGoto then nil else 
            (dex_label,
            DEX_Goto (Z_of_N (pSucc)))::nil in
          output ++ gotoIns
      | h :: nil =>
             if needsGoto then  
                match h with 
                  | DEX_Ifcmp cmp ra rb o => 
                      match succs with
                        | s :: pSucc :: t =>
                           output ++ (dex_label, DEX_Ifcmp (opposite_cmp cmp) ra rb o)::nil
                        | _ => let lastIns := (dex_label, h)::
                           ((dex_label + 1)%N,
                           DEX_Goto (Z_of_N (pSucc)))::nil in
                              output ++ lastIns
                      end
                  | DEX_Ifz cmp r o =>
                       match succs with
                        | s :: pSucc :: t =>
                           output ++ (dex_label, DEX_Ifz (opposite_cmp cmp) r o)::nil
                        | _ => let lastIns := (dex_label, h)::
                           ((dex_label + 1)%N,
                           DEX_Goto (Z_of_N (pSucc)))::nil in
                              output ++ lastIns
                       end
                  | _ => (output ++ (dex_label, h) :: nil)
                end 
             else (output ++ (dex_label, h) :: nil)
      | h :: t => add_instructions (t) (succs) (pSucc) (dex_label + 1)%N (needsGoto) (output ++ (dex_label, h) :: nil)
    end.
  
  Fixpoint output_blocks (lst : list JVM_PC) (m:BlockMap) (ret:Block) (dex_label:DEX_PC) 
    (output:list (DEX_PC*DEX_Instruction))
  : (list (DEX_PC*DEX_Instruction) * (BlockMap * Block)) :=
    match lst with
      | nil => (output, (m, ret)) 
      | h :: t =>
          let isReturn := beq_pc (Some h) (Some BLOCK.retLabel) in
          let cb := if isReturn then ret else 
                      opval (MapPC.get _ m h) BLOCK.empty in
          let needsGoto := match (BLOCK.pSucc cb) with
                             | None => false
                             | Some x => 
                             match t with 
                               | x :: t' => false
                               | _ => true
                             end
                           end in
          let currentContent := add_instructions (BLOCK.dex_instructions cb) 
                                (BLOCK.succs cb) (opval (BLOCK.pSucc cb) (0)%N) 
                                (dex_label) (needsGoto) (nil) in
          let newOutput := output ++ currentContent in
          let newBlock := BLOCK.update_dex_label cb dex_label in
          let newRet := if isReturn then newBlock else ret in
          let newM := if isReturn then m else
                        MapPC.update _ m h (newBlock) in
            output_blocks (t) (newM) (newRet) 
             (Nplus (dex_label) (N_of_nat (length currentContent))) 
             (newOutput)
    end.
(* TODO fix into pair *)
  Fixpoint fix_target (lst : list (DEX_PC*DEX_Instruction))
  (m:BlockMap) (ret:Block) (result:list (DEX_Instruction*(DEX_PC*DEX_PC))) 
  : (list (DEX_Instruction*(DEX_PC*DEX_PC))) :=
    match lst with 
      | nil => result
      | (pc,ins) :: t => 
        match ins with 
          | DEX_Goto o => 
                let isReturn := beq_pc (Some pc) (Some BLOCK.retLabel) in
                let succBlock := if isReturn then ret else
                                   (opval (MapPC.get _ m (N_of_Z o)) BLOCK.empty) in
                let succLabel := opval (BLOCK.dex_label succBlock) (0)%N in
                let newIns := DEX_Goto (Z_of_N (succLabel) - Z_of_N (pc))%Z in
                  fix_target (t) (m) (ret) ((newIns,(pc,succLabel))::result)
          | DEX_Ifcmp cmp ra rb o => 
                let isReturn := beq_pc (Some pc) (Some BLOCK.retLabel) in
                let succBlock := if isReturn then ret else
                                   (opval (MapPC.get _ m (N_of_Z o)) BLOCK.empty) in
                let succLabel := opval (BLOCK.dex_label succBlock) (0)%N in
                let newIns := DEX_Ifcmp cmp ra rb (Z_of_N (succLabel) - Z_of_N (pc))%Z in
                  fix_target (t) (m) (ret) ((newIns,(pc,(pc+1)%N))::result)
          | DEX_Ifz cmp r o => 
                let isReturn := beq_pc (Some pc) (Some BLOCK.retLabel) in
                let succBlock := if isReturn then ret else
                                   (opval (MapPC.get _ m (N_of_Z o)) BLOCK.empty) in
                let succLabel := opval (BLOCK.dex_label succBlock) (0)%N in
                let newIns := DEX_Ifz cmp r (Z_of_N (succLabel) - Z_of_N (pc))%Z in
                  fix_target (t) (m) (ret) ((newIns,(pc,(pc+1)%N))::result)
          | _ => fix_target (t) (m) (ret) ((ins,(pc, (pc+1)%N))::result)
        end
    end.

  Definition consolidate_blocks (arg:list JVM_PC * (BlockMap * Block)) 
  : list (DEX_Instruction*(DEX_PC*DEX_PC)) := 
    let lst := fst arg in
    let m := fst (snd arg) in
    let ret := snd (snd arg) in
    let (insnList, sndRet) :=  output_blocks (lst) (m) (ret) (0)%N (nil) in
    let (newM, newRet) := sndRet in
      fix_target (insnList) (newM) (newRet) (nil).


  Fixpoint construct_bytecodemethod (lst:list (DEX_Instruction*(DEX_PC*DEX_PC)) ) 
  (bc:MapPC.t (DEX_Instruction*(option DEX_PC * list DEX_ClassName))) 
  : DEX_BytecodeMethod :=
    match lst with
      | nil => DEX_BYTECODEMETHOD.Build_t (1)%N (bc) (1) (1) (1)   
      | (ins, (pc, pc')) :: t => 
             construct_bytecodemethod (t) (DEX_bc_cons (pc) ins (pc') bc)
    end.

  Definition bytecode_translate : DEX_BytecodeMethod :=
    construct_bytecodemethod 
      (consolidate_blocks (pick_order (translate_instructions 
      (trace_parent_child (start_block))))) (DEX_bc_empty).
*)
  End BytecodeMethod_Translator. 
(*
  Section Translate_se.
    Parameter Translate_PC : JVM_PC -> DEX_PC.
  End Translate_se.
*)
 
End DX_TRANSLATOR.