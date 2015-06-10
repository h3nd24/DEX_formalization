Require Export LoadBicolano.

Import JVM_Dom.JVM_Prog DEX_Dom.DEX_Prog.

Module MapPC <: MAP with Definition key := JVM_PC := BinNatMap.

Module Type DX_TRANSLATOR_TYPE.

  Parameter Block : Type.
  Parameter SBMap : Type.
  Parameter BlockMap : Type.
  Parameter TSMap : Type.
  Parameter BPMap : Type.
  Parameter bm : JVM_BytecodeMethod.
  Parameter r0 : DEX_Reg.
  (* Parameter translate : JVM_Program -> DEX_Program. *)
  
  (* We zoom in on bytecode translation *)
  Parameter bytecode_translate : DEX_BytecodeMethod.
  Parameter start_block : (BlockMap * SBMap).
  Parameter trace_parent_child : (BlockMap * SBMap) -> (BlockMap * (BPMap * (TSMap * Block))).
  Parameter translate_instructions : (BlockMap * (BPMap * (TSMap * Block))) -> (BlockMap * Block).
  Parameter pick_order : (BlockMap * Block) -> (BlockMap * Block).
  Parameter consolidate_blocks : (BlockMap * Block) -> DEX_BytecodeMethod.

End DX_TRANSLATOR_TYPE.

Module DX_TRANSLATOR <: DX_TRANSLATOR_TYPE.
  Parameter bm : JVM_BytecodeMethod.
  Parameter r0 : DEX_Reg.
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

  Definition insnList := create_insnList (bm).

  Module BLOCK.
    Record t : Type := mkBlock {
      jvm_instructions : list JVM_Instruction;
      parents : list JVM_PC;
      succs : list JVM_PC;
      pSucc : option JVM_PC;
      order : option nat;
      dex_instructions : list DEX_Instruction
    }.
    Definition empty : t :=
      mkBlock (nil) (nil) (nil) (None) (None) (nil).

    Definition append_source_instructions (source:t) (l:list JVM_Instruction) : t :=
      mkBlock (l++source.(jvm_instructions)) (source.(parents)) 
        (source.(succs)) (source.(pSucc)) (source.(order)) (source.(dex_instructions)).

    Definition append_dex_instructions (source:t) (l:list DEX_Instruction) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) 
        (source.(succs)) (source.(pSucc)) (source.(order)) (l++source.(dex_instructions)).

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
      mkBlock (source.(jvm_instructions)) (newParents) 
        (source.(succs)) (source.(pSucc)) (source.(order)) (source.(dex_instructions)).

    Definition append_succs (source:t) (l:list JVM_PC) : t :=
      let newSuccs := append_no_duplicate (l) (source.(succs)) in
      mkBlock (source.(jvm_instructions)) (source.(parents)) 
        (newSuccs) (source.(pSucc)) (source.(order)) (source.(dex_instructions)).

    Definition update_pSucc (source:t) (pSucc:JVM_PC) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) 
        (source.(succs)) (Some pSucc) (source.(order)) (source.(dex_instructions)).

    Definition update_order (source:t) (newOrder:nat) : t :=
      mkBlock (source.(jvm_instructions)) (source.(parents)) 
        (source.(succs)) (source.(pSucc)) (Some newOrder) (source.(dex_instructions)).

   (* 2's complement of -2 *)
   Definition retLabel := Npos (xI (xO (xI (xI (xI (xI (xI (xI 
     (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI (xI 
     (xI (xI (xI (xI (xI (xI (xI xH)
     )))))))))))))))))))))))))))))).
(*   Definition ex := Npos (xI (xO (xO (xO (xO (xO (xO (xO 
     (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))).  *)
  End BLOCK.
  Definition Block := BLOCK.t.

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

        | _ => start_block_rec (t) (start_block_false (pc') (maps)) (* Default for 
          not yet implemented instructions *)
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
          | _ => (n)%nat
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
        | _ => parse_insn_rec (t) (sb) (maps) (* Default for 
          not yet implemented instructions *)
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
        | JVM_Return => BLOCK.mkBlock (nil) (nil) (nil) (None) (None) (DEX_Return::nil)
        | JVM_Vreturn k => BLOCK.mkBlock (nil) (nil) (nil) (None) (None) 
                           (DEX_VReturn (translate_valKind (k)) (r0) ::nil)
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
     (m:BlockMap) (bp:BPMap) (ts:TSMap) (ret:Block)
  := match l with 
       | nil => (m, ret)
       | (pc, (pc',ins)) :: t => 
        let blockIndex := opval (MapPC.get _ bp pc) (0)%N in
        let cb := opval (MapPC.get _ m blockIndex) (BLOCK.empty) in
        let tsValue := get_tsValue (MapPC.get _ ts pc) (ins) in
      match ins with
        | JVM_Const t0 z => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Const (translate_const_type (t0)) (N_toReg (tsValue)) z)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup_x1 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup_x2 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup2 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup2_x1 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue+1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Dup2_x2 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue-3)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue-4)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-3)) (N_toReg (tsValue+1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-4)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Goto o => translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_I2b => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_I2b (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_I2s => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_I2s (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Ibinop op => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ibinop (translate_binop_op (op)) (N_toReg (tsValue)) (N_toReg (tsValue)) (N_toReg (tsValue-1)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_If_icmp cmp o => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ifcmp (translate_comp (cmp)) (N_toReg (tsValue-1)) (N_toReg (tsValue-2)) o)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_If0 cmp o => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ifz (translate_comp (cmp)) (N_toReg (tsValue-1)) o)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Iinc l0 z => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_IbinopConst (DEX_AddInt) (l0) (l0) z)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Ineg => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Ineg (N_toReg (tsValue)) (N_toReg (tsValue)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Lookupswitch d l0 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_SparseSwitch (N_toReg (tsValue-1)) (length l0) (l0))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)


        | JVM_Nop => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Nop)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Pop => translate_instructions_rec (t) (m) (bp) (ts) (ret)
        | JVM_Pop2 => translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Return => translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Swap => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (DEX_Ival) (N_toReg (tsValue+1)) (N_toReg (tsValue-1)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue)) (N_toReg (tsValue-2)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-1)) (N_toReg (tsValue)))::
            (DEX_Move (DEX_Ival) (N_toReg (tsValue-2)) (N_toReg (tsValue+1)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Tableswitch d low high l0 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_PackedSwitch (N_toReg (tsValue-1)) (low) (length l0) (l0))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Vload k l0 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (translate_move_type (k)) (N_toReg (tsValue)) (l0))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Vreturn k => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_VReturn (translate_valKind (k)) (0)%N)::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | JVM_Vstore k l0 => let newM := BLOCK.append_dex_instructions (cb) 
           ((DEX_Move (translate_move_type (k)) (l0) (N_toReg (tsValue-1)))::nil) in
          translate_instructions_rec (t) (m) (bp) (ts) (ret)

        | _ => translate_instructions_rec (t) (m) (bp) (ts) (ret) (* Default for 
          not yet implemented instructions *)
      end
    end.

  Definition translate_instructions (arg:BlockMap * (BPMap * (TSMap * Block))) : (BlockMap * Block) 
  := let m := fst (arg) in
     let bp := fst (snd arg) in
     let ts := fst (snd (snd arg)) in
     let ret := snd (snd (snd arg)) in
     translate_instructions_rec (insnList) (m) (bp) (ts) (ret).

  Definition pick_order (arg:BlockMap * Block) : (BlockMap * Block)
  := (MapN.empty Block, BLOCK.empty).

  Definition consolidate_blocks (arg:BlockMap * Block) : DEX_BytecodeMethod 
  := DEX_BYTECODEMETHOD.Build_t (1)%N 
     (MapN.empty (DEX_Instruction*(option DEX_PC * list DEX_ClassName))) 
     (1) (1) (1).
  
  Definition bytecode_translate : DEX_BytecodeMethod :=
    consolidate_blocks (pick_order (translate_instructions (trace_parent_child (start_block)))).

End DX_TRANSLATOR.