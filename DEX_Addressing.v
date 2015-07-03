Require Export Annotated.

Import DEX_StaticHandler.DEX_StaticHandler DEX_BigStep.DEX_Dom DEX_Prog.

Module Make (M:MAP).
  Definition address := M.key.
  Variable codes : M.t (DEX_Instruction*(option address*list DEX_ClassName)).
  Variable jump_label : address -> DEX_OFFSET.t -> address.

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
End Make.