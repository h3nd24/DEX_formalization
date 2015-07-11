(* Require Export JVM_Framework. *)
(* Hendra : Used for method typability *)
Require Export JVM_step.
Require Export JVM_typing_rules.
Require Export cdr.

Import (*JVM_BigStepWithTypes*) JVM_BigStepAnnot.JVM_BigStepAnnot JVM_BigStep.JVM_BigStep JVM_Dom JVM_Prog.
Import Level.L.

(*
Definition ValidMethod (p:JVM_Program) (m:JVM_Method) : Prop :=
  exists c, JVM_PROG.defined_Class p c /\ JVM_CLASS.defined_Method c m.
*)

Definition step (p:JVM_Program) (*subclass_test*) : JVM_Method -> JVM_PC -> option JVM_ClassName -> option JVM_PC -> Prop := fun m pc tau opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ JVM_step (*p subclass_test*) m pc i tau opc.

Require check_cdr.
Module MapKind' := MapOption_Base Map2P(*ClassName*).
  Definition Tag := option JVM_ClassName.
  Module MapKind <: MAP with Definition key := Tag := Map_Of_MapBase MapKind'.
  Module CheckCdr := check_cdr.Make MapN(*PC*) MapKind.

  Fixpoint map_from_list (l:list JVM_PC) : MapN.t bool :=
    match l with
      | nil => MapN.empty _
      | cons i l => MapN.update _ (map_from_list l) i true
    end.

  Definition upd_reg : 
    JVM_PC -> Tag -> list JVM_PC -> CheckCdr.M.t (MapN.t bool) -> CheckCdr.M.t (MapN.t bool) :=
    fun i kd l reg =>
      CheckCdr.M.update _ reg (i,kd) (map_from_list l).

  Definition empty_reg : CheckCdr.M.t (MapN.t bool) := CheckCdr.M.empty _.

  Definition upd_jun : 
    JVM_PC -> Tag -> JVM_PC -> MapN.t (MapKind.t CheckCdr.PC) -> MapN.t (MapKind.t CheckCdr.PC) :=
    fun i kd j jun =>     CheckCdr.M.update _ jun (i ,kd) j.

  Definition empty_jun : MapN.t (MapKind.t CheckCdr.PC) := MapN.empty _.
(* There was correctness check here *)
(*
  Section CDR_dummy.

    Variable PC Kind: Set.
    Variable step : PC -> Kind -> option PC -> Prop.

    Definition dummy_cdr : CDR step.
    refine (make_CDR (fun _ _ _ => True) (fun _ _ _ => False) _ _ _ _); auto.
    intuition.
  Qed.

End CDR_dummy.
*)

Section CheckTypable.

  Variable p : JVM_ExtendedProgram.
  Variable se : (*JVM_Method -> JVM_sign ->*) JVM_PC -> L.t.
  Variable S :  (*JVM_Method -> JVM_sign ->*) JVM_PC -> list L.t'.
(*  Variable subclass_test : JVM_ClassName -> JVM_ClassName -> bool. *)

  Variable reg : (*JVM_Method -> *)CheckCdr.M.t (MapN.t bool).
(*  Variable jun : JVM_Method -> MapN.t (MapKind.t CheckCdr.PC).*)

  Definition stacktype : Set := TypeStack.

  Definition for_all_region : (*JVM_Method -> *)JVM_PC -> JVM_tag -> (JVM_PC->bool) -> bool :=
    (*fun m => *) CheckCdr.for_all_region2 (reg).

  Definition selift (*m sgn*) i (tau:JVM_tag) k :=
    for_all_region (*m*) i tau (fun j => L.leql_t k (se (*m sgn*) j)).

  Definition check_st0 m (*sgn*) : bool :=
    match JVM_METHOD.body m with
      | None => false
      | Some bm => match S (*m sgn*) (JVM_BYTECODEMETHOD.firstAddress bm) with
                     | nil => true
                     | _ => false
                   end
    end.
  
  Definition check_m m test :=
    if JVM_METHOD.isStatic m then test m (JVM_static_signature p (JVM_METHOD.signature m))
          else for_all _ (fun k => test m (JVM_virtual_signature p (JVM_METHOD.signature m) k)) L.all
    .
  
  Definition check m : bool := check_m m 
    (fun m sgn =>
      (check_st0 m (*sgn*)) &&
      for_all_steps_m (*p subclass_test*) m
      (fun i ins tag oj => 
        JVM_tcheck (*p subclass_test*) m sgn (se (*m sgn*)) (selift (*m sgn*)) (S (*m sgn*)) i ins)
    ).

  
(* There was correctness check here *)
End CheckTypable.
