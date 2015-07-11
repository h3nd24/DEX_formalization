(* Require Export JVM_Framework. *)
(* Hendra : To check typability of a DEX program. Contains the intermediate step in translation process *)
Require Export DEX_step.
Require Export DEX_typing_rules.
Require Export cdr.

Import (*JVM_BigStepWithTypes*) DEX_BigStepAnnot.DEX_BigStepAnnot DEX_BigStep.DEX_BigStep DEX_Dom DEX_Prog.
Import Level.L.

Require DEX_step.
Require DEX_typing_rules.

(* Module BinMapN <: MAP with Definition key := N := BinMap. *)

Module Step_final := DEX_step.Make MapN.
Module Typing_final := DEX_typing_rules.Make MapN.

Module Step_int := DEX_step.Make MapAddress.
Module Typing_int := DEX_typing_rules.Make MapAddress.

(*
Definition ValidMethod (p:DEX_Program) (m:DEX_Method) : Prop :=
  exists c, DEX_PROG.defined_Class p c /\ DEX_CLASS.defined_Method c m.

Definition step_final (p:DEX_Program) (*subclass_test*) 
: DEX_Method -> DEX_PC -> option DEX_ClassName -> option DEX_PC -> Prop := fun m pc tau opc =>
  ValidMethod p m /\ exists i, instructionAt m pc = Some i /\ Step_final.DEX_step (*p subclass_test*) m pc i tau opc.
*)

Require check_cdr.
  Module MapKind' := MapOption_Base Map2P(*ClassName*).
  Definition Tag := option DEX_ClassName.
  Module MapKind <: MAP with Definition key := Tag := Map_Of_MapBase MapKind'.
  Module CheckCdr_final := check_cdr.Make MapN(*PC*) MapKind.
  
  Module CheckCdr_int := check_cdr.Make MapAddress MapKind.
  
  Fixpoint map_from_list_final (l:list DEX_PC) : MapN.t bool :=
    match l with
      | nil => MapN.empty _
      | cons i l => MapN.update _ (map_from_list_final l) i true
    end.

  Fixpoint map_from_list_int (l:list (N * N)) : MapAddress.t bool :=
    match l with
      | nil => MapAddress.empty _
      | cons (bi,j) l => MapAddress.update _ (map_from_list_int l) (bi,j) true
    end.


  Definition upd_reg_final : 
    DEX_PC -> Tag -> list DEX_PC -> CheckCdr_final.M.t (MapN.t bool) -> CheckCdr_final.M.t (MapN.t bool) :=
    fun i kd l reg =>
      CheckCdr_final.M.update _ reg (i,kd) (map_from_list_final l).

  Definition upd_reg_int : 
    (N * N) -> Tag -> list (N*N) -> CheckCdr_int.M.t (MapAddress.t bool) 
      -> CheckCdr_int.M.t (MapAddress.t bool) :=
    fun i kd l reg =>
      CheckCdr_int.M.update _ reg (i,kd) (map_from_list_int l).

  Definition empty_reg_final : CheckCdr_final.M.t (MapN.t bool) := CheckCdr_final.M.empty _.
  Definition empty_reg_int : CheckCdr_int.M.t (MapAddress.t bool) := CheckCdr_int.M.empty _.
(*
  Definition upd_jun : 
    DEX_PC -> Tag -> DEX_PC -> MapN.t (MapKind.t CheckCdr.PC) -> MapN.t (MapKind.t CheckCdr.PC) :=
    fun i kd j jun =>     CheckCdr.M.update _ jun (i ,kd) j.

  Definition empty_jun : MapN.t (MapKind.t CheckCdr.PC) := MapN.empty _.
(* There was correctness check here *)

  Section CDR_dummy.

    Variable PC Kind: Set.
    Variable step : PC -> Kind -> option PC -> Prop.

    Definition dummy_cdr : CDR step.
    refine (make_CDR (fun _ _ _ => True) (fun _ _ _ => False) _ _ _ _); auto.
    intuition.
  Qed.

End CDR_dummy.
*)

Section CheckTypable_Final.

  (*Variable p : DEX_ExtendedProgram.*)
  Definition codes_final := MapN.t (DEX_Instruction*(option DEX_PC*list DEX_ClassName)).
  Variable se : (*codes_final -> DEX_sign ->*) DEX_PC -> L.t.
  Variable RT :  (*codes_final -> DEX_sign ->*) DEX_PC -> TypeRegisters.
(*  Variable subclass_test : DEX_ClassName -> DEX_ClassName -> bool. *)
  Variable isStatic : bool.
  Variable static_signature : DEX_sign.
  Variable virtual_signature : L.t -> DEX_sign.
  Variable locR : list DEX_Reg.

  Variable reg : codes_final -> CheckCdr_final.M.t (MapN.t bool).
  (*Variable jun : codes -> MapN.t (MapKind.t CheckCdr.PC).*)

  Definition for_all_region_final : codes_final -> DEX_PC -> DEX_tag -> (DEX_PC->bool) -> bool :=
    fun compiled_code => CheckCdr_final.for_all_region2 (reg compiled_code).

  Definition selift_final compiled_code i (tau:DEX_tag) k :=
    for_all_region_final compiled_code i tau (fun j => L.leql_t k (se j)).

(*
  Definition check_st0 m sgn : bool :=
    match DEX_METHOD.body m with
      | None => false
      | Some bm => match S m sgn (DEX_BYTECODEMETHOD.firstAddress bm) with
                     | nil => true
                     | _ => false
                   end
    end.
*)  

  Definition check_codes_final (compiled_code:codes_final) test :=
    if isStatic then test compiled_code (static_signature)
          else for_all _ (fun k => test compiled_code (virtual_signature k)) L.all
    .
  
  Definition check_final compiled_code : bool := check_codes_final compiled_code
    (fun compiled_code0 sgn =>
      (*(check_st0 m sgn) &&*)
      Step_final.for_all_steps_codes (*p subclass_test*) (DEX_OFFSET.jump)
      (fun i ins tag oj => 
        Typing_final.DEX_tcheck (*p subclass_test*) compiled_code0 (DEX_OFFSET.jump)
          locR sgn (se) (selift_final compiled_code0) (RT) i ins)
      (compiled_code)
    ).

  
(* There was correctness check here *)
End CheckTypable_Final.

Section CheckTypable_Intermediate.

  (*Variable p : DEX_ExtendedProgram.*)
  Definition codes_int := MapAddress.t (DEX_Instruction*(option (N*N)*list DEX_ClassName)).
  Variable se : (*codes_int -> DEX_sign ->*) (N*N) -> L.t.
  Variable RT : (*codes_int -> DEX_sign ->*) (N*N) -> TypeRegisters.
(*  Variable subclass_test : DEX_ClassName -> DEX_ClassName -> bool. *)
  Variable isStatic : bool.
  Variable static_signature : DEX_sign.
  Variable virtual_signature : L.t -> DEX_sign.
  Variable locR : list DEX_Reg.

  Variable reg : (*codes_int -> *)CheckCdr_int.M.t (MapAddress.t bool).
(*  Variable jun : codes -> MapN.t (MapKind.t CheckCdr.PC). *)

  Definition for_all_region_int : (*codes_int -> *)(N*N) -> DEX_tag -> ((N*N)->bool) -> bool :=
    (*fun compiled_code => *)CheckCdr_int.for_all_region2 (reg (*compiled_code*)).

  Definition selift_int (*compiled_code*) i (tau:DEX_tag) k :=
    for_all_region_int (*compiled_code*) i tau (fun j => L.leql_t k (se j)).

(*
  Definition check_st0 m sgn : bool :=
    match DEX_METHOD.body m with
      | None => false
      | Some bm => match S m sgn (DEX_BYTECODEMETHOD.firstAddress bm) with
                     | nil => true
                     | _ => false
                   end
    end.
*)  

  (* Relies on the definition that the target is absolute *)
  Definition jump_address (i:N*N) (o:DEX_OFFSET.t) : (N*N) :=
    (Zabs_N (o), 0%N).

  Definition check_codes_int (compiled_code:codes_int) test :=
    if isStatic then test compiled_code (static_signature)
          else for_all _ (fun k => test compiled_code (virtual_signature k)) L.all
    .
  
  Definition check_int compiled_code : bool := check_codes_int compiled_code
    (fun compiled_code0 sgn =>
      (*(check_st0 m sgn) &&*)
      Step_int.for_all_steps_codes (*p subclass_test*) (jump_address)
      (fun i ins tag oj => 
        Typing_int.DEX_tcheck (*p subclass_test*) compiled_code0 (jump_address)
          locR sgn (se) (selift_int) (RT) i ins)
      (compiled_code)
    ).

  Lemma jump_address_eq : forall i a, jump_address i (Z_of_N a) = (a, (0)%N).
  Proof.
    admit.
  Qed.

  Lemma switch_next_0 : forall (code:DEX_Instruction*(option Step_int.address * list DEX_ClassName))
    ins next_l next l bi j, (ins, next_l) = code ->
    (next, l) = next_l ->
    next = Some (bi, j) -> ~ (eq j 0)%N -> False.
  Proof.
    admit.
  Qed.

  Lemma all_ins_has_next : forall (code:DEX_Instruction*(option Step_int.address * list DEX_ClassName))
    ins next_l next l, 
    code = (ins, next_l) ->
    ~ (ins = DEX_Return \/ exists k r, ins = DEX_VReturn k r) ->
    next_l = (next, l) ->
    next = None -> False.
  Proof.
    admit.
  Qed.

(*
    Lemma for_all_steps_codes_true2 : forall codes
      (test:Step_int.address -> DEX_Instruction -> DEX_tag -> option Step_int.address -> bool), 
      (forall i ins tau oj,
        Step_int.instructionAtAddress codes i = Some ins ->
        Step_int.DEX_step (codes) (jump_address) i ins tau oj -> 
        test i ins tau oj = true) ->
        Step_int.for_all_steps_codes (jump_address) (test) (codes) = true.
    Proof.
      intros.
      (* assert (T2:=Step_int.all_step_in_get_steps _ _ _ _ _ _ H0). *)
      unfold Step_int.for_all_steps_codes.

      (* *)
      destruct codes as (oMbi, tMbi). 
      destruct oMbi. destruct t0. 
      destruct o. destruct p. (*destruct d.*) 
      simpl. apply andb_true_intro. split. admit.
      (* trial *)
        unfold BinMap_Base.fold. unfold fold.
        set (f:= (fun (p0 : BinMap_Base.key)
        (a : prod DEX_Instruction
               (prod (option Step_int.address) (list DEX_ClassName)))
        (b : bool) =>
      andb
        match a return bool with
        | pair ins next =>
            for_all (prod DEX_tag (option Step_int.address))
              (fun tau_oj : prod DEX_tag (option Step_int.address) =>
               match tau_oj return bool with
               | pair tau oj =>
                   test (@pair MapN.key MapN.key N0 (Npos p0)) ins tau oj
               end)
              (Step_int.get_steps jump_address
                 (@pair MapN.key MapN.key N0 (Npos p0)) ins
                 (@fst (option Step_int.address) (list DEX_ClassName) next))
        end b)).
        set (acc:= (fold_rec
        (MapN.t
           (prod DEX_Instruction
              (prod (option Step_int.address) (list DEX_ClassName)))) bool
        (fun (p0 : BinMap_Base.key)
           (a : MapN.t
                  (prod DEX_Instruction
                     (prod (option Step_int.address) (list DEX_ClassName))))
           (b : bool) =>
         MapN.fold
           (prod DEX_Instruction
              (prod (option Step_int.address) (list DEX_ClassName))) bool
           (fun (k2 : MapN.key)
              (a0 : prod DEX_Instruction
                      (prod (option Step_int.address) (list DEX_ClassName))) =>
            andb
              match a0 return bool with
              | pair ins next =>
                  for_all (prod DEX_tag (option Step_int.address))
                    (fun tau_oj : prod DEX_tag (option Step_int.address) =>
                     match tau_oj return bool with
                     | pair tau oj =>
                         test (@pair MapN.key MapN.key (Npos p0) k2) ins tau
                           oj
                     end)
                    (Step_int.get_steps jump_address
                       (@pair MapN.key MapN.key (Npos p0) k2) ins
                       (@fst (option Step_int.address) (list DEX_ClassName)
                          next))
              end) a b) tMbi xH true)).
         assert (forall x, fold_rec 
           (DEX_Instruction * (option Step_int.address * list DEX_ClassName))
           bool f t0 x acc = true).
         (* Proving Assertion *)
           assert (acc = true). admit.
           generalize dependent t0.
           induction t0. auto. 
           destruct a; intros.
           replace (fold_rec (DEX_Instruction * (option Step_int.address * list DEX_ClassName))
              bool f ( node (option (DEX_Instruction * (option Step_int.address * list DEX_ClassName))) 
             (Some p0) t0_1 t0_2) x acc) with 
             (fold_rec (DEX_Instruction * (option Step_int.address * list DEX_ClassName))
              bool f t0_2 (xI x) (f (inv_pos x xH) p0 (fold_rec (DEX_Instruction * (option Step_int.address * list DEX_ClassName))
              bool f t0_1 (xO x) acc))).
           rewrite IHt0_1. 
           assert (f (inv_pos x 1) p0 true = true). admit. 
           rewrite H3. rewrite H2 in IHt0_2. apply IHt0_2 .
           intros. apply H. destruct ins.
           apply H. auto.
               
      apply andb_true_intro; split; 
      try (auto; fail);
      (* Generic solution, will deal for sequential instructions *)
      try (apply H with (i:=(0,0)%N); auto; destruct next eqn:Hnext;
      (* No next instruction *)
      try (apply False_ind; apply all_ins_has_next with (code:=p) (next:=next)
        (next_l:=next_l) (l:=list_exc) (ins:=ins) in Hnext; try (subst; auto; fail); 
        unfold not; intros; inversion H0; rewrite Hins in H1; inversion H1;
        (*rewrite Hins in H1; inversion H1;*) inversion H2; inversion H3; fail);
      (* Has next instruction *)
      try (econstructor; auto; fail)).
      (* end Generic solution *)
         (* *)
         apply H0. 
      (* trial *)     

      induction t0. 
      (* base case t0 *)
         unfold BinMap_Base.fold. unfold fold.
         simpl. 
         set (f:= (fun (p0 : BinMap_Base.key)
        (a : MapN.t
               (prod DEX_Instruction
                  (prod (option Step_int.address) (list DEX_ClassName))))
        (b : bool) =>
      MapN.fold
        (prod DEX_Instruction
           (prod (option Step_int.address) (list DEX_ClassName))) bool
        (fun (k2 : MapN.key)
           (a0 : prod DEX_Instruction
                   (prod (option Step_int.address) (list DEX_ClassName))) =>
         andb
           match a0 return bool with
           | pair ins next =>
               for_all (prod DEX_tag (option Step_int.address))
                 (fun tau_oj : prod DEX_tag (option Step_int.address) =>
                  match tau_oj return bool with
                  | pair tau oj =>
                      test (@pair MapN.key MapN.key (Npos p0) k2) ins tau oj
                  end)
                 (Step_int.get_steps jump_address
                    (@pair MapN.key MapN.key (Npos p0) k2) ins
                    (@fst (option Step_int.address) (list DEX_ClassName) next))
           end) a b)).
         assert (forall x, fold_rec 
           (MapN.t (DEX_Instruction * (option Step_int.address * list DEX_ClassName)))
           bool f tMbi x true = true). 
         (* proving assertion *)
           intros. generalize dependent x. induction tMbi.  auto. 
           destruct a. 
           intros.
           replace (fold_rec (MapN.t (DEX_Instruction * (option Step_int.address * list DEX_ClassName)))
              bool f ( node (option (MapN.t (DEX_Instruction * (option Step_int.address * list DEX_ClassName)))) 
             (Some t0) tMbi1 tMbi2) x true) with 
             (fold_rec (MapN.t (DEX_Instruction * (option Step_int.address * list DEX_ClassName)))
              bool f tMbi2 (xI x) (f (inv_pos x xH) t0 (fold_rec (MapN.t (DEX_Instruction * (option Step_int.address * list DEX_ClassName)))
              bool f tMbi1 (xO x) true))).
           rewrite IHtMbi1. 
           assert (f (inv_pos x 1) t0 true = true). 
           (* proving that f will yield true *)
           clear IHtMbi1 IHtMbi2. 
           unfold f. admit. 
           (* *)
           rewrite H0. apply IHtMbi2. apply H.
           intros.
           replace (fold_rec (node (option A) (None) t1 t2) x true) with 
             (fold_rec t2 (xI x) (fold_rec t1 (xO x) true)).
           rewrite IHt1. apply IHt2. auto.
         (* *) 
         apply H0.
         (* base case tMbi *)
         auto.
         (* induction case tMbi *)
         simpl. destruct a.
           (* current node has instruction *)
           admit.
           (* current node has no instruction *)
           simpl. rewrite -> IHtMbi2.
      
(*
      unfold MapAddress.for_all. simpl.
      unfold MapAddress'.fold.
      unfold MapN.fold. unfold BinNatMap_Base.fold.
      destruct codes as (code0, MapCode0) eqn:Hcodes.
      destruct code0 eqn:Hcode0.
      destruct t0 as (code00, MapCode00)eqn:HMapCode00. 
      destruct code00 eqn:Hcode00.
      apply andb_true_intro. split.
      destruct p as (ins, next_l) eqn:Hp.
      destruct next_l as (next, list_exc) eqn:Hnext_l. 
      unfold for_all.
      unfold fold_right.
(*      assert (T2:=Step_int.all_step_in_get_steps _ _ _ _ _ _). *)
      unfold Step_int.get_steps.
      destruct ins eqn:Hins.    
      apply andb_true_intro; split.
      try (auto; fail);
      (* Generic solution, will deal for sequential instructions *)
      try (apply H with (i:=(0,0)%N); auto; destruct next eqn:Hnext;
      (* No next instruction *)
      try (apply False_ind; apply all_ins_has_next with (code:=p) (next:=next)
        (next_l:=next_l) (l:=list_exc) (ins:=ins) in Hnext; try (subst; auto; fail); 
        unfold not; intros; inversion H0; rewrite Hins in H1; inversion H1;
        (*rewrite Hins in H1; inversion H1;*) inversion H2; inversion H3; fail);
      (* Has next instruction *)
      try (econstructor; auto; fail)).
      (* end Generic solution *)
      destruct a as (bi, j) eqn:Ha.
      destruct (N.eq_dec j 0)%N.
      rewrite e.
      rewrite <- jump_address_eq with (i:=(0,0)%N).
      apply Step_int.DEX_packedSwitch with 
        (codes:=(Some (Some (DEX_PackedSwitch rt firstKey size l, 
                (Some (jump_address (0%N, 0%N) (Z.of_N bi)), list_exc)), MapCode00), MapCode0))
        (jump_label:=jump_address) (i:=(0,0)%N) (rt:=rt)
        (firstKey:=firstKey) (size:=size) (l:=l) (d:=a).
      left. split. 
        unfold Step_int.nextAddress. simpl. rewrite jump_address_eq. rewrite Ha. rewrite e. auto.
        rewrite jump_address_eq. rewrite <- e. apply Ha.
        (* right *) apply False_ind. 
        apply switch_next_0 with (code:=p) (ins:=DEX_PackedSwitch rt firstKey size l) (next_l:=next_l)
        (next:=next) (bi:=bi) (j:=j) (l:=list_exc) in Hnext; try (subst; auto; fail).
      (* switch list target *)
      
      set (l0 := (@map DEX_OFFSET.t (prod DEX_tag (option Step_int.address))
        (fun o : DEX_OFFSET.t =>
         @pair DEX_tag (option Step_int.address) (@None DEX_ClassName)
           (@Some Step_int.address
              (jump_address (@pair MapN.key MapN.key N0 N0) o))) l)
        ) in *. Step_int.address
      (*rewrite <- l0.
      Definition l0 : list DEX_OFFSET.t -> list (option DEX_ClassName * option (N*N))
      := map (fun o : DEX_OFFSET.t => ((None:option DEX_ClassName), Some 
        (jump_address (0%N, 0%N) o))) .*)
      replace  (map (fun o : DEX_OFFSET.t => (None, None)) l)
         with (map (fun o : DEX_OFFSET.t => ((None:DEX_tag), None)) l).
Check l0.

      apply PackedSwitch_successors with (rt:=rt) (firstKey:=firstKey)
        (size:=size) (l:=l) (test:=test) (p:=p)
        (next:=next) (list_exc:=list_exc) (MapCode00:=MapCode00) (MapCode0:=MapCode0).
      auto. auto.
      (* SparseSwitch *)
      destruct a as (bi, j) eqn:Ha.
      destruct (N.eq_dec j 0)%N.
      rewrite e.
      rewrite <- jump_address_eq with (i:=(0,0)%N).
      apply Step_int.DEX_sparseSwitch with 
        (codes:=(Some (Some (DEX_SparseSwitch rt size l, 
                (Some (jump_address (0%N, 0%N) (Z.of_N bi)), list_exc)), MapCode00), MapCode0))
        (jump_label:=jump_address) (i:=(0,0)%N) (rt:=rt)
        (size:=size) (l:=l) (d:=a).
      left. split. 
        unfold Step_int.nextAddress. simpl. rewrite jump_address_eq. rewrite Ha. rewrite e. auto.
        rewrite jump_address_eq. rewrite <- e. apply Ha.
        (* right *) apply False_ind. 
        apply switch_next_0 with (code:=p) (ins:=DEX_SparseSwitch rt size l) (next_l:=next_l)
        (next:=next) (bi:=bi) (j:=j) (l:=list_exc) in Hnext; try (subst; auto; fail).
      (* switch list target *)
        admit.
      (* Ifcmp *)
      apply andb_true_intro. split; try (auto; fail).
      apply H with (i:=(0,0)%N).
      auto. econstructor. auto.
      (* Ifz *) (*Basically the same as Ifcmp *)
      apply andb_true_intro. split; try (auto; fail).
      apply H with (i:=(0,0)%N).
      auto. econstructor. auto.
*) 
    Qed.
*)
(* There was correctness check here *)
End CheckTypable_Intermediate.
