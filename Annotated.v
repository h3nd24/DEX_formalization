(** * Annotated.v: Syntax of JVM program extended with security type annotations *)
Require Export LoadBicolano.
Require Export Level.
Require Export Axioms.

Import BigStep.BigStep.Dom.Prog.


Record sign : Set := make_sign {
  lvt : Var -> L.t';
  resType : option L.t';
  (* DEX resExceptionType : ClassName -> L.t;*)
  heapEffect : L.t
}.

Definition default_signature : sign :=
  make_sign
    (fun _ => L.Simple L.bot)
    None
    (* DEX (fun _ => L.bot) *)
    L.bot.    


Record ExtendedProgram : Type := extP {
  prog :> Program;
  newArT : Method * PC -> L.t';
  static_signature : ShortMethodSignature -> sign;
  virtual_signature : ShortMethodSignature -> L.t -> sign;
  ft : FieldSignature -> L.t';
  locR : ShortMethodSignature -> list Var
}.

(* DEX
Definition throwableBy (p:Program) := PROG.throwableBy p.
*)

(*
Definition static_signature (p:ExtendedProgram) mid : sign :=
  match MapShortMethSign.get _ p.(signatures) mid with
    | Some sgn => sgn
    | None => default_signature
  end.

Definition  virtual_signature (p:ExtendedProgram) mid (k:L.t) : sign :=
  static_signature p mid.
*)

(* DEX
Definition well_formed_lookupswitch m := forall pc def l i o1 o2,
  instructionAt m pc = Some (Lookupswitch def l) ->
  In (i, o1) l -> In (i, o2) l -> o1=o2.
*)

(* DEX
Definition np := (javaLang,NullPointerException).
Definition cc := (javaLang,ClassCastException).
Definition ae := (javaLang,ArithmeticException).
Definition nase := (javaLang,NegativeArraySizeException).
Definition iob := (javaLang,ArrayIndexOutOfBoundsException).
Definition ase := (javaLang,ArrayStoreException).
*)

Definition tag := option ClassName.

(* DEX
Definition TypeStack := list L.t'.
*)
Module VarMap := BinNatMap.
Definition TypeRegisters := VarMap.t L.t'.

(* DEX
Definition compat_type_st_lvt (s:sign) (st:TypeStack) (n:nat) : Prop :=
  forall x, ((Var_toN x)<n)%nat -> exists k,
    nth_error st (n-(Var_toN x)-1)%nat = Some k /\
    L.leql' k (lvt s x).
*)

Definition compat_type_rt_lvt (s:sign) (rt:TypeRegisters) 
  (p:list Var) (n:nat) : Prop :=
  forall x, ((Var_toN x)<n)%nat ->
    exists r k, nth_error p (Var_toN x) = Some r /\ BinNatMap.get _ rt r = Some k /\
    L.leql' k (lvt s x).

(* DEX
Definition elift m pc k st :=
  match throwableAt m pc with
    | nil => st
    | _ => lift k st
  end.
*)

