(*** Framework.v: Abstract framework where we prove non interference from unwindings lemmas *)
Require Export Level.
Require Export cdr.

 Import L.

Section A.
Variable observable : L.t.

Variable PC : Set.
Variable Method : Type.
Variable Tag: Set.
Variable step : Method -> PC -> Tag -> option PC -> Prop.
Variable PM : Method -> Prop.
Variable cdr : forall m, PM m -> CDR (step m).
Implicit Arguments region.

Variable Sign : Set.

Record SignedMethod : Type := SM {unSign:Method; sign:Sign}.
Coercion unSign :  SignedMethod >-> Method.

(* DEX
Variable istate rstate : Type.
Variable exec : Method -> nat -> Kind -> istate -> istate+rstate -> Prop.

Variable pc : istate -> PC.
*)


Notation "m |- p1 =>( k ) p2" := (step m p1 k (Some p2)) (at level 30). 
Notation "m |- p1 =>( k ) " := (step m p1 k None) (at level 30).

Variable stacktype : Set.
Variable pbij : Set.
Variable texec : forall m, PM m ->
      Sign -> (PC->L.t) -> PC -> Tag ->  
      stacktype -> option stacktype -> Prop.

Variable s0 : stacktype.
(* Variable init : Method -> istate -> Prop. *)
Variable init_pc : Method -> PC -> Prop.

Variable P : SignedMethod -> Prop.

Variable PM_P : forall m, P m -> PM m.

Definition Typable (m:Method) (H:PM m) (sgn:Sign) (se:Method->Sign->PC->L.t) (S:Method->Sign->PC->stacktype) : Prop :=
  (forall i, init_pc m i -> S m sgn i = s0) /\
  (forall i kd,
     m |- i =>(kd) ->
     texec m H sgn (se m sgn) i kd (S m sgn i) None) /\
  (forall i j kd,
    m |- i =>(kd) j ->
    exists st,
      texec m H sgn (se m sgn) i kd (S m sgn i) (Some st) 
      /\ sub st (S m sgn j)).

Definition TypableProg se S := 
  forall m sgn (H:P (SM m sgn)), Typable m (PM_P _ H) sgn se S.

End A.






