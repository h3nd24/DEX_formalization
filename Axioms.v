(** * Axioms.v: the only axiom in this development is excluded middle *)

Axiom excluded_middle : forall (P:Prop), P \/ ~P.

Lemma eq_excluded_middle : forall (A:Set) (x y:A), x=y \/ x<>y.
Proof (fun A x y => excluded_middle _).