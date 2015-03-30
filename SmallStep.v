(** * Bicolano: Small step (interface implementation) *)

(* <Insert License Here>

    $Id: SmallStep.v 69 2006-03-06 20:16:11Z davidpichardie $ *)

(** Formalization of Java small step semantics.
 Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
  Tim Lindholm, Frank Yellin"

 @author David Pichardie *)


Require List.
Require Export SmallStepType.

Module MakeSmallStep (D:SEMANTIC_DOMAIN) <: SMALLSTEP.

  Module Dom := D.

  (* Inductive definition are put in SmallStepLoad.v.
     They are shared with SmallStepType.v *)
  Load "SmallStepLoad.v".

End MakeSmallStep.



(* 
 Local Variables: 
 coq-prog-name: "coqtop -emacs"
 End:
*)
