(** * Bicolano: Small step (interface only) *)

(* <Insert License Here>

    $Id: BigStep.v 68 2006-02-02 15:06:27Z davidpichardie $ *)

(** Small step semantics. Module type.

 @author David Pichardie *)

Require Export Domain.

Module Type SMALLSTEP.

  Declare Module Dom: SEMANTIC_DOMAIN.

  Load "SmallStepLoad.v".

End SMALLSTEP.
