(** * Tactics.v: Some useful tactics *)

Ltac case_eq_test test thm := 
  match goal with
    [ |- context[test ?x ?y] ] => 
    generalize (thm x y); destruct (test x y);
      let h := fresh "Hyp" in (intros Hyp)
  end.

Ltac caseeq t := generalize (refl_equal t); pattern t at -1 in |- * ; case t.

Ltac Cleanand:= 
  (repeat match goal with
            | [ H: ?a /\ ?b  |- _] => destruct H
          end).


Ltac Cleanexand :=
  match goal with
    | H:(ex ?X2) |- _ => destruct H;  intros; Cleanexand
    | H:(and ?X2 ?X3) |- _ => destruct H; intros; Cleanexand
    |  _ => idtac
  end.

Ltac Cleanandimp := repeat (split; try intros; try assumption).

Ltac Splitand:= 
  (repeat match goal with
            | [ |- ?a /\ ?b ] => split
          end).

Ltac DiscrimateEq := 
  repeat 
    (match goal with
       | [ x: ?a = _, y: ?a = _ |- _] => rewrite x in y; discriminate y || (injection y; intros; clear y; subst)
     end).

(***********************************************************)
(* Taken From http://cocorico.cs.ru.nl/coqwiki/TacticExts  *)
Ltac rewrite_in_cxt H :=
  let T := type of H in
    match T with
      | ?t1 = ?t2 =>
        repeat
          (
            generalize H; clear H; 
              match goal with
                | id : context[t1] |- _ =>
                  intro H; rewrite H in id
              end
          )
    end.
Ltac rewrite_all H :=
  rewrite_in_cxt H; rewrite H.
Ltac replace_in_cxt t1 t2 :=
  let H := fresh "H" in
    (cut (t1 = t2); [ intro H; rewrite_in_cxt H; clear H | idtac ]).
Ltac replace_all t1 t2 :=
  let H := fresh "H" in
    (cut (t1 = t2); [ intro H; rewrite_all H; clear H | idtac ]).
(***********************************************************)


(* inversion with substitution *)
Ltac inversion_mine H := inversion H; clear H; try subst.

(* Find a contradiction in the current context *)
Ltac Contradiction :=
  match goal with
    | [ x: ~ ?T, y: ?T |- _] => elim x; apply y
  end.

Ltac trivial_eq :=
  match goal with
    [ id : ?x <> ?x |- _ ] => elim id; reflexivity
  end.