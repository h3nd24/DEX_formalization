(** * Bicalano: Implementation of a subclass test *)

Require Import List.

Set Implicit Arguments.

Section FOLD.

Variable A : Type.
Variable f : A -> option A.

Fixpoint fold_opt (l:list A) : option (list A) :=
  match l with
  | nil  => None
  | a::l =>
    match f a with
    | None =>
      match fold_opt l with
      | None => None
      | Some l' => Some (a::l')
      end
    | Some a' => Some (a' :: l)  
    end
  end.

End FOLD.

Section SUBCLASS.

Variable name : Set.
Variable class : Type.
Variable get_name : class -> name.
Variable eq_name : name -> name -> bool.
Variable superclass : class -> option name.

Inductive tree : Set :=
  node : name -> list tree -> tree.

Fixpoint get_tree  (n:name) (lt: list tree) {struct lt} : 
                                    option (tree * list tree) := 
  match lt with
  | nil => None
  | t :: lt => 
    let (x,_) := t in
    if eq_name x n then Some (t, lt)
    else match get_tree n lt with
    | None => None
    | Some (nt,lt) => Some (nt, t::lt)
    end
  end. 

Definition init_tree n lt :=
  match get_tree n lt with
  | None => (node n nil, lt)
  | Some(tc, lt) => (tc, lt)
  end.
    
Fixpoint add_subclass (s:name) (c:tree) (t:tree) {struct t} : option tree :=
  match t with
  | node x l =>
    if eq_name x s then Some (node x (c::l))
    else match fold_opt (add_subclass s c) l with
    | None => None
    | Some l => Some (node x l)
    end
  end.
  
Section BUILD_TREE.

 Variable obj : name.

 Fixpoint build_tree (lt:list tree) (l:list class) {struct l} : 
                                                               list tree :=
   match l with   
   | nil => lt
   | c::l => 
     let (tc,lt) := init_tree (get_name c) lt in
     let super := match superclass c with Some s => s | None => obj end in
     let lt := 
       match fold_opt (add_subclass super tc) lt with
       | Some lt => lt
       | None => (node super (cons tc nil)) :: lt
       end in
     build_tree lt l 
   end.
  
End BUILD_TREE.


Variable map : Type -> Type.
Variable empty : forall C:Set, map C.
Variable update : forall C:Set, map C -> name -> C -> map C.
Variable get : forall C:Set, map C -> name -> option C.

Fixpoint build_supers (super:list name) (t:tree) (m:map(list name)){struct t} :
                            map (list name) := 
  match t with
  | node a lt =>
    update (fold_right (build_supers (a::super)) m lt) a super
  end.

Fixpoint test_In (a:name) (l:list name) {struct l} : bool :=
  match l with
    nil => false
  | x::q => if eq_name a x then true else test_In a q
  end.

Fixpoint get_obj (l:list class) : option (name * list class) := 
 match l with
 | nil => None
 | c::l =>
    match superclass c with
    | None => Some (get_name c, l)
    | Some _ =>
      match get_obj l with
      | None => None
      | Some (obj, l) => Some (obj, c::l)
      end
    end
 end.

Definition subclass_test (l:list class) : option (name -> name -> bool) :=
  match get_obj l with
  | None => None
  | Some (obj, l) =>
    match build_tree obj nil l with
    | t::nil =>
      let m := build_supers nil t (empty (list name)) in
      Some (fun x y =>
              match get m x with
              | None => false
              | Some supers => if eq_name x y then true else test_In y supers
              end)
    | _ => None
    end 
  end.

End SUBCLASS.


(*





























Section __A__.
Variable A : Set.
Variable test : A -> A -> bool.

Inductive tree (A:Set) : Set :=
  node : A -> list (tree A) -> tree A.

Section fold_opt.
Variable B:Set.
Variable f:B->option B.

Fixpoint fold_opt (l:list B) {struct l} : option (list B) :=
 match l with
   nil => None
 | a::q =>
    match f a with
     | Some a' => Some (a'::q)
     | None => 
        match fold_opt q with
          None => None
        | Some q' => Some (a::q')
        end
    end
 end.

End fold_opt.

Fixpoint add (n s:A) (t:tree A) {struct t} : option (tree A) :=
  match t with
    node x l =>
      if test x s then Some (node x (node n nil::l))
      else
        match fold_opt (add n s) l with
          None => None
        | Some l' => Some (node x  l')
        end
  end.

Variable class : Set.
Variable name : class -> A.
Variable superclass : class -> option A.

Fixpoint build_tree_rec (t:tree A) (l:list class) {struct l} : option (tree A) :=
 match l with
  nil => Some t
 | c::q => 
     match superclass c with
      Some s =>
         match (add (name c) s t) with
          None => None
        | Some t' => build_tree_rec t' q
        end
     | _ => None
     end
 end.

Definition build_tree (l:list class) : option (tree A) :=
 match l with 
 | nil => None
 | c::l => 
    match superclass c with
     None => build_tree_rec (node (name c) nil) l
    | _ => None
    end
 end.

Fixpoint test_In (a:A) (l:list A) {struct l} : bool :=
  match l with
    nil => false
  | x::q => if test a x then true else test_In a q
  end.

Fixpoint find (C:Set) (a:A) (l:list (A*C)) {struct l} : option C :=
  match l with
    nil => None
  | (x,c)::q => if test a x then Some c else find a q
  end.

Variable B:Set -> Set.
Variable empty : forall C:Set, B C.
Variable update : forall C:Set, B C -> A -> C -> B C.
Variable get : forall C:Set, B C -> A -> option C.

Fixpoint build_supers (l:list A) (t:tree A) (b:B (list A)) {struct t}  : B (list A) := 
  match t with
    node a ltt =>
      update (fold_right (build_supers (a::l)) b ltt)  a l
  end.

Definition subclass_test (l:list class) : option (A -> A -> bool) :=
  match build_tree l with
    None => None
  | Some t =>
      let m := build_supers nil t (empty (list A)) in
        Some (fun x y =>
                match get m x with
                  None => false
                | Some supers => test_In y supers
                end)
  end.

End __A__.






















(*

Definition l : list (class nat) := 
 (mc 0 None)::(mc 1 (Some 0))::(mc 2 (Some 0))::(mc 3 (Some 0))::
 (mc 4 (Some 1))::
 (mc 5 (Some 1))::
 (mc 6 (Some 4))::
 (mc 7 (Some 2))::
 (mc 8 (Some 2))::nil.

Fixpoint nat_eq (n1 n2:nat) {struct n1} : bool :=
  match n1,n2 with
    O,O => true
  | S p1,S p2 => nat_eq p1 p2
  | _,_ => false
  end.

Eval compute in build_tree nat_eq l.

Definition t :=
   (node 0
      (node 3 nil::
       node 2 (node 8 nil ::
               node 7 nil :: nil) ::
       node 1 (node 5 nil :: 
               node 4 (node 6 nil :: nil) :: 
               nil) ::
       nil)).


Definition subclass_nat_test :=
 @subclass_test nat nat_eq
   (fun C => list (nat*C))
   (fun C => @nil (nat*C))
   (fun C a c b =>cons (a,c) b)
   (find nat_eq).

Eval compute in
 @build_supers nat
      (fun C => list (nat*C))
   (fun C a c b =>cons (a,c) b)
   nil t nil.

Definition test (A:Set) (f_op:option (A->A->bool)) :=
  match f_op with 
   None => fun _ _ => false
 | Some f => f
  end.

Eval compute in test (subclass_nat_test l) 3 0.
Eval compute in test (subclass_nat_test l) 2 0.
Eval compute in test (subclass_nat_test l) 8 0.
Eval compute in test (subclass_nat_test l) 8 2.
Eval compute in test (subclass_nat_test l) 7 0.
Eval compute in test (subclass_nat_test l) 7 2.
Eval compute in test (subclass_nat_test l) 1 0.
Eval compute in test (subclass_nat_test l) 5 0.
Eval compute in test (subclass_nat_test l) 5 1.
Eval compute in test (subclass_nat_test l) 4 0.
Eval compute in test (subclass_nat_test l) 4 1.
Eval compute in test (subclass_nat_test l) 6 0.
Eval compute in test (subclass_nat_test l) 6 1.
Eval compute in test (subclass_nat_test l) 6 4.
Eval compute in test (subclass_nat_test l) 6 2.
Eval compute in test (subclass_nat_test l) 6 3.
Eval compute in test (subclass_nat_test l) 6 5.
Eval compute in test (subclass_nat_test l) 6 7.
Eval compute in test (subclass_nat_test l) 6 8.


*)
*)
