(** * Bicolano: Number axiomatisation *)

Require Export ZArith.
Require Export Bool.

(** Common interface for numerics domains *)
Open Local Scope Z_scope.
(** Taken form CompCert project *)

 Module Type NUMERIC.
  Parameter t : Set.
  Parameter power : nat.
  Parameter toZ : t -> Z.

  Parameter add : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter div : t -> t -> t.
  Parameter rem : t -> t -> t.
  Parameter shr : t -> t -> t.
  Parameter shl : t -> t -> t.
  Parameter ushr : t -> t -> t.
  Parameter and : t -> t -> t.
  Parameter or : t -> t -> t.
  Parameter xor : t -> t -> t. 
  Parameter neg : t -> t.
  Parameter not : t -> t.
  Parameter const : Z -> t.

 End NUMERIC.
 
 Module Type NUMSIZE.
  Parameter power : nat.
 End NUMSIZE.

 Module Make (S:NUMSIZE) <: NUMERIC.

  Definition modulus : Z := two_power_nat S.power.
  Definition half_modulus : Z := modulus / 2.

  Record t_: Set := mkint { intval: Z; intrange: 0 <= intval < modulus }.
  Definition t : Set := t_.

  Definition power := S.power.

  Definition unsigned (n: t) : Z := intval n.

  Definition signed (n: t) : Z :=
    if Zlt_bool (unsigned n) half_modulus
      then unsigned n
      else unsigned n - modulus.

  Definition toZ : t -> Z := signed.

  Lemma two_power_nat_O : two_power_nat O = 1.
  Proof. reflexivity. Qed.

  Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
  Proof.
    induction n. rewrite two_power_nat_O. omega.
    rewrite two_power_nat_S. omega.
  Qed.
  
  Lemma mod_in_range:
    forall x, 0 <= Zmod x modulus < modulus.
  Proof.
    intro.
    exact (Z_mod_lt x modulus (two_power_nat_pos power)).
  Qed.
  
  Definition repr (x: Z) : t := 
    mkint (Zmod x modulus) (mod_in_range x).

  Definition add (x y: t) : t :=
    repr (unsigned x + unsigned y).
  Definition sub (x y: t) : t :=
    repr (unsigned x - unsigned y).
  Definition mul (x y: t) : t :=
    repr (unsigned x * unsigned y).

  Definition Zdiv_round (x y: Z) : Z :=
    if Zlt_bool x 0 then
      if Zlt_bool y 0 then (-x) / (-y) else - ((-x) / y)
      else
        if Zlt_bool y 0 then -(x / (-y)) else x / y.
  Definition Zmod_round (x y: Z) : Z :=
    x - (Zdiv_round x y) * y.
  
  Definition div (x y: t) : t :=
    repr (Zdiv_round (signed x) (signed y)).
  Definition rem (x y: t) : t :=
    repr (Zmod_round (signed x) (signed y)).

  Definition Z_bin_decomp (x: Z) : bool * Z :=
    match x with
      | Z0 => (false, 0)
      | Zpos p =>
        match p with
          | xI q => (true, Zpos q)
          | xO q => (false, Zpos q)
          | xH => (true, 0)
        end
      | Zneg p =>
        match p with
          | xI q => (true, Zneg q - 1)
          | xO q => (false, Zneg q)
          | xH => (true, -1)
        end
    end.
  Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: Z -> bool :=
    match n with
      | O =>
        (fun i: Z => false)
      | S m =>
        let (b, y) := Z_bin_decomp x in
          let f := bits_of_Z m y in
            (fun i: Z => if Zeq_bool i 0 then b else f (i - 1))
    end.
  
  Definition Z_shift_add (b: bool) (x: Z) :=
    if b then 2 * x + 1 else 2 * x.

  Fixpoint Z_of_bits (n: nat) (f: Z -> bool) {struct n}: Z :=
    match n with
      | O => 0
      | S m => Z_shift_add (f 0) (Z_of_bits m (fun i => f (i + 1)))
    end.
  
  Definition shr (x y: t): t :=
    repr (signed x / two_p (unsigned y)).

  Definition shl (x y: t): t :=
    let fx := bits_of_Z power (unsigned x) in
      let vy := unsigned y in
        repr (Z_of_bits power (fun i => fx (i - vy))).

  Definition ushr (x y: t): t :=
    let fx := bits_of_Z power (unsigned x) in
      let vy := unsigned y in
        repr (Z_of_bits power (fun i => fx (i + vy))).

  Definition bitwise_binop (f: bool -> bool -> bool) (x y: t) :=
    let fx := bits_of_Z power (unsigned x) in
      let fy := bits_of_Z power (unsigned y) in
        repr (Z_of_bits power (fun i => f (fx i) (fy i))).
  
  Definition and (x y: t): t := bitwise_binop andb x y.
  Definition or (x y: t): t := bitwise_binop orb x y.
  Definition xor (x y: t) : t := bitwise_binop xorb x y.

  Definition neg (x: t) := repr (- unsigned x).
  Definition not (x: t) := repr ((- unsigned x) - 1).
    (* assuming that neg is two's complement and not is one's complement *)

  Definition const : Z -> t := repr.

 End Make.

