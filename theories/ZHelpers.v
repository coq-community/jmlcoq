(**
----
_This file is part of_

----
*** A Formal Definition of JML in Coq #<br/># and its Application to Runtime Assertion Checking
Ph.D. Thesis by Hermann Lehner
----
Online available at #<a href="http://jmlcoq.info/">jmlcoq.info</a>#

Authors:
  - Hermann Lehner
  - David Pichardie (Bicolano)
  - Andreas Kaegi (Syntax Rewritings, Implementation of ADTs)

Copyright 2011 Hermann Lehner

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

----
*)

Require Import ZArith.
Require Import Sumbool.

(**
  Equality decision functions for 
  - Pair_eq_dec: pair types of decidable types A and B.
  - positivie_eq_dec
  - Z_eq_dec
  - ZPair_eq_dec
  *)

Section Pair_eq_dec.
  Variable A : Set.
  Variable B : Set.
  Variable A_eq_dec : forall x y:A, {x=y}+{x<>y}.
  Variable B_eq_dec : forall x y:B, {x=y}+{x<>y}.

  Definition Pair_eq_dec : forall x y:A*B, {x=y}+{x<>y}.
  Proof.
    (*
    intros x y.
    case x; case y.
    intros x1 x2 y1 y2.
    case (A_eq_dec x1 y1); case (B_eq_dec x2 y2); intros.
    left.
    rewrite e. rewrite e0. reflexivity.

    right.
    *)
    decide equality.
  Defined.
End Pair_eq_dec.
Implicit Arguments Pair_eq_dec [A B].

Definition positive_eq_dec : forall x y:positive, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

Definition Z_eq_dec : forall x y:Z, {x=y}+{x<>y}.
Proof.
  decide equality; apply positive_eq_dec.
Defined.

Definition ZPair_eq_dec : forall x y:Z*Z, {x=y}+{x<>y} := Pair_eq_dec Z_eq_dec Z_eq_dec.
  (*
  decide equality.
  case (Z_eq_dec b z0).
  left; assumption.
  right; assumption.
  case (Z_eq_dec a z).
  left; assumption.
  right; assumption.
  *)

Definition ZPair_eq_bool : forall x y :Z*Z, {b : bool | if b then x = y else x <> y} := 
  fun x y => bool_of_sumbool (ZPair_eq_dec x y).

Definition Z_eqb (x y:Z) : bool :=
  let (b,P) := Z_eq_bool x y in b.

Lemma Z_eqb_spec : forall x y, if Z_eqb x y then x = y else x <> y.
Proof.
  intros x y.
  unfold Z_eqb.
  destruct (Z_eq_bool x y).
  assumption.
Qed.

Definition ZPair_eqb (x y:Z*Z) : bool :=
  let (b,P) := ZPair_eq_bool x y in b.

Lemma ZPair_eqb_spec : forall x y, if ZPair_eqb x y then x = y else x <> y.
Proof.
  intros x y.
  unfold ZPair_eqb.
  destruct (ZPair_eq_bool x y).
  assumption.
Qed.

(* Eval compute in ZPair_eqb (1%Z,1%Z) (1%Z,1%Z). *)
