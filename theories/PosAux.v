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

Definition Peq x y :=
 match Pcompare x y Eq with 
 | Eq => true
 | _ => false
 end.

Lemma Peq_spec : forall x y, if Peq x y then x = y else x <> y.
Proof.
 unfold Peq;intros x y. 
 generalize (refl_equal (Pcompare x y Eq));pattern (Pcompare x y Eq) at -1;
  case (Pcompare x y Eq);intros.
 apply Pcompare_Eq_eq;trivial.
 intros Heq;rewrite Heq in H;rewrite Pcompare_refl in H;discriminate.
 intros Heq;rewrite Heq in H;rewrite Pcompare_refl in H;discriminate.
Qed.

Definition Neq x y := 
 match x, y with 
 | N0, N0 => true
 | Npos x, Npos y => Peq x y
 | _, _ => false
 end.

Lemma Neq_spec : forall x y, if Neq x y then x = y else x <> y.
Proof.
 destruct x;destruct y;simpl;trivial;try (intro; discriminate).
 generalize (Peq_spec p p0);destruct (Peq p p0);unfold not;intros;subst;trivial.  
 injection H0;trivial.
Qed.

Lemma Zeq_spec : forall (x y:Z), if Zeq_bool x y then x = y else x<>y.
Proof.
 unfold Zeq_bool;destruct x;destruct y;simpl;trivial;
  try (intro H;discriminate H;fail).
 fold (Peq p p0);generalize (Peq_spec p p0);destruct (Peq p p0);
  intros;subst;trivial.
 intro H1;injection H1;auto.
 generalize (refl_equal (Pcompare p p0 Eq));pattern (Pcompare p p0 Eq) at -1;
  case (Pcompare p p0 Eq);intros;simpl.
 rewrite (Pcompare_Eq_eq _ _ H);trivial.
 intros Heq;injection Heq;intros;subst;rewrite Pcompare_refl in H;discriminate.
 intros Heq;injection Heq;intros;subst;rewrite Pcompare_refl in H;discriminate.
Qed.


Definition nat_of_N (n : N) : nat := match n with
  | N0 => 0
  | (Npos p) => nat_of_P p
end.

Definition N_of_nat n := 
  match n with 
  | O => N0
  | S n => Npos (P_of_succ_nat n) 
  end.

Lemma nat_of_N_bij1 : 
    forall v, nat_of_N (N_of_nat v) = v.
Proof.
 intros [|n];simpl. reflexivity.
 apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Lemma nat_of_N_bij2 : forall n, N_of_nat (nat_of_N n) = n.
Proof.
 intros [|p];simpl. reflexivity.
 assert (exists m, nat_of_P p = S m).
 induction p.
  rewrite nat_of_P_xI;eauto.
  rewrite nat_of_P_xO.
  destruct IHp as (m, Heq);rewrite Heq.
  simpl;eauto.
  unfold nat_of_P;simpl. eauto.
  destruct H as (m,Heq);rewrite Heq;simpl.
  assert (H:=pred_o_P_of_succ_nat_o_nat_of_P_eq_id p).
  rewrite <- H;rewrite Heq.
  simpl.  rewrite Ppred_succ. trivial.
Qed.


Definition Npred x :=
 match x with
 | N0 => N0
 | Npos xH => N0
 | Npos p => Npos (Ppred p)
 end.
