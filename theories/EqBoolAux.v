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

Require Export Sumbool.
Require Import List.

Definition bool_eq (b1 b2:bool) := 
  if b1 then b2 
  else if b2 then false else true.

Lemma bool_eq_spec : forall b1 b2, if bool_eq b1 b2 then b1 = b2 else b1 <> b2.
Proof. destruct b1;destruct b2;simpl;trivial;intro;discriminate. Qed.

Section EqBool_Dec.

 Variable A:Type.
 Variable Aeq : A -> A -> bool.
 Variable Aeq_spec : forall x y, if Aeq x y then x = y else x <> y.

 Lemma Aeq_dec : forall (x y:A), x = y \/ x <> y.
 Proof.
  intros x y;generalize (Aeq_spec x y);destruct (Aeq x y);auto.
 Qed.

 Lemma Aeq_eq : forall x, Aeq x x = true.
 Proof.
  intros;generalize (Aeq_spec x x);destruct (Aeq x x);intros;trivial.
  elim H;trivial.
 Qed.

 Lemma Aeq_diff : forall x y, x <> y -> Aeq x y = false.
 Proof.
  intros x y H;generalize (Aeq_spec x y);destruct (Aeq x y);intros;trivial.
  elim H;trivial.
  Qed.

 Lemma Aeq_Dec : forall x y:A, {x=y}+{x<>y}.
 Proof.
   intros. induction (sumbool_of_bool (Aeq x y)).
   apply left. assert (h:= (Aeq_spec x y)); rewrite a in h; assumption.
   apply right. assert (h:= (Aeq_spec x y)); rewrite b in h; assumption.
 Qed.

 Section EqBool_Prod.
  Variable B:Set.
  Variable Beq : B -> B -> bool. 
  Variable Beq_spec : forall x y, if Beq x y then x = y else x <> y.

  Definition prod_eq (x y:A*B) :=
   let (x1,x2) := x in
   let (y1,y2) := y in
   if Aeq x1 y1 then Beq x2 y2 else false.

  Lemma prod_eq_spec : forall x y, if prod_eq x y then x = y else x <> y.
  Proof.
     intros (x1,x2) (y1,y2); simpl;generalize (Aeq_spec x1 y1);destruct (Aeq x1 y1);intros;subst.
     generalize (Beq_spec x2 y2);destruct (Beq x2 y2);intros;subst;trivial.
     intro H1;injection H1;auto.
     intro H1;injection H1;auto.
  Qed.

 End EqBool_Prod.

 Section EqOption.
   Definition opt_eq (x y: option A) := 
     match x, y with
     | Some x, Some y => Aeq x y
     | None, None => true
     | _, _ => false
     end.
  
  Lemma opt_eq_spec : forall o1 o2, if opt_eq o1 o2 then o1 = o2 else o1 <> o2.
  Proof.
   intros [a1|] [a2|];simpl;trivial;try (intro H;discriminate H;fail).
   generalize (Aeq_spec a1 a2);destruct (Aeq a1 a2);intros;subst;trivial.
   intro H1;injection H1;auto.
  Qed.

 End EqOption.

 Section EqList. 

  Fixpoint list_eq (x y:list A) {struct x} : bool :=
    match x, y with
    | a1::x, a2::y => if Aeq a1 a2 then list_eq x y else false
    | nil, nil => true
    | _, _ => false
    end.

  Lemma list_eq_spec : forall l1 l2, if list_eq l1 l2 then l1 = l2 else l1 <> l2.
  Proof.
   induction l1;destruct l2;simpl;intros;trivial;try (intro;discriminate;fail).
   generalize (Aeq_spec a a0);destruct (Aeq a a0);intros;subst;trivial.
   generalize (IHl1 l2);destruct (list_eq l1 l2);intros;subst;trivial.
   intro H1;injection H1;auto.
   intro H1;injection H1;auto.
  Qed.

 End EqList.
End EqBool_Dec.
